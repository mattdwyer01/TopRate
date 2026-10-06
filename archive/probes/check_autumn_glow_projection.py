"""One-off check: what does the CURRENT wpr_models/ (whatever is on disk
right now, e.g. your just-retrained one) actually project for Autumn
Glow's next race, using her real captured history and real race
conditions. Compares against the wprp_proj already sitting in
toprate_runners.csv (what the dashboard is currently showing).

NO EM DASHES policy: hyphens only in this file.
"""
import pandas as pd
import wpr_projection as wp

runners = pd.read_csv('toprate_runners.csv', dtype={'run_id': str, 'race_id': str},
                      low_memory=False)
ag_rows = runners[(runners['horse'] == 'Autumn Glow') & (runners['resulted'] != 1)]
if ag_rows.empty:
    ag_rows = runners[runners['horse'] == 'Autumn Glow']
    print("No pending race found for Autumn Glow - showing her most recent row instead.")
row = ag_rows.iloc[-1]
print(f"Race: {row['date']} {row['venue']} R{row['race']}  dist={row['distance']} "
      f"going={row['going']} class={row['race_class']}")
print(f"Currently on dashboard: wprp_proj={row.get('wprp_proj')}  "
      f"wprp_conf={row.get('wprp_conf')}")

form = pd.read_csv('wpr_form_history.csv.gz', dtype={'horse_id': str}, low_memory=False)
ag_form = form[form['horse'] == 'Autumn Glow'].copy()
print(f"\n{len(ag_form)} form-history rows loaded for Autumn Glow")

print(f"\nRaw wpr_nett from toprate_runners.csv for this row: {row.get('wpr_nett')!r}")

real_field_size = len(runners[runners['race_id'] == row['race_id']])
print(f"Real field size for this race (count of runners on race_id "
      f"{row['race_id']}): {real_field_size}")

runner = {
    'prior_runs': ag_form,
    'cur_distance': row['distance'],
    'cur_going': row['going'],
    'cur_track': row['venue'],
    'cur_track_grading': row['track_grading'],
    'cur_race_class': row['race_class'],
    'cur_field_size': real_field_size,
    'cur_wpr_nett': row.get('wpr_nett'),
}
results = wp.project_race([runner], row['date'])
r = results[0]
print(f"\nFreshly computed with current wpr_models/:")
print(f"  has_projection: {r['has_projection']}")
print(f"  projected_wpr:  {r['projected_wpr']}")
print(f"  confidence:     {r['confidence']}")
print(f"  peak_wpr:       {r.get('peak_wpr')}")
print(f"  avg_l3:         {r.get('avg_l3')}")

# Full feature vector actually fed to the model, so we can see exactly what
# got median-filled vs what came from her real history.
feats = wp.build_features(ag_form, row['distance'], row['going'], row['venue'],
                          row['track_grading'], row['date'],
                          cur_race_class=row['race_class'],
                          cur_field_size=real_field_size,
                          cur_wpr_nett=row.get('wpr_nett'))
med = wp._CFG['medians'] if wp._CFG else {}
print(f"\nRaw build_features() output (before any median-fill):")
for k in ['n_runs', 'first_up', 'runs_this_camp', 'days_since', 'avg_last3',
          'avg_last5', 'peak', 'career_avg', 'recent_vs_career', 'wpr_nett',
          'trend', 'ewm3', 'field_size']:
    v = feats.get(k) if feats else None
    is_nan = v is None or (isinstance(v, float) and v != v)
    flag = "  <-- MEDIAN-FILLED (raw value missing!)" if is_nan else ""
    print(f"  {k:20s} = {v!r}{flag}  (training median: {med.get(k)!r})")

# Ablation: how much is the model's OWN learned first_up discount actually
# worth for this exact feature vector? Predict twice, flipping only
# first_up, everything else identical - isolates that one feature's effect.
wp._load_models()
X = wp._feature_frame([feats])
base_pred = float(wp._PROJ.predict(X)[0]) + float(wp._CFG.get('calib_offset', 0.0))
X_no_firstup = X.copy()
X_no_firstup['first_up'] = 0
no_firstup_pred = float(wp._PROJ.predict(X_no_firstup)[0]) + float(wp._CFG.get('calib_offset', 0.0))
print(f"\nAblation - isolating the model's learned first_up effect:")
print(f"  prediction with first_up=1 (as-is):  {base_pred:.2f}")
print(f"  prediction with first_up=0 (all else equal): {no_firstup_pred:.2f}")
print(f"  model's learned first-up discount for this exact horse: "
      f"{base_pred - no_firstup_pred:+.2f}")

# first_up is DERIVED from days_since (days_since >= 90), so a tree model
# likely split on days_since directly rather than the redundant flag - the
# ablation above isolating first_up alone proves nothing on its own. Zero
# out the whole freshness cluster together (days_since, runs_this_camp,
# first_up, second_up, trend) to isolate the TOTAL "just spelled" effect.
X_fresh = X.copy()
for col, val in [('days_since', 21), ('runs_this_camp', 4), ('first_up', 0),
                 ('second_up', 0), ('trend', 0.0)]:
    if col in X_fresh.columns:
        X_fresh[col] = val
fresh_pred = float(wp._PROJ.predict(X_fresh)[0]) + float(wp._CFG.get('calib_offset', 0.0))
print(f"\n  prediction if treated as mid-campaign instead of first-up-off-a-spell: "
      f"{fresh_pred:.2f}")
print(f"  total 'just spelled' discount: {base_pred - fresh_pred:+.2f}")

# Feature importances - what is the model actually weighting most heavily?
print(f"\nTop 15 model feature importances (LightGBM gain):")
imp = sorted(zip(wp.FEATURES, wp._PROJ.feature_importances_),
            key=lambda t: -t[1])[:15]
for name, val in imp:
    print(f"  {name:20s} {val}")
