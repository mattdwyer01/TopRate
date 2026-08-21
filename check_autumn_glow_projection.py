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

runner = {
    'prior_runs': ag_form,
    'cur_distance': row['distance'],
    'cur_going': row['going'],
    'cur_track': row['venue'],
    'cur_track_grading': row['track_grading'],
    'cur_race_class': row['race_class'],
    'cur_field_size': None,
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
