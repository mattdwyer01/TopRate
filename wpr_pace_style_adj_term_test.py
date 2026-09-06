"""
wpr_pace_style_adj_term_test.py - tests a NEW candidate ADJ_TERM: does a
runner's PREDICTED running style (cur_settle_band: Leader/On-pace/Midfield/
Back, already computed pre-race from the horse's own history + today's
barrier) benefit or suffer given the race's PREDICTED pace shape
(cur_race_speed_label: Hot/Fast/Even/Slow, race_speed_estimate.py's own
leak-safe pre-race model)?

WHY THIS EXISTS (direct user example): a lower-rated horse drawn to get an
uncontested, soft lead (predicted Slow pace + predicted Leader) can be a
BETTER bet than a higher-rated horse that has to work into a genuine speed
duel or make ground from off a hot pace - but WPR's projection currently
has NO term for this. The pace label already shown on the dashboard's
speed map is DISPLAY-ONLY; it never adjusts any individual horse's number.

TODAY'S EARLIER DIAGNOSTIC (wpr_track_bias_pace_review_v1.py, using the
ACTUAL post-race pace as an oracle) found this effect is real, large, and
monotonic: leader miss go from -1.03 (actual slow pace) to -4.00 (actual
hot pace). This script tests whether the model's OWN PRE-RACE PREDICTION
of pace/style (not the oracle) carries enough of that signal to be worth
adding as a real ADJ_TERM.

DESIGN: a population-level shrunk lookup, exactly the same shape as the
existing track_barrier ADJ_TERM (the one precedent that has actually
worked in this codebase - per-horse versions of similar ideas, own_settle/
own_barrier/own_pace, all failed on small per-horse samples):
  residual = target - career_avg (quality-normalised)
  grouped by cur_race_speed_label, then by cur_settle_band within that
  group, shrunk toward the GLOBAL mean for that settle_band (across all
  pace labels) with strength K, then centered per pace_label group (so it
  can never become a flat "hot races are just lower-WPR" bias - only the
  RELATIVE effect of running style WITHIN that pace context survives,
  same centering discipline as track_barrier's per-(track,dist_band)
  centering).

LEAK-SAFETY: cur_settle_band is already a leak-safe pre-race prediction
(own history + today's barrier - see build_features's own comment).
cur_race_speed_label needs a LEAK-SAFE historical reconstruction for
training - reuses wpr_own_pace_backtest.build_race_speed_labels(), which
already correctly keys by race_id (verified empirically here: race_id
varies correctly per row within one horse's own raw form-history table,
unlike run_id, which is constant across a whole scrape - confirmed by
direct inspection before trusting this join).

LIVE WIRING, if this validates: race_speed_estimate.py's rs_label is
ALREADY computed daily in toprate_daily.py BEFORE project_race() runs
(see add_race_speed_columns-style step) but is never threaded into the
runners dict passed to project_race() - a ONE-LINE addition
("cur_race_speed_label": r.get("rs_label")), not new infrastructure.

VALIDATION: same bidirectional bar as every other candidate today - both
directions of a swapped chronological split must improve held-out MAE.

NO EM DASHES policy: hyphens only.
"""
import time

import numpy as np
import pandas as pd
from sklearn.metrics import mean_absolute_error

import wpr_projection as wpr
from wpr_own_pace_backtest import build_race_speed_labels
from wpr_void_expansion_bidirectional_test import fit_track_barrier, fit_pace_baseline_reversed, additive_predict

FORM_CSV = "wpr_form_history.csv.gz"
SETTLE_BANDS = ["Leader", "On-pace", "Midfield", "Back"]
K_VALUES = [100.0, 300.0, 600.0]


def prepare_frame(race_id_to_label):
    print("  building training frame (build_features, with race_speed_labels)...")
    D = wpr.build_training_frame(FORM_CSV, n_jobs=-1, race_speed_labels=race_id_to_label) \
        .dropna(subset=["target", "date"]).sort_values("date")
    print(f"  {len(D):,} training rows")

    # cur_race_speed_label as its own column - own_pace already proved this
    # join (D's own "race_id", sourced from the raw per-row form-history
    # race_id inside _horse_feature_rows - see that function's own
    # docstring) is leak-safe and correct; reusing the exact same key here.
    D["cur_race_speed_label"] = D["race_id"].map(race_id_to_label)
    print(f"  cur_race_speed_label coverage: {D['cur_race_speed_label'].notna().mean()*100:.1f}%")
    print(f"  cur_settle_band coverage: {D['cur_settle_band'].notna().mean()*100:.1f}%")

    _name_map, _tj_lookup = wpr._load_trainer_jockey_by_horse_date(FORM_CSV)
    _tj_dates = D["date"].dt.strftime("%Y-%m-%d")
    _tj_names = D["horse_id"].map(_name_map)
    _tj_vals = [_tj_lookup.get((n, d), (np.nan, np.nan)) for n, d in zip(_tj_names, _tj_dates)]
    D["trainer_win_pct_365d"] = [t for t, j in _tj_vals]
    D["jockey_win_pct_90d"] = [j for t, j in _tj_vals]

    from wpr_void import void_from_comment_only
    cv = D["comments_video"] if "comments_video" in D.columns else None
    cs = D["comments_steward"] if "comments_steward" in D.columns else None
    if cv is not None or cs is not None:
        cv = cv if cv is not None else [None] * len(D)
        cs = cs if cs is not None else [None] * len(D)
        void_mask = [void_from_comment_only(a, b)[0] for a, b in zip(cv, cs)]
        n_void = int(sum(void_mask))
        D = D[[not v for v in void_mask]].copy()
        print(f"  void filter: excluded {n_void:,} compromised runs, {len(D):,} rows remain")

    if "going" in D.columns:
        g = D["going"].astype(str).str.strip().str.lower()
        blank_going = D["going"].isna() | g.isin(["", "nan", "none", "<na>"])
        n_blank = int(blank_going.sum())
        if n_blank:
            D = D[~blank_going].copy()
            print(f"  surface filter: excluded {n_blank:,} blank-going rows, {len(D):,} remain")

    D["_base"] = wpr._BASE_BLEND_ALPHA * D["wpr_nett"] + (1 - wpr._BASE_BLEND_ALPHA) * D["ewm5"]
    D["_base"] = D["_base"].fillna(D["wpr_nett"]).fillna(D["ewm5"]).fillna(D["avg_last3"]).fillna(D["career_avg"])
    D = D.dropna(subset=["_base"]).copy()
    return D


def fit_pace_style(trn, k):
    resid = trn["target"] - trn["career_avg"]
    frame = pd.DataFrame({
        "pace": trn["cur_race_speed_label"], "band": trn["cur_settle_band"], "residual": resid,
    }).dropna(subset=["pace", "band", "residual"])
    global_by_band = frame.groupby("band")["residual"].mean().to_dict()
    lookup = {}
    for pace_val, g in frame.groupby("pace"):
        stats = g.groupby("band")["residual"].agg(["mean", "count"])
        shrunk = {}
        for b in SETTLE_BANDS:
            if b in stats.index:
                n, m = stats.loc[b, "count"], stats.loc[b, "mean"]
                shrunk[b] = (n * m + k * global_by_band.get(b, 0.0)) / (n + k)
            else:
                shrunk[b] = global_by_band.get(b, 0.0)
        center = float(np.mean(list(shrunk.values())))
        lookup[pace_val] = {
            b: float(max(-wpr._OWN_DELTA_CAP, min(wpr._OWN_DELTA_CAP, shrunk[b] - center))) for b in shrunk
        }
    return lookup


def pace_style_term(pace_val, band_val, lookup):
    if pace_val is None or band_val is None or (isinstance(pace_val, float) and pd.isna(pace_val)):
        return 0.0
    return float(lookup.get(pace_val, {}).get(band_val, 0.0))


def held_out_mae_both_directions(D, k):
    trainer_edges, trainer_lookup = wpr._fit_merit_lookup(D, "trainer_win_pct_365d")
    jockey_edges, jockey_lookup = wpr._fit_merit_lookup(D, "jockey_win_pct_90d")

    results = {}
    for direction, (trn, te) in [
        ("A: forward (oldest 70% trn, newest 15% te)",
         (D[D["date"] < D["date"].quantile(0.70)],
          D[D["date"] >= D["date"].quantile(0.85)])),
        ("B: reversed (newest 70% trn, oldest 15% te)",
         (D[D["date"] > D["date"].quantile(0.30)],
          D[D["date"] <= D["date"].quantile(0.15)])),
    ]:
        te = te.copy()
        tb_lookup = fit_track_barrier(trn)
        te["track_barrier"] = [
            wpr._track_barrier_term(trk, dist, bar, fs, tb_lookup)
            for trk, dist, bar, fs in zip(te["track"], te["cur_distance"], te["barrier"], te["field_size"])
        ]
        te["trainer_merit"] = [wpr._merit_term(wpr._merit_bucket(v, trainer_edges), trainer_lookup)
                                for v in te["trainer_win_pct_365d"]]
        te["jockey_merit"] = [wpr._merit_term(wpr._merit_bucket(v, jockey_edges), jockey_lookup)
                               for v in te["jockey_win_pct_90d"]]
        cutoff = trn["date"].min() if "reversed" in direction else trn["date"].max()
        pace_lookup_fn = fit_pace_baseline_reversed if "reversed" in direction else \
            (lambda c: wpr._fit_pace_baseline(FORM_CSV, c))
        pb_lookup = pace_lookup_fn(cutoff)
        te["closing_merit"] = [wpr._closing_merit_term(p, pb_lookup) for p in te["closing_pairs"]]

        pace_style_lookup = fit_pace_style(trn, k)
        te["pace_style"] = [
            pace_style_term(pv, bv, pace_style_lookup)
            for pv, bv in zip(te["cur_race_speed_label"], te["cur_settle_band"])
        ]

        scored = te.dropna(subset=["_base"] + wpr.ADJ_TERMS)
        baseline_mae = mean_absolute_error(scored["target"], additive_predict(scored))

        scored2 = scored.copy()
        candidate_terms = wpr.ADJ_TERMS + ["pace_style"]
        cand_pred = scored2["_base"].to_numpy() + wpr._cap_adj_sum(
            scored2[candidate_terms].to_numpy()).sum(axis=1)
        candidate_mae = mean_absolute_error(scored2["target"], cand_pred)

        print(f"  [k={k:.0f}] direction {direction}: n_trn={len(trn):,} n_te={len(scored):,} "
              f"baseline={baseline_mae:.4f} candidate={candidate_mae:.4f} "
              f"({'better' if candidate_mae < baseline_mae else 'worse'}, {candidate_mae - baseline_mae:+.4f})")
        results[direction] = (baseline_mae, candidate_mae)
    return results


def run():
    print("Building leak-safe historical race-speed labels (race_speed_estimate.py's own model)...")
    since = (pd.Timestamp.today() - pd.Timedelta(days=365)).strftime("%Y-%m-%d")
    race_id_to_label = build_race_speed_labels(since)

    print("\nPreparing training frame...")
    t0 = time.time()
    D = prepare_frame(race_id_to_label)
    print(f"  done in {time.time() - t0:.0f}s")

    print("\n=== pace_style ADJ_TERM candidate: K sweep, both directions ===")
    for k in K_VALUES:
        print(f"\n--- K={k:.0f} ---")
        res = held_out_mae_both_directions(D, k)
        both_better = all(c < b for b, c in res.values())
        print(f"  {'BOTH DIRECTIONS IMPROVED' if both_better else 'not both improved'}")

    print("\nDone.")


if __name__ == "__main__":
    run()
