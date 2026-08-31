"""
wpr_closing_merit_strike_eval.py - tests a population-level "trip/pace-
adjusted closing sectional merit" candidate ADJ_TERM, motivated by the
Sectional Time Ratings doc's core warning: a horse's raw closing sectional
strength is misleading without race context ("flashing lights" - a horse
that closes fast because the leaders slowed dramatically, not because it
ran home genuinely well), AND by the WFA Performance Ratings doc's own
admission that "subjective judgments such as those for bad luck in
running, pace, or track bias disadvantage are not factored into each
horse's individual rating... by leaving these subjective factors out, you
can judge individual allowances... and gain a winning edge" - i.e.
wpr_nett deliberately does NOT do the pace-context adjustment this
candidate attempts.

WHY THIS IS STRUCTURALLY DIFFERENT FROM own_pace / settle_pace (both
already tested and REJECTED this session)
  Both prior candidates needed a PREDICTION of TODAY's race (a forecast of
  today's tempo, or the horse's own historical tempo-band match) - noisy
  by construction, since the future is unknown pre-race. This candidate
  uses ONLY a horse's own PAST run's ALREADY-KNOWN, REAL numbers: how fast
  its last-600m sectional was, and how the race it ran in ACTUALLY
  unfolded (raceShapeEarly, measured after the fact) - no forecast, no
  leak (it's about a run that already happened), and no per-horse
  own-history MATCHING requirement (own_pace/own_settle's dilution
  problem) since every horse with a recent run gets a value, not just
  horses with enough matching-category history.

METHODOLOGY
  1. Population-level baseline: fit "expected sect_i_l600 given this
     race's ACTUAL early pace bias (raceShapeEarly, bucketed)" from ALL
     historical runs on one chronological half of the raw form history.
     residual = actual sect_i_l600 - expected(bucket) - the "flashing
     lights" correction: closing fast in a race that let everyone close
     fast scores near 0, closing fast against a genuinely tough pace
     scores positive.
  2. For each horse, at each point in time, average the residuals from
     its own last up to 3 PRIOR runs (shrunk by count, same _shrink
     convention as every other own_* term) - this is the candidate
     feature, "closing_merit".
  3. Add it to the current 7-term ADJ_TERMS baseline, compare held-out
     top-1 strike rate and MAE, chronological half-split, BOTH
     directions (the baseline fit AND the closing_merit residual
     baseline are both refit per direction, so nothing leaks across).

USAGE
  python wpr_closing_merit_strike_eval.py

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd
from sklearn.metrics import mean_absolute_error

import wpr_projection as wpr
from wpr_own_pace_backtest import add_base, add_track_barrier

FORM_CSV = "wpr_form_history.csv.gz"
RUNNERS_CSV = "toprate_runners.csv"
PACE_BINS = [-999, -7, -5, -3, -1, 1, 3, 5, 7, 999]
_SHRINK_K = 3.0  # matches wpr._OWN_DELTA_SHRINK_K


def _shrink(delta, n):
    return delta * n / (n + _SHRINK_K)


def load_raw_form():
    fh = pd.read_csv(FORM_CSV, low_memory=False)
    fh["date"] = pd.to_datetime(fh["date"], errors="coerce")
    fh = wpr._dedup_scrape_baseline(fh, verbose=True)
    fh = fh[(fh["isBarrierTrial"] != True) & (fh["is_jumpout"] != True)].copy()
    fh["sect_i_l600"] = pd.to_numeric(fh["sect_i_l600"], errors="coerce")
    fh["raceShapeEarly"] = pd.to_numeric(fh["raceShapeEarly"], errors="coerce")
    fh = fh.dropna(subset=["date", "horse_id", "run_id"]).sort_values(
        ["horse_id", "date"]).reset_index(drop=True)
    return fh


def fit_pace_baseline(fit_rows):
    """Population mean sect_i_l600 per raceShapeEarly bucket, fit on
    fit_rows only."""
    d = fit_rows.dropna(subset=["sect_i_l600", "raceShapeEarly"]).copy()
    d["bucket"] = pd.cut(d["raceShapeEarly"], bins=PACE_BINS)
    return d.groupby("bucket", observed=True)["sect_i_l600"].mean()


def build_closing_merit(fh, baseline):
    """For every row, compute this run's residual (if it has the needed
    data), then for every row return the shrunk average of the PRIOR
    (up to 3) runs' residuals - the leak-safe, point-in-time feature."""
    d = fh.copy()
    d["bucket"] = pd.cut(d["raceShapeEarly"], bins=PACE_BINS)
    # .map() against a dict (not the Series directly) avoids pandas
    # propagating the bucket column's category dtype onto "expected",
    # which otherwise blocks the float subtraction below.
    d["expected"] = d["bucket"].map(baseline.to_dict()).astype(float)
    d["residual"] = d["sect_i_l600"].astype(float) - d["expected"]

    out = {}
    for _, g in d.groupby("horse_id", sort=False):
        resid = g["residual"].to_numpy()
        run_ids = g["run_id"].to_numpy()
        for i in range(len(g)):
            prior = resid[max(0, i - 3):i]
            prior = prior[~np.isnan(prior)]
            if len(prior):
                out[run_ids[i]] = _shrink(float(prior.mean()), len(prior))
    return out


def top1_strike_rate(frame, proj_col):
    f = frame.copy()
    f["rank"] = f.groupby("race_id")[proj_col].rank(ascending=False, method="first")
    top1 = f[f["rank"] == 1]
    return float(top1["won"].mean() * 100), int(top1["won"].sum()), len(top1)


def proj_of(frame, extra_terms):
    terms = list(wpr.ADJ_TERMS) + extra_terms
    return frame["_base"].to_numpy() + wpr._cap_adj_sum(frame[terms].to_numpy()).sum(axis=1)


def run():
    print("Loading and prepping raw form history...")
    fh = load_raw_form()
    fh["run_id"] = fh["run_id"].astype(str)
    print(f"  {len(fh):,} rows after dedup/trial-exclusion, "
          f"{fh['sect_i_l600'].notna().mean()*100:.1f}% have sect_i_l600, "
          f"{fh['raceShapeEarly'].notna().mean()*100:.1f}% have raceShapeEarly")

    raw_mid = fh["date"].quantile(0.5)
    raw_h1, raw_h2 = fh[fh["date"] < raw_mid], fh[fh["date"] >= raw_mid]

    print("\nFitting pace-context baseline (direction 1: on raw H1)...")
    baseline_d1 = fit_pace_baseline(raw_h1)
    print(baseline_d1)
    merit_d1 = build_closing_merit(fh, baseline_d1)

    print("\nFitting pace-context baseline (direction 2: on raw H2)...")
    baseline_d2 = fit_pace_baseline(raw_h2)
    print(baseline_d2)
    merit_d2 = build_closing_merit(fh, baseline_d2)

    print(f"\nclosing_merit coverage: direction1={len(merit_d1):,} run_ids, "
          f"direction2={len(merit_d2):,} run_ids (of {fh['run_id'].nunique():,} total)")

    print("\nRebuilding training frame (no race_speed_labels needed)...")
    full = wpr.build_training_frame(FORM_CSV, verbose=True, n_jobs=-1)
    full["date"] = pd.to_datetime(full["date"])
    full["run_id"] = full["run_id"].astype(str)

    print("\nMerging race result (won) from toprate_runners.csv by run_id...")
    tr = pd.read_csv(RUNNERS_CSV, dtype={"run_id": str}, low_memory=False,
                      usecols=["run_id", "won", "resulted", "scratched"])
    tr["resulted"] = pd.to_numeric(tr["resulted"], errors="coerce")
    tr["scratched"] = pd.to_numeric(tr["scratched"], errors="coerce")
    tr["won"] = pd.to_numeric(tr["won"], errors="coerce")
    tr = tr[(tr["resulted"] == 1) & (tr["scratched"] != 1)].dropna(subset=["won"])
    tr = tr.drop_duplicates(subset="run_id", keep="last")
    full = full.merge(tr[["run_id", "won"]], on="run_id", how="inner")

    full = add_base(full)
    non_tb_terms = [t for t in wpr.ADJ_TERMS if t != "track_barrier"]
    full = full.dropna(subset=["target", "_base", "career_avg"] + non_tb_terms +
                        ["barrier", "field_size", "track", "cur_distance"])

    mid = full["date"].quantile(0.5)
    h1, h2 = full[full["date"] < mid].copy(), full[full["date"] >= mid].copy()
    print(f"\nH1: {len(h1):,} rows (< {mid.date()}), H2: {len(h2):,} rows (>= {mid.date()})")

    h1_d1, h2_d1 = h1.copy(), h2.copy()
    add_track_barrier(h1_d1, [h1_d1, h2_d1])
    h1_d1["closing_merit"] = h1_d1["run_id"].map(merit_d1).fillna(0.0)
    h2_d1["closing_merit"] = h2_d1["run_id"].map(merit_d1).fillna(0.0)

    h1_d2, h2_d2 = h1.copy(), h2.copy()
    add_track_barrier(h2_d2, [h1_d2, h2_d2])
    h1_d2["closing_merit"] = h1_d2["run_id"].map(merit_d2).fillna(0.0)
    h2_d2["closing_merit"] = h2_d2["run_id"].map(merit_d2).fillna(0.0)

    cov = (h1_d1["closing_merit"] != 0.0).mean() * 100
    print(f"closing_merit non-zero on {cov:.1f}% of scoped rows")

    for d in (h1_d1, h2_d1, h1_d2, h2_d2):
        d["proj_base"] = proj_of(d, [])
        d["proj_cm"] = proj_of(d, ["closing_merit"])

    print("\n=== H1-fit/H2-validate direction ===")
    b_r1, b_k1, b_n1 = top1_strike_rate(h1_d1, "proj_base")
    b_r2, b_k2, b_n2 = top1_strike_rate(h2_d1, "proj_base")
    c_r1, c_k1, c_n1 = top1_strike_rate(h1_d1, "proj_cm")
    c_r2, c_k2, c_n2 = top1_strike_rate(h2_d1, "proj_cm")
    b_mae2 = mean_absolute_error(h2_d1["target"], h2_d1["proj_base"])
    c_mae2 = mean_absolute_error(h2_d1["target"], h2_d1["proj_cm"])
    print(f"  top-1 strike:  baseline H1={b_k1}/{b_n1}={b_r1:.2f}%  H2(held-out)={b_k2}/{b_n2}={b_r2:.2f}%")
    print(f"  top-1 strike:  +closing_merit H1={c_k1}/{c_n1}={c_r1:.2f}%  H2(held-out)={c_k2}/{c_n2}={c_r2:.2f}%")
    print(f"  held-out MAE:  baseline={b_mae2:.4f}  +closing_merit={c_mae2:.4f}")

    print("\n=== H2-fit/H1-validate direction ===")
    b_r2b, b_k2b, b_n2b = top1_strike_rate(h2_d2, "proj_base")
    b_r1b, b_k1b, b_n1b = top1_strike_rate(h1_d2, "proj_base")
    c_r2b, c_k2b, c_n2b = top1_strike_rate(h2_d2, "proj_cm")
    c_r1b, c_k1b, c_n1b = top1_strike_rate(h1_d2, "proj_cm")
    b_mae1 = mean_absolute_error(h1_d2["target"], h1_d2["proj_base"])
    c_mae1 = mean_absolute_error(h1_d2["target"], h1_d2["proj_cm"])
    print(f"  top-1 strike:  baseline H2={b_k2b}/{b_n2b}={b_r2b:.2f}%  H1(held-out)={b_k1b}/{b_n1b}={b_r1b:.2f}%")
    print(f"  top-1 strike:  +closing_merit H2={c_k2b}/{c_n2b}={c_r2b:.2f}%  H1(held-out)={c_k1b}/{c_n1b}={c_r1b:.2f}%")
    print(f"  held-out MAE:  baseline={b_mae1:.4f}  +closing_merit={c_mae1:.4f}")

    strike_improved = (c_r2 > b_r2) and (c_r1b > b_r1b)
    mae_improved = (c_mae2 < b_mae2) and (c_mae1 < b_mae1)
    print(f"\nTop-1 strike rate improved in BOTH held-out directions: {strike_improved} "
          f"(H2: {b_r2:.2f}% -> {c_r2:.2f}%, H1: {b_r1b:.2f}% -> {c_r1b:.2f}%)")
    print(f"Held-out MAE improved in BOTH directions: {mae_improved} "
          f"(H2: {b_mae2:.4f} -> {c_mae2:.4f}, H1: {b_mae1:.4f} -> {c_mae1:.4f})")
    if strike_improved:
        print("\nclosing_merit clears the strike-rate bar in both directions - a real, "
              "adoptable effect worth a full recalibrated rebuild before shipping.")
    else:
        print("\nclosing_merit does NOT clear the strike-rate bar in both directions - not "
              "adoptable on this test.")


if __name__ == "__main__":
    run()
