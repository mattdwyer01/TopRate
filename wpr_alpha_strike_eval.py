"""
wpr_alpha_strike_eval.py - does _BASE_BLEND_ALPHA (currently 0.50, chosen for
interpretability over the previously-validated 0.80) affect the model's
TOP-1 STRIKE RATE (does the highest-rated runner actually win), as opposed
to MAE (which is what alpha was last evaluated against)?

WHY THIS EXISTS
  wpr_projection.py's base = alpha*wpr_nett + (1-alpha)*ewm3. A prior
  session found alpha=0.80 beats 0.50 on held-out MAE, but it was reverted
  to 0.50 for interpretability, not because 0.80 was wrong. The user's new
  ask is specifically about strike rate (does the top pick win, not how
  close the predicted WPR number is), which is a different objective:
  alpha's effect on MAE and on within-race RANKING are not guaranteed to
  point the same way, since MAE cares about the absolute gap and ranking
  only cares about relative order.

METHODOLOGY
  - Reuses wpr_projection.build_training_frame() ONCE (n_jobs=-1, no
    race_speed_labels - this isn't about own_pace) to get wpr_nett, ewm3,
    avg_last3, career_avg, and the (alpha-independent - they're per-horse
    own-history deltas relative to career_avg, computed before any base
    blending) ADJ_TERMS for every historical (horse, run).
  - Merges in race_id/won/resulted/scratched from toprate_runners.csv by
    run_id (str) to know which runner actually won each historical race -
    build_training_frame's own "target" is the horse's FUTURE WPR, not a
    race result, so this join is required.
  - For each alpha candidate: base = alpha*wpr_nett + (1-alpha)*ewm3
    (uncalibrated - see caveat below), proj = base + sum(ADJ_TERMS,
    capped same as production), rank = argsort(-proj) within race_id.
  - Reports top-1 strike rate (wprp_rank==1 -> won) on a chronological
    half-split, BOTH directions, matching every other alpha/ADJ_TERMS
    decision's own bar in this project (own_pace backtest, etc).

CAVEAT: this test is UNCALIBRATED (skips _calibrate_base's piecewise
slope/intercept, which was fit specifically for alpha=0.50 and would be
wrong to reuse unchanged for a different alpha - refitting calibration
per alpha candidate is a real project, not a quick sanity check). Since
calibration is piecewise by population percentile (not per-race), it CAN
reorder runners within a race relative to raw base, so this result is
directionally informative about alpha's effect on ranking, not a promise
that the exact same gap would survive a properly recalibrated production
rebuild. Treat a clear win here as "worth doing the full recalibration",
not as "ready to ship".

USAGE
  python wpr_alpha_strike_eval.py

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd

import wpr_projection as wpr
from wpr_own_pace_backtest import add_track_barrier

FORM_CSV = "wpr_form_history.csv.gz"
RUNNERS_CSV = "toprate_runners.csv"
ALPHA_GRID = [0.30, 0.40, 0.50, 0.60, 0.70, 0.80, 0.90]


def add_uncalibrated_proj(D, alpha):
    both = D["wpr_nett"].notna() & D["ewm3"].notna()
    base = np.where(both, alpha * D["wpr_nett"] + (1 - alpha) * D["ewm3"],
                    D["wpr_nett"].fillna(D["ewm3"]))
    base = pd.Series(base, index=D.index).fillna(D["avg_last3"]).fillna(D["career_avg"])
    adj = wpr._cap_adj_sum(D[wpr.ADJ_TERMS].to_numpy()).sum(axis=1)
    return base + adj


def top1_strike_rate(frame):
    """% of races where the runner with the LOWEST proj-rank (rank 1) won.
    frame must have race_id, proj, won."""
    if len(frame) == 0:
        return float("nan"), 0, 0
    frame = frame.copy()
    frame["rank"] = frame.groupby("race_id")["proj"].rank(ascending=False, method="first")
    top1 = frame[frame["rank"] == 1]
    return float(top1["won"].mean() * 100), int(top1["won"].sum()), len(top1)


def run():
    print("Building training frame (no race_speed_labels needed for this test)...")
    full = wpr.build_training_frame(FORM_CSV, verbose=True, n_jobs=-1)
    full["date"] = pd.to_datetime(full["date"])
    full["run_id"] = full["run_id"].astype(str)

    print("\nMerging race result (won/race_id) from toprate_runners.csv by run_id...")
    tr = pd.read_csv(RUNNERS_CSV, dtype={"run_id": str, "race_id": str}, low_memory=False,
                      usecols=["run_id", "race_id", "won", "resulted", "scratched"])
    tr["resulted"] = pd.to_numeric(tr["resulted"], errors="coerce")
    tr["scratched"] = pd.to_numeric(tr["scratched"], errors="coerce")
    tr["won"] = pd.to_numeric(tr["won"], errors="coerce")
    tr = tr[(tr["resulted"] == 1) & (tr["scratched"] != 1)].dropna(subset=["won", "race_id"])
    tr = tr.drop_duplicates(subset="run_id", keep="last")

    # full already carries its own race_id (build_training_frame's
    # _horse_feature_rows retains it) - merging tr's race_id too would
    # collide into race_id_x/race_id_y and silently break every
    # groupby("race_id") below, so only "won" is pulled in here.
    full = full.merge(tr[["run_id", "won"]], on="run_id", how="inner")
    # track_barrier isn't produced by build_training_frame (needs an actual
    # fitted lookup, unlike every other ADJ_TERMS entry - see
    # wpr_own_pace_backtest.add_track_barrier) so it's excluded here and
    # fitted per half below, on the columns it needs.
    non_tb_terms = [t for t in wpr.ADJ_TERMS if t != "track_barrier"]
    full = full.dropna(subset=["wpr_nett", "avg_last3", "career_avg"] + non_tb_terms +
                        ["barrier", "field_size", "track", "cur_distance"])
    print(f"Rows with a known race result and enough history for a base: {len(full):,} "
          f"({full['race_id'].nunique():,} races)")

    mid = full["date"].quantile(0.5)
    h1, h2 = full[full["date"] < mid].copy(), full[full["date"] >= mid].copy()
    # track_barrier is alpha-independent (fit from target - career_avg, no
    # base blend involved) so it only needs fitting once per half, not once
    # per alpha candidate below. Fit on each half's own data and apply to
    # itself - each half here is an independent "what would strike rate
    # look like" snapshot, not a fit/validate pair (that's what H1-vs-H2
    # AGREEMENT further down is for), so this in-sample fit is fine.
    add_track_barrier(h1, [h1])
    add_track_barrier(h2, [h2])
    h1 = h1.dropna(subset=["track_barrier"])
    h2 = h2.dropna(subset=["track_barrier"])
    print(f"H1: {len(h1):,} rows (< {mid.date()}), H2: {len(h2):,} rows (>= {mid.date()})\n")

    print("Nothing is 'fit' per alpha - it's a fixed blend weight, not a regression - so both "
          "halves are just independently reported at each alpha; the real question is whether "
          "the ranking of alpha candidates by top-1 strike rate agrees across H1 and H2.\n")
    print(f"{'alpha':>6s} | {'H1 top-1 strike':>20s} | {'H2 top-1 strike':>20s}")
    results = []
    for alpha in ALPHA_GRID:
        h1["proj"] = add_uncalibrated_proj(h1, alpha)
        h2["proj"] = add_uncalibrated_proj(h2, alpha)
        r1, k1, n1 = top1_strike_rate(h1)
        r2, k2, n2 = top1_strike_rate(h2)
        print(f"{alpha:6.2f} | {k1:4d}/{n1:5d} = {r1:5.2f}%    | {k2:4d}/{n2:5d} = {r2:5.2f}%")
        results.append((alpha, r1, r2))

    cur = next(r for r in results if r[0] == 0.50)
    best_h1 = max(results, key=lambda r: r[1])
    best_h2 = max(results, key=lambda r: r[2])
    print(f"\nCurrent production alpha=0.50: H1={cur[1]:.2f}%, H2={cur[2]:.2f}%")
    print(f"Best alpha on H1: {best_h1[0]:.2f} ({best_h1[1]:.2f}%)")
    print(f"Best alpha on H2: {best_h2[0]:.2f} ({best_h2[1]:.2f}%)")
    if best_h1[0] == best_h2[0] and best_h1[0] != 0.50:
        print(f"\nSame alpha ({best_h1[0]:.2f}) wins on BOTH halves independently - a real, "
              f"consistent signal by this project's own standard, worth a full recalibrated "
              f"rebuild to confirm before shipping.")
    else:
        print("\nBest alpha differs (or ties current) across the two halves - not a consistent "
              "enough signal to justify reopening the alpha decision on this test alone.")


if __name__ == "__main__":
    run()
