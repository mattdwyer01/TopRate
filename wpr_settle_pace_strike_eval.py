"""
wpr_settle_pace_strike_eval.py - tests a NEW candidate ranking feature
motivated directly by TopRate's own published Pace Bias statistics
(toprate.helpscoutdocs.com/article/225): for genuine market chances up to
$10 SP, on-pace runners' win strike rate swings from ~34% (slow early
shape) down to ~15% (fast early shape), and backmarkers swing the OPPOSITE
way (~12% up to ~25%) - a huge, monotonic, large-sample effect (replicated
directly on our own 476,719-row form history in this session: see chat).

WHY THIS IS DIFFERENT FROM own_pace / own_settle (both already tested and
REJECTED this session, see wpr_projection.py's own experiment log)
  own_pace and own_settle both ask "does THIS horse personally run above
  its own level when [tempo/settle-band] matches today's prediction" - a
  PER-HORSE OWN-HISTORY lookup, shrunk to ~0 for any horse without enough
  of its own matching-band history. Both failed (worse held-out MAE).

  This candidate asks a POPULATION-LEVEL question instead, structurally
  identical to track_barrier (the one ADJ_TERM that already uses a fitted
  population lookup, not an own-history one): "across ALL horses, how much
  does being predicted to sit in settle-band X, in a race predicted to run
  at pace-shape Y, shift the residual (target - career_avg)". It doesn't
  need the same horse to have run in that exact scenario before, so it
  isn't diluted the same way for lightly-raced horses. It hasn't been
  tried in this form.

INPUTS (both leak-safe, both already exist in the codebase)
  - cur_settle_band: this horse's PREDICTED running position today
    (Leader/On-pace/Midfield/Back - see wpr_projection._settle_band),
    computed from PRIOR runs + barrier only. Already emitted by
    build_features/build_training_frame - free, no extra work.
  - pace_label: the race-WIDE predicted early tempo (Hot/Fast/Even/Slow),
    from race_speed_estimate.py run with a prior-only cutoff (same
    leak-safe labels built for the own_pace backtest - see
    wpr_own_pace_backtest.build_race_speed_labels). LOW CONFIDENCE
    (~+0.24 held-out correlation with actual raceShapeEarly - see
    domain.ts) - the real-world effect will be damped by this forecast
    noise relative to the raw actual-result-based statistic above.

METHODOLOGY (same bar as every other candidate this session)
  - Fit a shrunk (settle_band, pace_label) -> residual lookup, exactly
    like track_barrier's shrinkage (see add_track_barrier), on one
    chronological half; apply to both halves; repeat with roles swapped.
  - Report BOTH top-1 strike rate (the user's current ask) and held-out
    MAE (the model's existing adoption bar) in both directions. Adopt-
    worthy only if strike rate (or MAE) improves in BOTH directions,
    same standard as own_pace/track_barrier/etc.

USAGE
  python wpr_settle_pace_strike_eval.py --since 2026-03-01

NO EM DASHES policy: hyphens only in this file.
"""
import argparse

import numpy as np
import pandas as pd
from sklearn.metrics import mean_absolute_error

import wpr_projection as wpr
from wpr_own_pace_backtest import build_race_speed_labels, add_base, add_track_barrier

FORM_CSV = "wpr_form_history.csv.gz"
RUNNERS_CSV = "toprate_runners.csv"
SETTLE_PACE_K = 50.0


def add_settle_pace(fit, frames):
    """Fits a shrunk (cur_settle_band, pace_label) -> residual lookup on
    `fit` (population-level, NOT per-horse - see module docstring), applies
    it to every frame in `frames`. Unseen combos, or rows missing either
    input, get 0.0 (no adjustment) - same "unseen -> 0" contract as
    track_barrier."""
    key = fit["cur_settle_band"].astype(str) + "|" + fit["pace_label"].astype(str)
    resid = fit["target"] - fit["career_avg"]
    tmp = pd.DataFrame({"key": key, "residual": resid})
    tmp = tmp[fit["cur_settle_band"].notna() & fit["pace_label"].notna()]
    global_mean = tmp["residual"].mean()
    stats = tmp.groupby("key")["residual"].agg(["mean", "count"])
    lookup = {}
    for k, row in stats.iterrows():
        n, m = row["count"], row["mean"]
        shrunk = (n * m + SETTLE_PACE_K * global_mean) / (n + SETTLE_PACE_K)
        lookup[k] = float(max(-wpr._OWN_DELTA_CAP, min(wpr._OWN_DELTA_CAP, shrunk - global_mean)))
    for frame in frames:
        k = frame["cur_settle_band"].astype(str) + "|" + frame["pace_label"].astype(str)
        frame["settle_pace"] = k.map(lookup).fillna(0.0)
        frame.loc[frame["cur_settle_band"].isna() | frame["pace_label"].isna(), "settle_pace"] = 0.0


def proj_of(frame, extra_terms):
    terms = list(wpr.ADJ_TERMS) + extra_terms
    return frame["_base"].to_numpy() + wpr._cap_adj_sum(frame[terms].to_numpy()).sum(axis=1)


def top1_strike_rate(frame, proj_col):
    f = frame.copy()
    f["rank"] = f.groupby("race_id")[proj_col].rank(ascending=False, method="first")
    top1 = f[f["rank"] == 1]
    return float(top1["won"].mean() * 100), int(top1["won"].sum()), len(top1)


def run(since):
    labels = build_race_speed_labels(since)

    print("\nRebuilding training frame (own_pace comes along unused; "
          "cur_settle_band is already free from build_features)...")
    full = wpr.build_training_frame(FORM_CSV, verbose=True, race_speed_labels=labels, n_jobs=-1)
    full["date"] = pd.to_datetime(full["date"])
    full["run_id"] = full["run_id"].astype(str)
    full["pace_label"] = full["run_id"].map(labels)

    print("\nMerging race result (won/race_id) from toprate_runners.csv by run_id...")
    tr = pd.read_csv(RUNNERS_CSV, dtype={"run_id": str, "race_id": str}, low_memory=False,
                      usecols=["run_id", "race_id", "won", "resulted", "scratched"])
    tr["resulted"] = pd.to_numeric(tr["resulted"], errors="coerce")
    tr["scratched"] = pd.to_numeric(tr["scratched"], errors="coerce")
    tr["won"] = pd.to_numeric(tr["won"], errors="coerce")
    tr = tr[(tr["resulted"] == 1) & (tr["scratched"] != 1)].dropna(subset=["won", "race_id"])
    tr = tr.drop_duplicates(subset="run_id", keep="last")
    full = full.merge(tr[["run_id", "race_id", "won"]], on="run_id", how="inner")

    full = add_base(full)
    non_tb_terms = [t for t in wpr.ADJ_TERMS if t != "track_barrier"]
    full = full.dropna(subset=["target", "_base", "career_avg"] + non_tb_terms +
                        ["barrier", "field_size", "track", "cur_distance"])
    scoped = full[full["date"] >= pd.Timestamp(since)].copy()
    labelled = scoped["pace_label"].notna().mean() * 100
    print(f"\nScoped rows: {len(scoped):,} (has a leak-safe pace_label on {labelled:.1f}%, "
          f"cur_settle_band non-null on {scoped['cur_settle_band'].notna().mean()*100:.1f}%)")
    print("settle_band x pace_label coverage (both present):")
    both = scoped.dropna(subset=["cur_settle_band", "pace_label"])
    print(pd.crosstab(both["cur_settle_band"], both["pace_label"]))

    mid = scoped["date"].quantile(0.5)
    h1, h2 = scoped[scoped["date"] < mid].copy(), scoped[scoped["date"] >= mid].copy()
    print(f"\nH1: {len(h1):,} rows (< {mid.date()}), H2: {len(h2):,} rows (>= {mid.date()})")

    # Direction 1: fit on H1, apply to both halves. Direction 2: fit on H2.
    h1_d1, h2_d1 = h1.copy(), h2.copy()
    add_track_barrier(h1_d1, [h1_d1, h2_d1])
    add_settle_pace(h1_d1, [h1_d1, h2_d1])
    h1_d2, h2_d2 = h1.copy(), h2.copy()
    add_track_barrier(h2_d2, [h1_d2, h2_d2])
    add_settle_pace(h2_d2, [h1_d2, h2_d2])

    for d in (h1_d1, h2_d1, h1_d2, h2_d2):
        d["proj_base"] = proj_of(d, [])
        d["proj_settle_pace"] = proj_of(d, ["settle_pace"])

    print("\n=== H1-fit/H2-validate direction ===")
    b_r1, b_k1, b_n1 = top1_strike_rate(h1_d1, "proj_base")
    b_r2, b_k2, b_n2 = top1_strike_rate(h2_d1, "proj_base")
    c_r1, c_k1, c_n1 = top1_strike_rate(h1_d1, "proj_settle_pace")
    c_r2, c_k2, c_n2 = top1_strike_rate(h2_d1, "proj_settle_pace")
    b_mae2 = mean_absolute_error(h2_d1["target"], h2_d1["proj_base"])
    c_mae2 = mean_absolute_error(h2_d1["target"], h2_d1["proj_settle_pace"])
    print(f"  top-1 strike:  baseline H1={b_k1}/{b_n1}={b_r1:.2f}%  H2(held-out)={b_k2}/{b_n2}={b_r2:.2f}%")
    print(f"  top-1 strike:  +settle_pace H1={c_k1}/{c_n1}={c_r1:.2f}%  H2(held-out)={c_k2}/{c_n2}={c_r2:.2f}%")
    print(f"  held-out MAE:  baseline={b_mae2:.4f}  +settle_pace={c_mae2:.4f}")

    print("\n=== H2-fit/H1-validate direction ===")
    b_r2b, b_k2b, b_n2b = top1_strike_rate(h2_d2, "proj_base")
    b_r1b, b_k1b, b_n1b = top1_strike_rate(h1_d2, "proj_base")
    c_r2b, c_k2b, c_n2b = top1_strike_rate(h2_d2, "proj_settle_pace")
    c_r1b, c_k1b, c_n1b = top1_strike_rate(h1_d2, "proj_settle_pace")
    b_mae1 = mean_absolute_error(h1_d2["target"], h1_d2["proj_base"])
    c_mae1 = mean_absolute_error(h1_d2["target"], h1_d2["proj_settle_pace"])
    print(f"  top-1 strike:  baseline H2={b_k2b}/{b_n2b}={b_r2b:.2f}%  H1(held-out)={b_k1b}/{b_n1b}={b_r1b:.2f}%")
    print(f"  top-1 strike:  +settle_pace H2={c_k2b}/{c_n2b}={c_r2b:.2f}%  H1(held-out)={c_k1b}/{c_n1b}={c_r1b:.2f}%")
    print(f"  held-out MAE:  baseline={b_mae1:.4f}  +settle_pace={c_mae1:.4f}")

    strike_improved = (c_r2 > b_r2) and (c_r1b > b_r1b)
    mae_improved = (c_mae2 < b_mae2) and (c_mae1 < b_mae1)
    print(f"\nTop-1 strike rate improved in BOTH held-out directions: {strike_improved} "
          f"(H2: {b_r2:.2f}% -> {c_r2:.2f}%, H1: {b_r1b:.2f}% -> {c_r1b:.2f}%)")
    print(f"Held-out MAE improved in BOTH directions: {mae_improved} "
          f"(H2: {b_mae2:.4f} -> {c_mae2:.4f}, H1: {b_mae1:.4f} -> {c_mae1:.4f})")
    if strike_improved:
        print("\nsettle_pace clears the strike-rate bar in both directions - a real, "
              "adoptable effect worth a full recalibrated rebuild before shipping.")
    else:
        print("\nsettle_pace does NOT clear the strike-rate bar in both directions - not "
              "adoptable on this test.")


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--since", type=str, default=None,
                     help="only label/test races on or after this date (default: 6 months back)")
    args = ap.parse_args()
    since = args.since or (pd.Timestamp.today() - pd.Timedelta(days=183)).strftime("%Y-%m-%d")
    run(since)
