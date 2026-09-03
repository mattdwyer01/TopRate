"""
wpr_top_pick_margin_strategy_kfold.py - tests a GENUINELY DIFFERENT bet-
selection mechanism from "edge vs market" (already shown not to work -
see wpr_real_model_calibration_diagnosis.py / wpr_calibrated_edge_kfold_
validation.py: the model's calibrated probability is slightly WORSE than
the market's own, so backing disagreement-with-market just backs the
model's own noise).

WHY THIS IS DIFFERENT, NOT MORE OF THE SAME: "edge >= threshold" requires
the model to be a BETTER probability estimator than the market, which
the data says it isn't. This strategy does NOT require that. It only
requires two much weaker things: (1) the model's own TOP-1 ranking
within a race has some genuine skill (WPR was originally validated for
exactly this - rank/MAE accuracy - independent of the failed edge-vs-
market calibration test), and (2) the well-documented favourite-longshot
bias in wagering markets (short prices are, on average, slightly
UNDER-bet relative to true win probability; long prices are OVER-bet) -
neither of which requires the model to out-predict the market's
probability, just to reliably identify races where its own top pick is
a clear, standout selection. This is also the exact mechanism behind
this repo's existing (Aug 2026, pre-session) Watchlist feature
(frontend/src/lib/watchlist.ts) - "back the #1 WPR-ranked runner when it
leads #2 by >= minGap and the market still has it out at >= minPrice,
no unrated runner in the field" - which that code's own comments say
held up under an earlier chronological half-split check. This re-
validates that SAME mechanism from scratch against the REAL, CORRECTED
model (dist_edge_correction/first_up_trial_correction removed, see
PR #165) with a proper K=4 chronological fold sweep, reporting PER-FOLD
results (not just the pooled average) - a genuine effect should show up
positively across most/all folds, not just look good on average while
being driven by one lucky fold (multiple-comparisons risk from sweeping
a grid of (min_gap, min_price) combinations is real; per-fold robustness
is the check against it, not proof positive on its own).

METHOD: for every race with >=4 runners where every runner has a real
projection (has_projection True - same eligibility bar used throughout
this session), rank runners by projected_wpr. gap = rank1 - rank2 (in
WPR points). For each (min_gap, min_price) combination in the grid,
"bet" = races where gap >= min_gap AND rank1's market price >= min_price
- staking is proportional stake-to-return-RETURN_UNITS, same convention
as every other backtest this session. Reused, not refit, across K=4
chronological folds - there is no fitted parameter here (unlike the
isotonic calibration script), so this is a direct threshold sweep, not
a train/apply split; the K-fold structure here is purely for reporting
per-period robustness, not leak prevention.

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd

from wpr_calibrated_edge_kfold_validation import build_pool

MIN_GAP_GRID = [2, 3, 4, 5, 6, 8, 10]
MIN_PRICE_GRID = [2.0, 3.0, 4.0, 5.0, 7.0, 10.0]
PRICE_CAP = 26.0
RETURN_UNITS = 4
N_FOLDS = 4
MIN_FIELD_SIZE = 4


def build_top_picks(pool):
    """One row per eligible race: rank1/rank2 proj, gap, rank1's price/won."""
    pool = pool.sort_values(["race_id", "proj"], ascending=[True, False])
    field_size = pool.groupby("race_id")["proj"].transform("size")
    pool = pool[field_size >= MIN_FIELD_SIZE].copy()

    rows = []
    for race_id, g in pool.groupby("race_id"):
        g = g.sort_values("proj", ascending=False)
        if len(g) < 2:
            continue
        r1, r2 = g.iloc[0], g.iloc[1]
        rows.append({
            "race_id": race_id, "date": r1["date"],
            "gap": float(r1["proj"] - r2["proj"]),
            "price": float(r1["price"]), "won": int(r1["won"]),
        })
    return pd.DataFrame(rows)


def score(df):
    n = len(df)
    if n == 0:
        return None
    wins = int(df["won"].sum())
    stake = RETURN_UNITS / df["price"].to_numpy()
    profit = np.where(df["won"] == 1, RETURN_UNITS - stake, -stake)
    staked = stake.sum()
    total_profit = profit.sum()
    se = profit.std(ddof=1) / np.sqrt(n) if n > 1 else np.nan
    t = profit.mean() / se if se and se > 0 else np.nan
    return {"n": n, "strike": wins / n * 100, "staked": staked,
            "profit": total_profit, "roi": total_profit / staked * 100 if staked else np.nan, "t": t}


def run():
    pool = build_pool()
    print(f"Population: {len(pool):,} runners across {pool['race_id'].nunique():,} races")

    picks = build_top_picks(pool)
    picks = picks[picks["price"] <= PRICE_CAP].copy()
    picks = picks.sort_values("date").reset_index(drop=True)
    print(f"Eligible races (field>={MIN_FIELD_SIZE}, every runner projected, top pick price<=${PRICE_CAP:.0f}): "
          f"{len(picks):,}")

    n = len(picks)
    fold_edges = np.array_split(np.arange(n), N_FOLDS)
    picks["_fold"] = -1
    for i, idx in enumerate(fold_edges):
        picks.loc[picks.index[idx], "_fold"] = i
    for i in range(N_FOLDS):
        f = picks[picks["_fold"] == i]
        print(f"  fold {i}: {len(f):,} races, {f['date'].min().date()} to {f['date'].max().date()}")

    print(f"\n{'='*120}\nBASELINE: back EVERY field's top-projected runner, no gap/price filter\n{'='*120}")
    base = score(picks)
    print(f"  n={base['n']:6d}  strike={base['strike']:5.1f}%  staked={base['staked']:9.2f}u  "
          f"profit={base['profit']:+9.2f}u  ROI={base['roi']:+7.1f}%  t={base['t']:+.2f}")

    print(f"\n{'='*120}\nGRID: min_gap x min_price, POOLED across all folds\n{'='*120}")
    header = f"{'min_gap':>8}  {'min_price':>10}  {'n':>6}  {'strike':>7}  {'ROI':>8}  {'t':>6}  folds_positive"
    print(header)
    candidates = []
    for min_gap in MIN_GAP_GRID:
        for min_price in MIN_PRICE_GRID:
            sub = picks[(picks["gap"] >= min_gap) & (picks["price"] >= min_price)]
            s = score(sub)
            if s is None or s["n"] < 30:
                continue
            fold_rois = []
            for i in range(N_FOLDS):
                fsub = sub[sub["_fold"] == i]
                fs = score(fsub)
                fold_rois.append(fs["roi"] if fs and fs["n"] >= 10 else None)
            n_pos = sum(1 for r in fold_rois if r is not None and r > 0)
            n_valid_folds = sum(1 for r in fold_rois if r is not None)
            flag = " <-- ALL FOLDS POSITIVE" if n_valid_folds == N_FOLDS and n_pos == N_FOLDS else ""
            print(f"{min_gap:>8.0f}  {min_price:>10.1f}  {s['n']:>6d}  {s['strike']:>6.1f}%  "
                  f"{s['roi']:>+7.1f}%  {s['t']:>+5.2f}  {n_pos}/{n_valid_folds} folds >0{flag}")
            candidates.append((min_gap, min_price, s, fold_rois))

    print(f"\n{'='*120}\nPER-FOLD DETAIL for candidates where ALL folds are individually positive\n{'='*120}")
    robust = [(mg, mp, s, fr) for mg, mp, s, fr in candidates
              if all(r is not None and r > 0 for r in fr)]
    if not robust:
        print("  None. No (min_gap, min_price) combination was positive in every single fold -")
        print("  any pooled-positive result in the grid above is being carried by one or two")
        print("  strong folds, not a consistent effect across the whole period.")
    else:
        for min_gap, min_price, s, fold_rois in robust:
            print(f"\n  min_gap>={min_gap}, min_price>=${min_price}: pooled n={s['n']}, "
                  f"pooled ROI={s['roi']:+.1f}%, pooled t={s['t']:+.2f}")
            for i, r in enumerate(fold_rois):
                fsub = picks[(picks["gap"] >= min_gap) & (picks["price"] >= min_price) & (picks["_fold"] == i)]
                fs = score(fsub)
                print(f"    fold {i}: n={fs['n']:4d}  strike={fs['strike']:5.1f}%  ROI={fs['roi']:+7.1f}%  t={fs['t']:+.2f}")

    print("\nMultiple-comparisons caveat applies MORE here than usual - this is a grid sweep over")
    print(f"{len(MIN_GAP_GRID)*len(MIN_PRICE_GRID)} combinations. Only trust a combination that is positive")
    print("in every fold individually, not just pooled - and even then, treat it as a hypothesis for")
    print("a genuine future walk-forward period, not a result to size real stakes around yet.")


if __name__ == "__main__":
    run()
