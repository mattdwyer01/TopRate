"""
wpr_real_correction_revalidation.py - re-validates dist_edge_correction
and first_up_trial_correction (both added directly to `adj` in the real
project_race(), bypassing _CALIB_ADJ_SLOPE) using the REAL model, not
the reconstruction that was just shown to disagree with the live
dashboard (wpr_full_history_current_model_breakdown.py's docstring has
the full story: recomputing Aug 3 - Sep 1 with the real project_race()
gave -17.3% ROI at beta=0.3, matching the live dashboard's own -18.1%,
while the reconstruction said the same days were +46.7%).

WHY THIS MATTERS MORE FOR THESE TWO TERMS SPECIFICALLY: both were
adopted THIS session on strike-rate/ROI grounds ALONE, explicitly
DESPITE worse MAE, via the reconstruction's methodology
(wpr_dist_edge_correction_kfold_test.py, wpr_first_up_trial_correction_
kfold_test.py). If that methodology's strike-rate/ROI numbers can't be
trusted, the entire justification for shipping these two corrections
collapses - they are live in production right now on the weakest
possible evidence.

METHOD: both corrections are PURELY ADDITIVE in project_race() - added
to `adj` after every other term, and surfaced unmodified in the
`contributions` dict, with no feedback into base_wpr, confidence, or any
other term. So instead of re-running project_race() three more times
(once per with/without combination), this runs it ONCE (capturing both
correction contributions alongside projected_wpr) and reconstructs all
four variants (both / dist_edge only / first_up only / neither) by
simple subtraction:
    proj_neither    = wprp_proj - dist_edge_contrib - first_up_contrib
    proj_dist_only  = wprp_proj - first_up_contrib
    proj_firstup_only = wprp_proj - dist_edge_contrib
    proj_both       = wprp_proj (already the shipped default)
Each variant gets its own real per-race softmax edge at beta=0.3 (same
method already validated against the live dashboard) and real strike-
rate/ROI, computed identically across the SAME 2026-04-26 to
2026-09-01 history, over the SAME held-out runners (dist_edge_correction
scored on the dist_edge!=0 subset, first_up_trial_correction scored on
the runs_this_camp==1-with-trial subset, "both" and "neither" scored
over the union of affected runners so the comparison covers everyone
either correction could possibly touch).

NO EM DASHES policy: hyphens only in this file.
"""
import time

import numpy as np
import pandas as pd

import wpr_projection as wpr

RUNNERS_CSV = "toprate_runners.csv"
FORM_CSV = "wpr_form_history.csv.gz"
BETA = 0.30
EDGE_THRESHOLD = 0.05
PRICE_CAP = 26.0
RETURN_UNITS = 4


def load_form_history():
    print("Reading form history (once)...")
    fh_raw = pd.read_csv(FORM_CSV, dtype={"horse": str, "horse_id": str}, low_memory=False)
    fh_raw["horse_lc"] = fh_raw["horse"].astype(str).str.strip().str.lower()
    fh_raw["date"] = pd.to_datetime(fh_raw["date"], errors="coerce")
    fh_raw["wpr"] = pd.to_numeric(fh_raw["wpr"], errors="coerce")

    fh = fh_raw.dropna(subset=["date", "wpr"])
    if "isBarrierTrial" in fh.columns:
        fh = fh[fh["isBarrierTrial"].fillna(0).astype(int) == 0]
    fh = fh.sort_values(["horse_lc", "date"])
    form_by_horse = dict(tuple(fh.groupby("horse_lc")))

    trial_by_horse = {}
    if "isBarrierTrial" in fh_raw.columns or "is_jumpout" in fh_raw.columns:
        is_trial = pd.Series(False, index=fh_raw.index)
        if "isBarrierTrial" in fh_raw.columns:
            is_trial |= fh_raw["isBarrierTrial"].fillna(0).astype(int) == 1
        if "is_jumpout" in fh_raw.columns:
            is_trial |= fh_raw["is_jumpout"].fillna(0).astype(int) == 1
        trial_fh = fh_raw[is_trial & fh_raw["date"].notna()].dropna(subset=["date"])
        trial_fh = trial_fh.sort_values(["horse_lc", "date"])
        trial_by_horse = dict(tuple(trial_fh.groupby("horse_lc")))
    print(f"  form_by_horse: {len(form_by_horse):,} horses, trial_by_horse: {len(trial_by_horse):,} horses")
    return form_by_horse, trial_by_horse


def project_date(day_df, race_date, form_by_horse, trial_by_horse):
    out = {}
    for race_id, race in day_df.groupby("race_id"):
        active_field_size = int((race.get("scratched", pd.Series([0] * len(race), index=race.index))
                                  .fillna(0).astype(int) != 1).sum())
        runners, idx_order = [], []
        for idx, r in race.iterrows():
            horse_lc = str(r.get("horse", "")).strip().lower()
            hist = form_by_horse.get(horse_lc)
            prior = hist[hist["date"] < race_date] if hist is not None else None
            trial_hist = trial_by_horse.get(horse_lc)
            trial_prior = trial_hist[trial_hist["date"] < race_date] if trial_hist is not None else None
            going = r.get("going") or "Good 4"
            runners.append({
                "prior_runs": prior, "trial_runs": trial_prior,
                "cur_distance": r.get("distance") or 1400,
                "cur_track": r.get("venue") or "",
                "cur_track_grading": r.get("track_grading"),
                "cur_race_class": r.get("race_class"),
                "cur_field_size": active_field_size,
                "cur_wpr_nett": r.get("wpr_nett"),
                "cur_barrier": r.get("barrier"),
                "cur_gear_changes": r.get("gear_changes"),
                "cur_trainer_win_pct_365d": r.get("trainer_win_pct_365d"),
                "cur_jockey_win_pct_90d": r.get("jockey_win_pct_90d"),
                "cur_going": going,
            })
            idx_order.append(idx)
        try:
            results = wpr.project_race(runners, race_date=race_date)
        except Exception as e:
            print(f"    projection error on race {race_id}: {e}")
            continue
        for idx, res in zip(idx_order, results):
            contrib = res.get("adjustment_contributions") or {}
            out[idx] = {
                "has_projection": bool(res.get("has_projection")),
                "projected_wpr": res.get("projected_wpr"),
                "dist_edge_contrib": contrib.get("dist_edge_correction", 0.0) or 0.0,
                "first_up_contrib": contrib.get("first_up_trial_correction", 0.0) or 0.0,
            }
    return out


def edge_for_variant(pool, proj_col, beta):
    """Per-race softmax edge using proj_col as the projection, restricted
    to races where every scored runner has a usable price - same rule as
    SummaryTab.tsx's collectPicks eligibility."""
    def _edge(g):
        proj = g[proj_col].to_numpy(dtype=float)
        price = g["price"].to_numpy(dtype=float)
        e = np.exp(beta * (proj - proj.max()))
        model_prob = e / e.sum()
        inv = 1.0 / price
        mkt_prob = inv / inv.sum()
        return pd.Series(model_prob - mkt_prob, index=g.index)
    return pool.groupby("race_id", group_keys=False).apply(_edge)


def score(pool, proj_col, label):
    edges = edge_for_variant(pool, proj_col, BETA)
    bets = pool[(edges >= EDGE_THRESHOLD) & (pool["price"] <= PRICE_CAP)].copy()
    if len(bets) == 0:
        print(f"  {label}: no qualifying bets")
        return
    stake = RETURN_UNITS / bets["price"].to_numpy()
    profit = np.where(bets["won"] == 1, RETURN_UNITS - stake, -stake)
    staked = stake.sum()
    total_profit = profit.sum()
    se = profit.std(ddof=1) / np.sqrt(len(profit)) if len(profit) > 1 else np.nan
    t = profit.mean() / se if se and se > 0 else np.nan
    strike = bets["won"].mean() * 100
    print(f"  {label:<28} n={len(bets):5d}  strike={strike:5.1f}%  staked={staked:8.2f}u  "
          f"profit={total_profit:+8.2f}u  ROI={total_profit/staked*100:+7.1f}%  t={t:+.2f}")


def run():
    print("Reading toprate_runners.csv...")
    runners = pd.read_csv(RUNNERS_CSV, low_memory=False,
                           dtype={"race_id": str, "horse": str, "venue": str, "state": str})
    runners["date"] = pd.to_datetime(runners["date"], errors="coerce")
    runners["resulted"] = pd.to_numeric(runners["resulted"], errors="coerce")
    runners = runners[runners["resulted"] == 1].copy()
    runners = runners.dropna(subset=["date", "race_id"])
    dates = sorted(runners["date"].dt.date.unique())
    print(f"Resulted rows: {len(runners):,} across {len(dates)} dates "
          f"({dates[0]} to {dates[-1]})")

    form_by_horse, trial_by_horse = load_form_history()

    print("\nProjecting every historical day (capturing correction contributions)...")
    t0 = time.time()
    proj_col = pd.Series(index=runners.index, dtype=float)
    dist_edge_col = pd.Series(0.0, index=runners.index)
    first_up_col = pd.Series(0.0, index=runners.index)
    has_proj_col = pd.Series(False, index=runners.index)
    for di, d in enumerate(dates):
        day_df = runners[runners["date"].dt.date == d]
        result = project_date(day_df, pd.Timestamp(d), form_by_horse, trial_by_horse)
        for idx, r in result.items():
            has_proj_col.at[idx] = r["has_projection"]
            if r["has_projection"]:
                proj_col.at[idx] = r["projected_wpr"]
                dist_edge_col.at[idx] = r["dist_edge_contrib"]
                first_up_col.at[idx] = r["first_up_contrib"]
        if (di + 1) % 10 == 0 or di == len(dates) - 1:
            print(f"  ... {di+1}/{len(dates)} dates ({time.time()-t0:.0f}s elapsed)")

    runners["wprp_proj"] = proj_col
    runners["dist_edge_contrib"] = dist_edge_col
    runners["first_up_contrib"] = first_up_col
    runners["has_projection"] = has_proj_col
    print(f"\nTotal: {int(has_proj_col.sum()):,} / {len(runners):,} runners projected in {time.time()-t0:.0f}s")
    print(f"Runners with a nonzero dist_edge_correction: {(dist_edge_col != 0).sum():,}")
    print(f"Runners with a nonzero first_up_trial_correction: {(first_up_col != 0).sum():,}")

    pool = runners[runners["has_projection"]].copy()
    sp = pd.to_numeric(pool["fixed_win_price"], errors="coerce")
    sp_fallback = pd.to_numeric(pool["starting_price_sp"], errors="coerce")
    pool["price"] = sp.fillna(sp_fallback)
    pool = pool.dropna(subset=["price"])
    pool = pool[pool["price"] > 1.0]
    pool["won"] = pd.to_numeric(pool["won"], errors="coerce").fillna(0).astype(int)

    pool["proj_both"] = pool["wprp_proj"]
    pool["proj_neither"] = pool["wprp_proj"] - pool["dist_edge_contrib"] - pool["first_up_contrib"]
    pool["proj_distonly"] = pool["wprp_proj"] - pool["first_up_contrib"]
    pool["proj_firstuponly"] = pool["wprp_proj"] - pool["dist_edge_contrib"]

    print(f"\n{'='*100}\nDIST_EDGE_CORRECTION: scored on dist_edge_contrib != 0 subset\n{'='*100}")
    dist_subset = pool[pool["dist_edge_contrib"] != 0]
    print(f"Subset size: {len(dist_subset):,}")
    score(dist_subset, "proj_both", "shipped (with dist_edge)")
    score(dist_subset, "proj_firstuponly", "without dist_edge")

    print(f"\n{'='*100}\nFIRST_UP_TRIAL_CORRECTION: scored on first_up_contrib != 0 subset\n{'='*100}")
    firstup_subset = pool[pool["first_up_contrib"] != 0]
    print(f"Subset size: {len(firstup_subset):,}")
    score(firstup_subset, "proj_both", "shipped (with first_up)")
    score(firstup_subset, "proj_distonly", "without first_up")

    print(f"\n{'='*100}\nBOTH CORRECTIONS: scored on the union (either correction nonzero)\n{'='*100}")
    union_subset = pool[(pool["dist_edge_contrib"] != 0) | (pool["first_up_contrib"] != 0)]
    print(f"Subset size: {len(union_subset):,}")
    score(union_subset, "proj_both", "shipped (both corrections)")
    score(union_subset, "proj_neither", "neither correction")
    score(union_subset, "proj_distonly", "dist_edge only")
    score(union_subset, "proj_firstuponly", "first_up only")

    print(f"\n{'='*100}\nWHOLE POPULATION (for reference, unaffected runners included)\n{'='*100}")
    score(pool, "proj_both", "shipped (both corrections)")
    score(pool, "proj_neither", "neither correction")

    print("\nSame multiple-comparisons caveat as always: one backtest, not a guarantee.")


if __name__ == "__main__":
    run()
