"""
wpr_full_history_current_model_breakdown.py - the DEFINITIVE daily/state/
quality/state-x-quality breakdown, using the REAL wpr.project_race()
(the exact function the live pipeline calls) across the FULL historical
range (2026-04-26 to 2026-09-01), at beta=0.3.

WHY THIS REPLACES wpr_beta03_daily_state_summary.py and wpr_summary_tab_
beta_comparison.py: those scripts reconstruct the model as `_base +
_cap_adj_sum(ADJ_TERMS)*_CALIB_ADJ_SLOPE`, with track_barrier/closing_
merit/trainer_merit/jockey_merit populated by SEPARATELY re-fitting
bucket lookups on a leak-free half-split (wpr_own_pace_backtest.
add_track_barrier, wpr_trainer_jockey_adj_strike_eval.add_closing_merit/
fit_bucket_lookup/apply_bucket) rather than using wpr_projection.py's
own already-shipped, fixed computation of those same terms, and never
included dist_edge_correction/first_up_trial_correction (both added
directly to `adj` in the real project_race(), bypassing _CALIB_ADJ_
SLOPE entirely). Confirmed live Sep 2026: recomputing the SAME Aug 3 -
Sep 1 window with this script's approach (verbatim wpr.project_race())
gives -17.3% ROI at beta=0.3, matching toprate_data.json's own live
numbers (-18.1% ROI) almost exactly - while the reconstruction script
said the SAME calendar days were +46.7% ROI. The reconstruction is not
a trustworthy stand-in for the real model; this script is.

METHOD: reimplements toprate_daily.compute_wpr_projection()'s own per-
race construction verbatim (same "base" dict fields, same active_field_
size/scratched handling, same prior_runs/trial_runs split) calling
wpr.project_race() directly, just restructured to read wpr_form_
history.csv.gz ONCE up front (that function is designed to be called
once/day in the real pipeline, not looped 104 times) - a pure
performance restructuring, not a logic change. Edge computed exactly as
SummaryTab.tsx's computeEffectiveEdges (per-race softmax(beta*proj),
edge = model_prob - market_prob). Staking: proportional stake-to-
return-RETURN_UNITS, matching the dashboard's own convention.

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

SCRATCH_DIR = "/tmp/claude-0/-home-user-TopRate/37b9fca0-b163-5591-8763-1dcf84252930/scratchpad"
DAILY_CSV_OUT = f"{SCRATCH_DIR}/full_current_model_daily_summary.csv"
STATE_CSV_OUT = f"{SCRATCH_DIR}/full_current_model_state_summary.csv"
QUALITY_CSV_OUT = f"{SCRATCH_DIR}/full_current_model_quality_summary.csv"
STATE_QUALITY_CSV_OUT = f"{SCRATCH_DIR}/full_current_model_state_quality_summary.csv"
BETS_CSV_OUT = f"{SCRATCH_DIR}/full_current_model_all_bets.csv"

QUALITY_BINS = [0, 20_000, 30_000, 50_000, 100_000, float("inf")]
QUALITY_LABELS = ["Bush (<=20k)", "Provincial (20-30k)", "Midweek Metro (30-50k)",
                   "Feature (50-100k)", "Stakes/Group (>100k)"]


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
            out[idx] = {"has_projection": bool(res.get("has_projection")),
                        "projected_wpr": res.get("projected_wpr")}
    return out


def edge_for_race(g):
    proj = g["proj"].to_numpy(dtype=float)
    price = g["price"].to_numpy(dtype=float)
    e = np.exp(BETA * (proj - proj.max()))
    model_prob = e / e.sum()
    inv = 1.0 / price
    mkt_prob = inv / inv.sum()
    return pd.Series(model_prob - mkt_prob, index=g.index)


def summarize(g):
    n = len(g)
    wins = int(g["won"].sum())
    stake = RETURN_UNITS / g["price"].to_numpy()
    profit = np.where(g["won"] == 1, RETURN_UNITS - stake, -stake)
    staked = float(stake.sum())
    total_profit = float(profit.sum())
    se = profit.std(ddof=1) / np.sqrt(n) if n > 1 else np.nan
    t = profit.mean() / se if se and se > 0 else np.nan
    return pd.Series({
        "n_bets": n, "wins": wins,
        "strike_pct": wins / n * 100 if n else np.nan,
        "staked_u": staked, "profit_u": total_profit,
        "roi_pct": total_profit / staked * 100 if staked else np.nan,
        "t_stat": t,
    })


def print_table(df, title, formatters=None):
    fmt = formatters or {
        "strike_pct": "{:.1f}%".format, "roi_pct": "{:+.1f}%".format,
        "staked_u": "{:.2f}u".format, "profit_u": "{:+.2f}u".format, "t_stat": "{:+.2f}".format,
    }
    print(f"\n{'='*90}\n{title}\n{'='*90}")
    print(df.to_string(index=False, formatters=fmt))


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

    print("\nProjecting every historical day with wpr.project_race() (the real live function)...")
    t0 = time.time()
    proj_col = pd.Series(index=runners.index, dtype=float)
    has_proj_col = pd.Series(False, index=runners.index)
    for di, d in enumerate(dates):
        day_df = runners[runners["date"].dt.date == d]
        result = project_date(day_df, pd.Timestamp(d), form_by_horse, trial_by_horse)
        for idx, r in result.items():
            has_proj_col.at[idx] = r["has_projection"]
            if r["has_projection"]:
                proj_col.at[idx] = r["projected_wpr"]
        if (di + 1) % 10 == 0 or di == len(dates) - 1:
            print(f"  ... {di+1}/{len(dates)} dates ({time.time()-t0:.0f}s elapsed)")

    runners["wprp_proj"] = proj_col
    runners["has_projection"] = has_proj_col
    print(f"\nTotal: {int(has_proj_col.sum()):,} / {len(runners):,} runners got a projection "
          f"in {time.time()-t0:.0f}s")

    bets_pool = runners[runners["has_projection"]].copy()
    sp = pd.to_numeric(bets_pool["fixed_win_price"], errors="coerce")
    sp_fallback = pd.to_numeric(bets_pool["starting_price_sp"], errors="coerce")
    bets_pool["price"] = sp.fillna(sp_fallback)
    bets_pool = bets_pool.dropna(subset=["price"])
    bets_pool = bets_pool[bets_pool["price"] > 1.0]
    bets_pool["won"] = pd.to_numeric(bets_pool["won"], errors="coerce").fillna(0).astype(int)
    bets_pool["proj"] = bets_pool["wprp_proj"]

    print(f"\nComputing per-race edge at beta={BETA}...")
    edges = bets_pool.groupby("race_id", group_keys=False).apply(edge_for_race)
    bets_pool["edge"] = edges
    bets_pool["quality"] = pd.cut(bets_pool["prize_money"], bins=QUALITY_BINS, labels=QUALITY_LABELS)

    bets = bets_pool[(bets_pool["edge"] >= EDGE_THRESHOLD) & (bets_pool["price"] <= PRICE_CAP)].copy()
    print(f"Qualifying bets (edge>={EDGE_THRESHOLD}, price<=${PRICE_CAP:.0f}): {len(bets):,}")
    bets[["date", "venue", "race", "horse", "state", "quality", "price", "edge", "won"]].to_csv(
        BETS_CSV_OUT, index=False)

    daily = bets.groupby(bets["date"].dt.date).apply(summarize, include_groups=False).reset_index()
    daily = daily.sort_values("date")
    daily.to_csv(DAILY_CSV_OUT, index=False)
    print_table(daily, f"DAILY SUMMARY (real model, beta={BETA})")

    monthly = bets.groupby(bets["date"].dt.to_period("M")).apply(summarize, include_groups=False).reset_index()
    monthly = monthly.rename(columns={"date": "month"})
    print_table(monthly, f"MONTHLY ROLLUP (real model, beta={BETA})")

    state_summary = bets.groupby("state", dropna=False).apply(summarize, include_groups=False).reset_index()
    state_summary = state_summary.sort_values("n_bets", ascending=False)
    state_summary.to_csv(STATE_CSV_OUT, index=False)
    print_table(state_summary, f"BREAKDOWN BY STATE (real model, beta={BETA})")

    quality_summary = bets.groupby("quality", observed=True).apply(summarize, include_groups=False).reset_index()
    quality_summary = quality_summary.set_index("quality").reindex(QUALITY_LABELS).reset_index()
    quality_summary.to_csv(QUALITY_CSV_OUT, index=False)
    print_table(quality_summary, f"BREAKDOWN BY RACE QUALITY (real model, beta={BETA})")

    state_quality = bets.groupby(["state", "quality"], observed=True).apply(
        summarize, include_groups=False).reset_index()
    state_order = state_summary["state"].tolist()
    state_quality["state"] = pd.Categorical(state_quality["state"], categories=state_order, ordered=True)
    state_quality["quality"] = pd.Categorical(state_quality["quality"], categories=QUALITY_LABELS, ordered=True)
    state_quality = state_quality.sort_values(["state", "quality"])
    state_quality.to_csv(STATE_QUALITY_CSV_OUT, index=False)
    print_table(state_quality, f"BREAKDOWN BY STATE x RACE QUALITY (real model, beta={BETA})")

    roi_pivot = state_quality.pivot(index="state", columns="quality", values="roi_pct")
    n_pivot = state_quality.pivot(index="state", columns="quality", values="n_bets")
    print(f"\n{'='*90}\nPIVOT: ROI% by state (rows) x quality (cols)\n{'='*90}")
    print(roi_pivot.to_string(float_format=lambda v: f"{v:+.1f}%" if pd.notna(v) else "-"))
    print(f"\n{'='*90}\nPIVOT: n bets by state (rows) x quality (cols)\n{'='*90}")
    print(n_pivot.to_string(float_format=lambda v: f"{v:.0f}" if pd.notna(v) else "-"))

    total_staked = bets.apply(lambda r: RETURN_UNITS / r["price"], axis=1).sum()
    total_profit = bets.apply(
        lambda r: (RETURN_UNITS - RETURN_UNITS / r["price"]) if r["won"] == 1 else -(RETURN_UNITS / r["price"]),
        axis=1).sum()
    print(f"\nOVERALL: n={len(bets):,}  staked={total_staked:.2f}u  profit={total_profit:+.2f}u  "
          f"ROI={total_profit/total_staked*100:+.1f}%")
    print(f"\nAll CSVs written under {SCRATCH_DIR}")


if __name__ == "__main__":
    run()
