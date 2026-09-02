"""
wpr_live_window_current_model_check.py - isolates whether wpr_live_data_
beta03_breakdown.py's stark result (-18.1% ROI over Aug 3 - Sep 1, vs
strongly positive over the ~5-month reconstruction-based backtest) is a
stale-model-vintage artifact or genuine live underperformance.

compute_wpr_projection() only computes a day's wprp_proj ONCE, the first
time that date is processed as "today" - so toprate_data.json's stored
wpjp for most of Aug 3 - Sep 1 likely predates several of this session's
model changes (alpha 0.8, dist_edge_correction, first_up_trial_
correction, MIN_RUNS=1), which all shipped today. This recomputes the
SAME 30-day window with wpr.project_race() run under TODAY's code
(reusing compute_wpr_projection()'s own per-race construction verbatim,
just restructured to read wpr_form_history.csv.gz once instead of once
per date), so the two runs are directly comparable: same days, same
races, same beta, only the model vintage differs.

NO EM DASHES policy: hyphens only in this file.
"""
import time

import numpy as np
import pandas as pd

import wpr_projection as wpr
from wpr_live_data_beta03_breakdown import summarize, print_table, QUALITY_BINS, QUALITY_LABELS

RUNNERS_CSV = "toprate_runners.csv"
FORM_CSV = "wpr_form_history.csv.gz"
BETA = 0.30
EDGE_THRESHOLD = 0.05
PRICE_CAP = 26.0
WINDOW_START = "2026-08-03"
WINDOW_END = "2026-09-01"


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


def run():
    runners = pd.read_csv(RUNNERS_CSV, low_memory=False,
                           dtype={"race_id": str, "horse": str, "venue": str, "state": str})
    runners["date"] = pd.to_datetime(runners["date"], errors="coerce")
    runners["resulted"] = pd.to_numeric(runners["resulted"], errors="coerce")
    runners = runners[(runners["resulted"] == 1) &
                       (runners["date"] >= WINDOW_START) & (runners["date"] <= WINDOW_END)].copy()
    runners = runners.dropna(subset=["date", "race_id"])
    dates = sorted(runners["date"].dt.date.unique())
    print(f"Resulted rows in window: {len(runners):,} across {len(dates)} dates "
          f"({dates[0]} to {dates[-1]})")

    form_by_horse, trial_by_horse = load_form_history()

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
        print(f"  ... {di+1}/{len(dates)} dates ({time.time()-t0:.0f}s)")

    runners["wprp_proj"] = proj_col
    runners["has_projection"] = has_proj_col
    print(f"\n{int(has_proj_col.sum()):,} / {len(runners):,} runners projected in {time.time()-t0:.0f}s "
          f"(TODAY's current model code)")

    bets_pool = runners[runners["has_projection"]].copy()
    sp = pd.to_numeric(bets_pool["fixed_win_price"], errors="coerce")
    sp_fallback = pd.to_numeric(bets_pool["starting_price_sp"], errors="coerce")
    bets_pool["price"] = sp.fillna(sp_fallback)
    bets_pool = bets_pool.dropna(subset=["price"])
    bets_pool = bets_pool[bets_pool["price"] > 1.0]
    bets_pool["won"] = pd.to_numeric(bets_pool["won"], errors="coerce").fillna(0).astype(int)
    bets_pool["proj"] = bets_pool["wprp_proj"]

    edges = bets_pool.groupby("race_id", group_keys=False).apply(edge_for_race)
    bets_pool["edge"] = edges

    bets = bets_pool[(bets_pool["edge"] >= EDGE_THRESHOLD) & (bets_pool["price"] <= PRICE_CAP)].copy()
    print(f"Qualifying bets under CURRENT model, same window: {len(bets):,}")

    daily = bets.groupby(bets["date"].dt.date).apply(summarize, include_groups=False).reset_index()
    daily = daily.sort_values("date")
    print_table(daily, f"DAILY SUMMARY, CURRENT MODEL RECOMPUTE (Aug 3 - Sep 1, beta={BETA})")

    total_staked = sum(4 / p for p in bets["price"])
    total_profit = sum((4 - 4/p) if w == 1 else -(4/p) for p, w in zip(bets["price"], bets["won"]))
    print(f"\nOVERALL (current model, same window): n={len(bets):,}  staked={total_staked:.2f}u  "
          f"profit={total_profit:+.2f}u  ROI={total_profit/total_staked*100:+.1f}%")


if __name__ == "__main__":
    run()
