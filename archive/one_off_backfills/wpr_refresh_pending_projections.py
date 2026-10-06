"""
wpr_refresh_pending_projections.py - recompute wprp_proj (and every derived
column) for PENDING (not-yet-resulted) races, using the CURRENTLY SHIPPED
model.

WHY THIS EXISTS (Sep 2026, user-caught bug)
  compute_wpr_projection()/compute_edge_score() in toprate_daily.py only
  ever process "today" - a pending race fetched on day X keeps whatever
  wprp_* values it got that day, forever, until it results. Every base-
  calc change this session (the tiered-regression revert, removing
  calibration, the beta change) shipped with a backfill of RESULTED rows
  only (wpr_backfill_historical_projections.py - resulted_mask==1), since
  that is all the Review tab's accuracy stats read. Nobody ever refreshed
  PENDING rows, so every upcoming race's displayed base/proj/price/edge
  silently kept running the OLD model until it actually raced - caught
  when a live runner detail panel (Matusalem, Wyong R6, today) showed
  base=94.4 when the current wpr_nett=95.4/ewm5=95.7 blend (no
  calibration) computes to 95.62 directly.

  Same underlying issue as the historical backfill, just the other half
  of the population - this script is that script's mirror, scoped to
  resulted_mask == 0 (or NaN) with a race_date >= today (no point
  refreshing pending rows for races so old they'll never be fetched
  again).

USAGE
  python wpr_refresh_pending_projections.py

Writes toprate_runners.csv in place. Does NOT rebuild toprate_data.json -
run toprate_daily.py's rebuild_html() (or --rebuild-only) separately after.

NO EM DASHES policy: hyphens only in this file.
"""
import json
import time

import pandas as pd

import wpr_projection as wpr
from toprate_daily import load_runners, save_runners, WPR_FORM_HISTORY_CSV


def run():
    print("Loading runners_df...")
    runners_df = load_runners()
    for col in ["wprp_proj", "wprp_conf", "wprp_price", "wprp_rank",
                "wprp_peak", "wprp_desc", "wprp_proj_alt", "wprp_conf_alt",
                "wprp_base", "wprp_adj", "wprp_contrib",
                "wprp_blend_prob", "wprp_blend_rank", "wprp_blend_price",
                "wprp_edge", "wprp_edge_prob", "wprp_edge_mkt_prob"]:
        if col not in runners_df.columns:
            runners_df[col] = None

    runners_df["date"] = pd.to_datetime(runners_df["date"], errors="coerce")
    resulted_mask = pd.to_numeric(runners_df.get("resulted"), errors="coerce") == 1
    today = pd.Timestamp.now().normalize()
    target = runners_df[~resulted_mask & (runners_df["date"] >= today)]
    print(f"Pending rows to refresh: {len(target):,} across "
          f"{target['race_id'].nunique():,} races (from {today.date()} onward)")

    print("Reading full form history (once)...")
    fh = pd.read_csv(WPR_FORM_HISTORY_CSV, dtype={"horse": str, "horse_id": str},
                     low_memory=False)
    fh["horse_lc"] = fh["horse"].astype(str).str.strip().str.lower()
    fh["date"] = pd.to_datetime(fh["date"], errors="coerce")
    fh["wpr"] = pd.to_numeric(fh["wpr"], errors="coerce")
    fh = fh.dropna(subset=["date", "wpr"])
    if "isBarrierTrial" in fh.columns:
        fh = fh[fh["isBarrierTrial"].fillna(0).astype(int) == 0]
    fh = fh.sort_values(["horse_lc", "date"])
    form_by_horse = dict(tuple(fh.groupby("horse_lc")))
    print(f"  {len(form_by_horse):,} horses with form history")

    race_groups = list(target.groupby("race_id"))
    n_races = len(race_groups)
    t0 = time.time()
    projected = fallback = races = edge_scored = 0

    for gi, (race_id, race) in enumerate(race_groups):
        if gi > 0 and gi % 50 == 0:
            elapsed = time.time() - t0
            eta = elapsed / gi * (n_races - gi)
            print(f"  ... {gi}/{n_races} races ({elapsed:.0f}s elapsed, "
                  f"~{eta:.0f}s remaining)")
        try:
            race_date = pd.to_datetime(race["date"].iloc[0], errors="coerce")
        except Exception:
            continue
        if pd.isna(race_date):
            continue

        active_field_size = int((race.get("scratched", pd.Series([0] * len(race), index=race.index))
                                  .fillna(0).astype(int) != 1).sum())

        runners, idx_order = [], []
        for idx, r in race.iterrows():
            horse_lc = str(r.get("horse", "")).strip().lower()
            hist = form_by_horse.get(horse_lc)
            prior = hist[hist["date"] < race_date] if hist is not None else None
            going = r.get("going") or "Good 4"
            runners.append({
                "prior_runs": prior,
                "cur_distance": r.get("distance") or 1400,
                "cur_going": going,
                "cur_track": r.get("venue") or "",
                "cur_track_grading": r.get("track_grading"),
                "cur_race_class": r.get("race_class"),
                "cur_field_size": active_field_size,
                "cur_wpr_nett": r.get("wpr_nett"),
                "cur_barrier": r.get("barrier"),
                "cur_gear_changes": r.get("gear_changes"),
                "cur_trainer_win_pct_365d": r.get("trainer_win_pct_365d"),
                "cur_jockey_win_pct_90d": r.get("jockey_win_pct_90d"),
            })
            idx_order.append(idx)

        try:
            results = wpr.project_race(runners, race_date=race_date)
        except Exception as e:
            print(f"  WPR projection error on race {race_id}: {e}")
            continue
        races += 1

        for idx, res in zip(idx_order, results):
            runners_df.at[idx, "wprp_peak"] = res.get("peak_wpr")
            runners_df.at[idx, "wprp_desc"] = res.get("description")
            if res.get("has_projection"):
                runners_df.at[idx, "wprp_proj"] = res.get("projected_wpr")
                runners_df.at[idx, "wprp_conf"] = res.get("confidence")
                runners_df.at[idx, "wprp_price"] = res.get("wpr_price")
                runners_df.at[idx, "wprp_rank"] = res.get("wpr_rank")
                runners_df.at[idx, "wprp_base"] = res.get("base_wpr")
                runners_df.at[idx, "wprp_adj"] = res.get("adjustment")
                contrib = res.get("adjustment_contributions")
                runners_df.at[idx, "wprp_contrib"] = (
                    json.dumps(contrib) if contrib is not None else None)
                projected += 1
            else:
                fallback += 1

        # Edge score - pre-race, so market_price is fixed_win_price (live
        # odds), falling back to starting_price_sp/price_top only in the
        # rare case those got backfilled onto a still-pending row.
        market_price = (race.get("fixed_win_price")
                        .combine_first(race.get("starting_price_sp"))
                        .combine_first(race.get("price_top")))
        edge_runners = []
        for idx in idx_order:
            edge_runners.append({
                "wprp_proj": runners_df.at[idx, "wprp_proj"],
                "market_price": market_price.get(idx),
            })
        try:
            edge_results = wpr.compute_edge_scores(edge_runners)
        except Exception as e:
            print(f"  Edge score error on race {race_id}: {e}")
            continue
        for idx, res in zip(idx_order, edge_results):
            if res.get("blend_prob") is not None:
                runners_df.at[idx, "wprp_blend_prob"] = res.get("blend_prob")
                runners_df.at[idx, "wprp_blend_rank"] = res.get("blend_rank")
                runners_df.at[idx, "wprp_blend_price"] = res.get("blend_price")
                edge_scored += 1
            if res.get("has_edge"):
                runners_df.at[idx, "wprp_edge"] = res.get("edge")
                runners_df.at[idx, "wprp_edge_prob"] = res.get("model_prob")
                runners_df.at[idx, "wprp_edge_mkt_prob"] = res.get("market_prob")

    elapsed = time.time() - t0
    print(f"\nDone in {elapsed:.0f}s: {projected:,} projected, {fallback:,} fallback "
          f"(too few runs), {edge_scored:,} edge-scored, across {races:,} races")

    save_runners(runners_df)
    print("Saved toprate_runners.csv")


if __name__ == "__main__":
    run()
