"""
toprate_daily.py
----------------
Single daily script — run once each morning (or evening after racing).

What it does:
  1. Logs in to TopRate API
  2. Fetches results for any unresulted runners from previous days
  3. Fetches today's races — stores ALL runners with signal data
  4. Computes per-race signal votes, builds selections summary
  5. Rebuilds the interactive live HTML

Files maintained:
  toprate_runners.csv    — full database, one row per runner per race
  toprate_selections.csv — one row per race (top selection + vote count), used by HTML
  toprate_data.json      — dashboard data payload, refreshed each run
  toprate_live.html      — the dashboard itself (frontend/ React+Vite build).
                            NOT rebuilt by this script - it's a static
                            artifact, rebuilt deliberately via
                            `npm run build` in frontend/ and committed.

Usage:
    python toprate_daily.py                  # standard daily run
    python toprate_daily.py --date 2026-04-24  # specific date (re-fetches pending)
    python toprate_daily.py --no-html        # skip HTML rebuild
    python toprate_daily.py --backfill 7     # update results for last N days

Requirements:
    pip install requests pandas openpyxl
"""

import requests
import pandas as pd
import tr_form_store
import meeting_transfer
import atw_offsets as _atw_offsets_mod
import runners_io
import numpy as np
import argparse
import sys
import time
import math
import json
import gzip
import os
import re
import warnings
import urllib3
from datetime import datetime, timedelta, date, timezone
from pathlib import Path
from collections import defaultdict, Counter
from statistics import mean, stdev


# -----------------------------------------------------------------------
# CONFIG
# -----------------------------------------------------------------------
RUNNERS_CSV    = runners_io.LIVE_CSV     # runners.csv; toprate_runners.csv is retired (runners_io falls back to it until runners.csv exists)
SELECTIONS_CSV = Path(__file__).parent / "toprate_selections.csv"
PRICE_HISTORY_CSV = Path(__file__).parent / "toprate_price_history.csv"
OUTPUT_HTML    = Path(__file__).parent / "toprate_live.html"
BT_RUNNERS_CSV = Path(__file__).parent / "toprate_runners_backtest.csv"
# Per-meeting full horse-history files (see build_horse_history_files()) -
# the static replacement for the dropped Supabase live-fetch that used to
# back the runner detail panel's "Recent runs" table beyond its embedded
# last-10-runs cap. One small JSON per (date, venue) meeting rather than
# one per horse (thousands of tiny files) or one combined blob (the same
# 100MB-limit mistake toprate_data.json itself already made once).
HORSE_HISTORY_DIR = Path(__file__).parent / "horse_history"

# WPR form-history dump. Each daily scrape's get_race_wpr_chart response
# carries, per runner, a `form` array of all that horse's past runs (wpr,
# distance, going, weight, sectional margins, settling positions, etc).
# build_wpr_history_lookup() consumes that array to compute summary signals
# but the raw per-run rows were previously discarded. We now persist them
# here, one row per (horse run), so a forward WPR-projection model can be
# trained later. This file is APPEND-ONLY and deduplicated on a stable key.
# It is not read by the daily pipeline or the dashboard - purely a data
# capture sink for offline modelling.
# Stored gzipped. gzip keeps the committed file well under GitHub's 100MB hard
# limit (the raw CSV crossed it): ~88MB CSV compresses to ~25MB, so it can be
# committed to git and persist across the Action's ephemeral runs (the append
# in flush_wpr_form_history needs the prior file present to accumulate).
# pandas reads/writes .gz transparently from the extension, so no other code
# change is needed - every read_csv/to_csv below inherits compression.
WPR_FORM_HISTORY_CSV = Path(__file__).parent / "wpr_form_history.csv.gz"

# Punting Form integration removed (WPR-only refactor). The PF subscription
# is cancelled; the model now runs on WPR projection only.

# 14 signals matching the backtest
SIGNALS_HIGHER = ["wpr_nett","wpr_last1","wpr_avg_last3","wpr_dist","wpr_going",
                  "jockey_win_pct_90d","trainer_win_pct_365d","toprate_rating","speed_rating",
                  "wpr_trend"]
SIGNALS_LOWER  = ["wpr_peak_rank_1yr","wpr_consistency"]
ALL_SIGNALS    = SIGNALS_HIGHER + SIGNALS_LOWER

# Runner DB columns
RUNNER_COLS = [
    # Race info
    "date","venue","state","race","race_id","race_name","distance","prize_money",
    "going","track_grading","rail_position","start_time","race_class",
    "race_shape_early","race_shape_mid","race_shape_late",
    "has_first_starter",
    # Runner info
    "run_id","horse_id","tab_number","barrier","horse","jockey","trainer","runs_with_wpr",
    # This runner's gear changes for TODAY's race (JSON list string, same
    # format as wpr_form_history.csv.gz's own per-run gear_changes column -
    # see apply_gear_changes_today), None if none announced/unavailable.
    "gear_changes",
    # Signal values (raw)
    "wpr_nett","wpr_rank","wpr_last1","wpr_avg_last3","wpr_trend","wpr_consistency",
    "wpr_peak_rank_1yr","wpr_dist","wpr_going",
    "avg_settled_pos","avg_800m_pos","avg_400m_pos","early_speed_score",
    "mid_speed_score","late_speed_score","total_speed_score",
    "toprate_rating","toprate_price","speed_rating",
    # Form Factor Rank/Score - TopRate's new (23 Jun 2026 upgrade) model,
    # explicitly computed WITHOUT betting market information as an input
    # (per their announcement), so it is a genuinely independent pre-race
    # signal rather than another market-derived number. Confirmed present
    # in get_race_detail as pfmScore/pfmScoreRank (probed 21 Aug 2026);
    # not yet used by anything - captured here to start accumulating
    # history before testing it as a WPR feature.
    "pfm_score","pfm_score_rank",
    "fixed_win_price","open_price","jockey_win_pct_90d","trainer_win_pct_365d",
    # TopRate's own jockey and trainer rating numbers (separate from win % strike rates)
    "jockey_rating","trainer_rating",
    # Jockey/trainer combo win%. DO NOT use as a predictive signal or wire into
    # SCORE_WEIGHTS/the edge score - confirmed data leak (Aug 2026 backtest):
    # on jt_combo_rides==1 rows, winPercent is ~100 when the horse won and ~0
    # when it lost, i.e. the provider's combo stat reflects TODAY's own result,
    # not a pre-race trailing window. A naive backtest on this field shows an
    # impossible +60-140% ROI purely because of this leak. Kept only for
    # display/reference; never feed it into a model or ranking.
    "jt_combo_win_pct","jt_combo_rides",
    # potPercent (profit-on-turnover) / lt3LengthsPercent (beaten <3 lengths)
    # from the SAME filtered stat-domain dicts as jockey_win_pct_90d/
    # trainer_win_pct_365d above - same trailing pre-race window, same
    # get_race_stats RPC, no leak risk (Sep 2026 addition, see chat).
    "jockey_pot_pct_90d","trainer_pot_pct_365d",
    "jockey_lt3l_pct_90d","trainer_lt3l_pct_365d",
    # Ride/runner counts behind jockey_win_pct_90d/trainer_win_pct_365d -
    # see build_stats_lookup's own comment for why (a thin count makes
    # winPercent unreliable, same failure mode as jt_combo_win_pct's
    # documented leak, just less extreme). The API DOES expose this
    # (confirmed 2026-09-17 via toprate_field_discovery.py against a live
    # runner page: rd.jockeyStats[0].rides) - it was 100% null in this CSV
    # column despite that not because of any API gap, but because the
    # race_runners row-build step below never actually read it out of the
    # stats_lu lookup dict (fixed 2026-09-17, see that fix's own comment).
    "jockey_starts_90d","trainer_starts_365d",
    # jt_combo_pot_pct/jt_combo_lt3l_pct come from the SAME array entry as
    # jt_combo_win_pct above, so they inherit its documented leak (on
    # jt_combo_rides==1 rows this reflects TODAY's own result, not a
    # pre-race trailing window). Same rule as jt_combo_win_pct: display/
    # reference only, never a model input.
    "jt_combo_pot_pct","jt_combo_lt3l_pct",
    # "Today stats" - horse-level CURRENT-state aggregates from the rich
    # __data.json runner page (rd["stats"]/rd["ratingProfiles"]), TODAY's
    # runners only, filled by apply_today_stats(). Keep this list in sync
    # with toprate_json_capture.TODAY_STATS_COLS (see that module's
    # _STATS_BLOCKS comment for what each one is and why the rest of
    # rd["stats"] was deliberately left out).
    "stats_first_up_starts","stats_first_up_wins","stats_first_up_places",
    "stats_second_up_starts","stats_second_up_wins","stats_second_up_places",
    "stats_track_starts","stats_track_wins","stats_track_places",
    "stats_sire_dry_starts","stats_sire_dry_wins","stats_sire_dry_places",
    "stats_sire_wet_starts","stats_sire_wet_wins","stats_sire_wet_places",
    "stats_current_jockey_starts","stats_current_jockey_wins","stats_current_jockey_places",
    "rating_career_best_wpr","rating_career_best_rank",
    "rating_career_next_wpr","rating_career_next_rank",
    "weight_handicap_today",   # today's handicap weight (runner page); fills weight_carried blanks
    # New signals supporting v3 core models (weight trajectory, distance specialty)
    "weight_trend","wins_at_dist","starts_at_dist","places_at_dist",
    "going_breakdown","form_string",
    # Per-runner weight carried today (was being collected but never saved)
    "weight_carried",
    # Pre-race market (starting_price_sp and price_top filled post-race)
    "starting_price_sp","price_top",
    # Result fields
    "finish_position","margin_finish","won","placed","resulted",
    # Set by tab_results_poller.py the moment TAB reports a race Paying/
    # Abandoned - lets the dashboard show a race as resulted right away
    # (see the "done" flag near the RACES payload build) without touching
    # `resulted` itself, which stays exclusively update_results()'s job
    # (the authoritative wpr_actual/comments_* pass, days later, confirms
    # or corrects it). Never read by anything price/accuracy-related.
    "interim_resulted",
    # Late scratch, set by toprate_price_refresh.py after first capture (the
    # isScratched check above only ever runs once, at capture time)
    "scratched",
    # Settled post-race values. wpr_actual = final weight-adjusted WPR; the two
    # comment fields are the video + stewards notes. All three land in the days
    # AFTER a race (filled by update_results re-fetch + fill_comments_from_history),
    # so they may be blank on race day and populate later. Declared here as
    # first-class columns (rather than relying on the extras catch-all) so they
    # are always present in a stable position in the CSV for offline analysis.
    "wpr_actual","comments_video","comments_steward",
]





# -----------------------------------------------------------------------
# PARALLEL FETCH
# -----------------------------------------------------------------------
# Each race needs 4 independent API calls (detail, cache, wpr, stats).
# These are network-bound and independent across races, so we pre-fetch
# them concurrently with a thread pool. The MAIN loop then processes the
# pre-fetched responses sequentially - so all row-building, accumulator
# writes, and ordering stay single-threaded and unchanged. Only the
# blocking HTTP waits are parallelised, which is where the time goes.
#
# A 30-day backfill is ~8,000 sequential requests (~1 hour). With 8
# workers the network waits overlap and it drops to roughly 10 minutes.
#
# Worker count is configurable via --workers (default 8). Set --workers 1
# to fall back to fully sequential behaviour if the API ever rate-limits.
DEFAULT_FETCH_WORKERS = 8




# -----------------------------------------------------------------------
# DATA BUILDERS
# -----------------------------------------------------------------------
def safe(v, default=None):
    try:
        f = float(v)
        return default if math.isnan(f) else f
    except: return default


# ── WPR form-history capture ──────────────────────────────────────────────
# Module-level accumulator. collect_wpr_form_history() appends raw per-run
# form rows here during the scrape; flush_wpr_form_history() writes them out
# once at the end of the run. Kept module-level (not threaded through call
# args) so the capture is a minimal, isolated addition to the scrape path.
_WPR_FORM_ROWS = []
# One-time flag so the wpr_chart-runner-keys diagnostic prints only once.
_WPR_KEYS_LOGGED = False
# Run-page ids of today's runners, accumulated during collect_wpr_form_history.
# Consumed once by the rich __data.json capture pass in flush_wpr_form_history.
_WPR_RICH_RUNIDS = set()
# run_id -> horse name, so the rich capture pass can name brand-new rows it
# creates for runs the thin feed never surfaced (it only has horse_id from
# the rich fetch itself, not the name).
_WPR_NAME_BY_RID = {}
# run_id (str) -> gear_changes JSON list string for TODAY's/this run's own
# upcoming race (Aug 2026 addition - see gear_change ADJ_TERM). Populated
# as a side effect of the SAME rich __data.json fetch that already runs
# for today's runners (_enrich_form_history_rich) - the field lives at the
# top level of the runner page object (rd["gearChanges"]), sibling to
# "form", not inside it, so it costs no extra network call. Consumed once
# by apply_gear_changes_today() to add a "gear_changes" column onto
# runners_df before it is saved to toprate_runners.csv.
_GEAR_CHANGES_TODAY = {}

# run_id (str) -> flat dict of horse-level CURRENT-state aggregates
# (Sep 2026 addition - see cap._extract_today_stats/cap._STATS_BLOCKS).
# Populated as the SAME side effect of the SAME rich __data.json fetch
# as _GEAR_CHANGES_TODAY above - same reasoning applies: these fields
# (own FU/2U record, track affinity, sire dry/wet split, this exact
# jockey pairing's record, career-best rating) are TopRate's own "as of
# now" aggregates, safe for TODAY's race but NEVER to be attached to
# historical wpr_form_history.csv.gz rows (that would leak future stats
# into past rows). Consumed once by apply_today_stats() to add columns
# onto runners_df before it is saved to toprate_runners.csv - mirrors
# apply_gear_changes_today() exactly, for the same reason.
_TODAY_STATS_BY_RID = {}

# Fields pulled from each form entry. These are the raw inputs a WPR
# projection model trains on (target = the `wpr` of the run itself).
# Confirmed against the live API via the structural diagnostic - the form
# entry carries 29 fields; we capture all the modelling-relevant ones.
# Anything the API doesn't provide for a given run comes through as None.
_WPR_FORM_FIELDS = [
    "formNumber", "raceNumber", "date",
    "track", "trackCode", "trackGrading",     # track identity + class proxy
    "distance", "going",
    "wpr",                                    # actual post-race WPR (target)
    "weightCarried",
    "barrier",                                # draw on the day
    "priceStarting",                          # SP that day (market signal)
    # full settle-to-finish position curve
    "positionSettled", "position800m", "position600m",
    "position400m", "position200m", "positionFinish",
    # sectional margins
    "margin800m", "margin600m", "margin400m", "margin200m", "marginFinish",
    # how the race was run
    "raceShapeEarly", "raceShapeMid", "raceShapeLate",
    "winner", "isBarrierTrial",
]














# ===========================================================================
# WPR PROJECTION  (Step 2c)
# ---------------------------------------------------------------------------
# Enriches the runners DataFrame with the model-only WPR projection: a
# projected run-day WPR, a 0-100 confidence rating, a fair-value WPR price,
# the in-race WPR rank, the horse's career peak WPR, and a one-line plain
# text explanation.
#
# Runs AFTER flush_wpr_form_history() (Step 2a) so wpr_form_history.csv on
# disk already contains every runner's full form history including the runs
# scraped today. For each race, each runner's PRIOR form (runs strictly
# before today) is pulled from that file and passed to wpr_projection.
#
# All projection logic lives in wpr_projection.py - this function only wires
# the runners DataFrame to it. The wpr_* columns are not in RUNNER_COLS;
# save_runners() persists them automatically as "extras".
# ===========================================================================

def compute_race_speed(runners_df, target_date_str=None):
    """Add rs_score and rs_label columns to the runners DataFrame - an
    AUTOMATED race-speed (early-tempo) estimate for every race today.

    Runs with no manual input. For each race it calls
    race_speed_estimate.estimate_race_speed, which aggregates the field's
    settling estimates into a 0-1 pressure score and a Hot/Fast/Even/Slow
    label.

    HONEST LABELLING - read before relying on this. The race-speed
    estimate is LOW CONFIDENCE. Validation found the tempo component has
    little correlation with how races are actually run early (race tempo
    is set on the day by jockey tactics and gate speed, which are not in
    pre-race data). rs_score / rs_label are therefore an ESTIMATE, not a
    verified prediction. They are surfaced for context only. Any use that
    feeds the WPR projection must be a SMALL, gentle adjustment
    proportionate to this modest reliability - never a large swing.

    Additive and fail-safe: returns the DataFrame unchanged on any
    failure - the estimate must never break the daily pipeline.
    """
    try:
        import race_speed_estimate as rse
    except Exception as e:
        print(f"  Race-speed estimate skipped: cannot import "
              f"race_speed_estimate ({e})")
        return runners_df

    for col in ["rs_score", "rs_label"]:
        if col not in runners_df.columns:
            runners_df[col] = None

    if target_date_str is None:
        target_date_str = date.today().strftime("%Y-%m-%d")
    day_mask = runners_df["date"].astype(str).str[:10] == target_date_str
    today = runners_df[day_mask]
    if len(today) == 0:
        print(f"  Race-speed estimate: no runners for {target_date_str}")
        return runners_df

    # form history for the settling estimates
    if not WPR_FORM_HISTORY_CSV.exists():
        print(f"  Race-speed estimate skipped: {WPR_FORM_HISTORY_CSV.name} "
              f"not found")
        return runners_df
    try:
        fh = pd.read_csv(WPR_FORM_HISTORY_CSV,
                         dtype={"horse": str, "horse_id": str},
                         low_memory=False)
        fh["horse_lc"] = fh["horse"].astype(str).str.strip().str.lower()
        fh["date"] = pd.to_datetime(fh["date"], errors="coerce")
        fh = fh.dropna(subset=["date"])
        if "isBarrierTrial" in fh.columns:
            fh = fh[fh["isBarrierTrial"].fillna(0).astype(int) == 0]
    except Exception as e:
        print(f"  Race-speed estimate skipped: could not read form "
              f"history ({e})")
        return runners_df

    # _prior_means() is the expensive part (a full-history groupby-mean
    # across 8 columns) and its result depends only on the date cutoff,
    # not which race - every race today shares the exact same "before
    # today" cutoff (the date column has no time component), so it was
    # being recomputed from scratch once per race for an identical
    # result every time. Compute it ONCE here instead. Fail-safe: if
    # this fails for any reason, leave _shared_pmeans None and each race
    # falls back to computing its own (slow but correct), same as before.
    _shared_pmeans = None
    try:
        _day_cutoff = pd.to_datetime(target_date_str)
        _shared_pmeans = rse._prior_means(fh, _day_cutoff)
    except Exception as e:
        print(f"  Race-speed: shared prior-means precompute skipped ({e})")

    done = 0
    for race_id, race in today.groupby("race_id"):
        try:
            race_date = pd.to_datetime(race["date"].iloc[0], errors="coerce")
            res = rse.estimate_race_speed(race, race_date, fh, pmeans=_shared_pmeans)
            score = res.get("score")
            label = res.get("label")
            idx = runners_df["race_id"].astype(str) == str(race_id)
            runners_df.loc[idx, "rs_score"] = (
                round(score, 3) if score is not None else None)
            runners_df.loc[idx, "rs_label"] = label
            done += 1
        except Exception as e:
            print(f"  Race-speed estimate error on race {race_id}: {e}")
            continue
    print(f"  Race-speed estimate: {done} races estimated "
          f"(low-confidence - context only)")
    return runners_df




def apply_new_projection(runners_df, recompute_edges=True):
    """Fill every wprp_* projection column from the new model's projection log (projection/overlay.py) and clear it everywhere
    else, so no projection from the previous model reaches the payload, the trackers or the accuracy stats. Then (optionally)
    recompute the edge columns from the new projections for every date in the recent window. Fail-safe: returns runners_df
    unchanged on any error."""
    try:
        from projection import overlay
        runners_df = overlay.apply(runners_df)
        n = int(pd.to_numeric(runners_df["wprp_proj"], errors="coerce").notna().sum())
        print(f"  New-model projections applied: {n:,} runners carry one")
    except Exception as e:
        print(f"  New-model projection overlay skipped ({e})")
    return runners_df


def compute_wpr_projection(runners_df, target_date_str=None, target_venues=None):
    """Step 2c. The WPR projections come from the new model (projection/run.py: daily, plus a fast refresh after a going change),
    logged to wpr_projection_log.csv.gz, and are applied here. The previous model (_compute_wpr_projection_previous_model) was RETIRED on
    8 Oct 2026: it only supplied wprp_contrib.speed_map, and the SM Adj column and Speed Map tint now read the new model's suitability
    adjustment instead. The function is kept for reference but no longer called. target_date_str/target_venues are accepted for call-site
    compatibility and unused."""
    return apply_new_projection(runners_df, recompute_edges=False)






def fill_comments_from_history(runners_df):
    """Self-healing comment fill for resulted runners.

    Comments (and the final WPR rating) arrive up to a few days AFTER a race.
    update_results() only captures them at finish-day, and only for races where
    resulted != 1, so a race locked as resulted on finish-day never picks up
    the comments that land later. This pass mirrors compute_wpr_actual's
    pattern: every daily run, it joins comments from the form history (which
    the rich capture keeps refreshing) onto ALL resulted runners that are still
    missing them. So comments fill in progressively over the days post-race
    with no manual backfill.

    Only FILLS empty cells; never overwrites an existing comment. Keyed on
    (horse_lc, date) - the same key compute_wpr_actual uses.
    """
    for col in ["comments_video", "comments_steward"]:
        if col not in runners_df.columns:
            runners_df[col] = pd.NA

    resulted_mask = runners_df.get("resulted") == 1
    if resulted_mask.sum() == 0:
        return runners_df

    try:
        fh = pd.read_csv(WPR_FORM_HISTORY_CSV,
                         dtype={"horse": str}, low_memory=False)
        if "comments_video" not in fh.columns and "comments_steward" not in fh.columns:
            print("  Comments: form history has no comment columns, skipping")
            return runners_df
        fh["horse_lc"] = fh["horse"].astype(str).str.strip().str.lower()
        fh["date_s"] = fh["date"].astype(str).str[:10]
        # latest scrape wins (comments are revised/added post-race)
        if "scrape_date" in fh.columns:
            fh = fh.sort_values("scrape_date")
        fh = fh.drop_duplicates(subset=["horse_lc", "date_s"], keep="last")

        def _clean(v):
            if v is None or pd.isna(v):
                return None
            s = str(v).strip()
            return s if s and s.lower() not in ("nan", "none", "<na>") else None

        vmap, smap = {}, {}
        for _, r in fh.iterrows():
            k = (r["horse_lc"], r["date_s"])
            cv = _clean(r.get("comments_video"))
            cs = _clean(r.get("comments_steward"))
            if cv is not None:
                vmap[k] = cv
            if cs is not None:
                smap[k] = cs
    except Exception as e:
        print(f"  Comments fill skipped: could not read form history ({e})")
        return runners_df

    def _empty(val):
        if val is None or pd.isna(val):
            return True
        s = str(val).strip().lower()
        return s in ("", "nan", "none", "<na>")

    nv = ns = 0
    for idx in runners_df[resulted_mask].index:
        hlc = str(runners_df.at[idx, "horse"]).strip().lower()
        d = str(runners_df.at[idx, "date"])[:10]
        if _empty(runners_df.at[idx, "comments_video"]):
            v = vmap.get((hlc, d))
            if v is not None:
                runners_df.at[idx, "comments_video"] = v
                nv += 1
        if _empty(runners_df.at[idx, "comments_steward"]):
            s = smap.get((hlc, d))
            if s is not None:
                runners_df.at[idx, "comments_steward"] = s
                ns += 1

    print(f"  Comments: filled {nv} video, {ns} steward on resulted runners "
          f"(fills in over the days after a race as comments land)")
    return runners_df


def compute_miss_explanations(runners_df):
    """Explain MATERIAL misses (|actual WPR - projected WPR| >= 4) on
    resulted runners, once both wpr_actual and comments are available.

    Uses wpr_miss.explain_miss() - see that module for the full logic
    (ran-above-its-own-ceiling check first for understatement, then
    comment-based reasoning via wpr_void's classifier, then an untried-trip
    check, then a big pre-race price move, then "no clear explanation" for
    the user to note manually). Re-run every day like
    compute_wpr_actual/fill_comments_from_history above, since its inputs
    (wpr_actual, comments) fill in progressively over the ~5 days after a
    race - a miss unexplained today may become explainable once the real
    comments land.

    Additive and fail-safe: any error leaves the columns as-is.
    """
    for col in ["wprp_miss_category", "wprp_miss_reason"]:
        if col not in runners_df.columns:
            runners_df[col] = None

    resulted_mask = runners_df.get("resulted") == 1
    if resulted_mask.sum() == 0:
        return runners_df

    try:
        from wpr_miss import explain_miss
    except ImportError:
        print("  Miss explanations skipped: wpr_miss not found")
        return runners_df

    n_material = n_explained = 0
    for idx in runners_df[resulted_mask].index:
        proj = pd.to_numeric(runners_df.at[idx, "wprp_proj"], errors="coerce") \
            if "wprp_proj" in runners_df.columns else None
        actual = pd.to_numeric(runners_df.at[idx, "wpr_actual"], errors="coerce") \
            if "wpr_actual" in runners_df.columns else None
        if pd.isna(proj) or pd.isna(actual):
            continue
        close_price = runners_df.at[idx, "starting_price_sp"] \
            if "starting_price_sp" in runners_df.columns else None
        if pd.isna(close_price):
            close_price = runners_df.at[idx, "price_top"] \
                if "price_top" in runners_df.columns else None
        category, reason = explain_miss(
            actual=actual,
            proj=proj,
            comment_video=runners_df.at[idx, "comments_video"]
                if "comments_video" in runners_df.columns else None,
            comment_steward=runners_df.at[idx, "comments_steward"]
                if "comments_steward" in runners_df.columns else None,
            starts_at_dist=runners_df.at[idx, "starts_at_dist"]
                if "starts_at_dist" in runners_df.columns else None,
            open_price=runners_df.at[idx, "open_price"]
                if "open_price" in runners_df.columns else None,
            close_price=close_price,
            peak_wpr=runners_df.at[idx, "wprp_peak"]
                if "wprp_peak" in runners_df.columns else None,
            avg_last3=runners_df.at[idx, "wpr_avg_last3"]
                if "wpr_avg_last3" in runners_df.columns else None,
        )
        if category is not None:
            n_material += 1
            runners_df.at[idx, "wprp_miss_category"] = category
            runners_df.at[idx, "wprp_miss_reason"] = reason
            if category != "unexplained":
                n_explained += 1

    print(f"  Miss explanations: {n_material} material misses (|miss|>=4), "
          f"{n_explained} explained by comments/untried-trip/price, "
          f"{n_material - n_explained} unexplained (flagged for manual review)")
    return runners_df
# -----------------------------------------------------------------------
# PF ingest and the Edge/Volume model rule were removed (WPR-only refactor
# Stage A). merge_pf_ratings, compute_model_picks, save_model_picks,
# remove_excluded_picks_for_evaluated_races, model_picks_summary and the
# EDGE/VOLUME rule config all deleted. Cumulative score (below) retained.
# -----------------------------------------------------------------------



# -----------------------------------------------------------------------
# Cumulative predictive score removed (WPR-only refactor Stage 2). The WPR
# projection now ranks runners; a separate composite score is redundant.
# compute_cumulative_score, _resolve_score_weights, _shrink_jt_combo and
# the SCORE_WEIGHTS / JT_COMBO / PF_RANK_SIGNALS constants all deleted.
# -----------------------------------------------------------------------




# -----------------------------------------------------------------------
# LOAD / SAVE
# -----------------------------------------------------------------------
# Prize money threshold for TAB filter. Races with prize_money below this
# are bush/country meetings that the user can't bet on at TAB and so are
# excluded from all outputs (HTML, picks, watchlist).
TAB_PRIZE_MIN = 20000

def load_runners():
    # Live file + gzipped archive of older races (runners_io.py: split Oct 2026 to stay under GitHub's 100MB limit)
    if runners_io.exists():
        df = runners_io.read_runners(RUNNERS_CSV, dtype={"run_id": str, "race_id": str})
        for col in RUNNER_COLS:
            if col not in df.columns:
                df[col] = None
        # Deduplicate by run_id on load — keeps last row (most recent data)
        before = len(df)
        df = df.drop_duplicates(subset=["run_id"], keep="last").reset_index(drop=True)
        if len(df) < before:
            print(f"  Removed {before - len(df)} duplicate runner rows from CSV")
        # Note: previous TAB_PRIZE_MIN filter removed here. Bush/picnic
        # races (< $20k prize) used to be hidden from ALL downstream work,
        # but user wants them visible in the Race tab for browsing while
        # keeping picks suppressed. The pick gate lives in
        # compute_model_picks (skip races below TAB_PRIZE_MIN there), so
        # this load-time filter is redundant and was removing data the
        # user wanted visible. TAB_PRIZE_MIN constant kept for pick gate.
        return df
    return pd.DataFrame(columns=RUNNER_COLS)

def save_runners(df):
    # Guarantee the late-settling result columns always exist, so the CSV
    # schema is stable for offline analysis even on a run where none got
    # filled this time (they stay blank until the values land).
    for col in ["wpr_actual", "comments_video", "comments_steward"]:
        if col not in df.columns:
            df[col] = pd.NA
    cols = [c for c in RUNNER_COLS if c in df.columns]
    extras = [c for c in df.columns if c not in RUNNER_COLS]
    # Always save deduplicated
    df = df.drop_duplicates(subset=["run_id"], keep="last")
    # Races older than runners_io.LIVE_DAYS go to toprate_runners_archive.csv.gz; the live CSV keeps the rest
    runners_io.save_split(df[cols + extras], RUNNERS_CSV)

def snapshot_prices(runners_df):
    """
    Append a price snapshot for all pending (unresulted) runners to PRICE_HISTORY_CSV.
    Each row: run_id, race_id, snapshot_time (UTC ISO), fixed_win_price.
    Keeps only last 7 days of history to bound file size.
    """
    if runners_df is None or runners_df.empty:
        return
    # Only snapshot pending runners with a fixed price
    pending = runners_df[
        (runners_df.get("resulted") != 1) &
        (runners_df.get("fixed_win_price").notna()) &
        (runners_df.get("fixed_win_price") > 1)
    ].copy()
    if pending.empty:
        print("  No pending runners with fixed prices to snapshot")
        return
    
    snapshot_time = datetime.now(timezone.utc).isoformat()
    snap = pd.DataFrame({
        "run_id": pending["run_id"].astype(str),
        "race_id": pending["race_id"].astype(str),
        "snapshot_time": snapshot_time,
        "fixed_win_price": pending["fixed_win_price"].astype(float),
    })
    
    # Append to existing history
    if PRICE_HISTORY_CSV.exists():
        try:
            hist = pd.read_csv(PRICE_HISTORY_CSV, dtype={"run_id": str, "race_id": str})
            hist = pd.concat([hist, snap], ignore_index=True)
        except Exception as e:
            print(f"  Warning: could not load price history ({e}); starting fresh")
            hist = snap
    else:
        hist = snap
    
    # Cull older than 7 days
    cutoff = (datetime.now(timezone.utc) - timedelta(days=7)).isoformat()
    hist = hist[hist["snapshot_time"] >= cutoff]
    
    hist.to_csv(PRICE_HISTORY_CSV, index=False)
    print(f"  Snapshot saved: {len(snap)} prices (history now {len(hist)} rows)")








# Mobile Safari real-world report (Sep 2026): toprate_data.json is ~85-90MB
# (see this file's own "100MB-limit" comments) and GitHub Pages' CDN does
# not compress files this large (community-reported ceiling around ~10MB;
# confirmed indirectly here by how slowly the live site loaded on a phone
# before this existed), so the frontend was downloading the full raw size
# every load. Writing a gzip companion here (checked: ~85MB -> ~18MB, a
# ~5x cut) lets the frontend fetch toprate_data.json.gz and decompress
# client-side via the DecompressionStream API instead (supported on iOS
# Safari since 16.4, so safe by now) - same data, far less to transfer and
# parse on a mobile connection. Falls back to plain toprate_data.json if
# the .gz fetch or DecompressionStream itself is unavailable (see
# fetchData.ts). compresslevel=6 (gzip's own default) - the fast level (1)
# saves little size for a payload this compressible, and this write
# happens on every price/results cycle so it should stay cheap, not chase
# the last few % a slower level (9) would cost real time for.
def _write_data_json(path, text):
    """Writes toprate_data.json AND its .gz companion together, so the two
    can never drift out of sync (see the module comment above) - EVERY
    write site for toprate_data.json must go through this, not
    path.write_text() directly, including patch_data_json()'s fast path
    below (a stale .gz after a price/result patch would silently serve old
    data to every gzip-capable client until the next full rebuild)."""
    path.write_text(text, encoding="utf-8")
    gz_path = path.with_name(path.name + ".gz")
    # mtime=0: gzip's header otherwise embeds the write time, which would
    # make two writes of BYTE-IDENTICAL content produce different git
    # diffs for no reason (harmless here since every real write also
    # changes RUN_ISO, but no reason to add spurious churn on top of that).
    with gzip.GzipFile(gz_path, mode="wb", compresslevel=6, mtime=0) as gz:
        gz.write(text.encode("utf-8"))


HISTORY_JSON_NAME = "toprate_history.json"


def _melbourne_today():
    try:
        from zoneinfo import ZoneInfo
        return datetime.now(ZoneInfo("Australia/Melbourne")).date().isoformat()
    except Exception:
        return (datetime.now(timezone.utc) + timedelta(hours=10)).date().isoformat()


# Payload slimming (14 Oct 2026). toprate_history.json had grown to 77 MB of the 100 MB GitHub limit. Two kinds of dead weight, neither read by the frontend:
#  1. runner keys nothing in frontend/src reads any more (TopRate-era ratings and speed scores that the payload writes as null, the old projection's alternates,
#     miss notes, form string, distance stats): _DEAD_RUNNER_KEYS, which frontend/src/types/data.ts no longer declares either;
#  2. null-valued keys inside the per-run form records (formRuns, peakRun, formAll and the horse_history files): the sectional and race-shape fields are blank
#     on every run, which was 11.6 MB of '"se":null,...'. The adapter reads every nullable field with ?? null, so an absent key means null.
_DEAD_RUNNER_KEYS = frozenset((
    "trr", "trp", "ff", "jrt", "trt", "spd", "es", "ms", "ls", "ts", "cs", "crk", "csc", "w", "wd", "wtr", "ds", "dw", "dp", "fm", "wpr1", "wpra", "wprt", "wprp",
    "jcp", "jcr", "wpjc", "wpjcA", "wpjpA", "wpjep", "wpjem", "wpjmc", "wpjmr", "wpjbpr", "wpjbp", "wpjbr", "asTend"))


def _drop_nulls(rec):
    return {k: v for k, v in rec.items() if v is not None}


def _slim_payload(data):
    """Return data with dead runner keys and null form-record keys removed (in place on the runner dicts)."""
    for race in data.get("RACES") or []:
        for u in race.get("runners") or []:
            for k in _DEAD_RUNNER_KEYS:
                u.pop(k, None)
            for lst in ("formRuns", "formAll"):
                if u.get(lst):
                    u[lst] = [_drop_nulls(e) for e in u[lst]]
            if u.get("peakRun"):
                u["peakRun"] = _drop_nulls(u["peakRun"])
    return data


def _write_payload(data, out_dir):
    """Write the dashboard payload as two files (Sep 2026, load speed):
      toprate_data.json     every key, RACES = today's and later races (Melbourne date); what the page
                            waits for (~20MB raw / ~4MB gz instead of ~90 / ~18)
      toprate_history.json  {"RACES": earlier races, "RUN_ISO": ...}, fetched by the frontend in the
                            background after the page is up and merged in (race_id dedupe, current wins)
    toprate_data.json carries HISTORY_ISO (when the history file was last written) so the frontend only
    refetches history when it changed. Both go through _write_data_json (each with its .gz companion)."""
    data = _slim_payload(data)
    today = _melbourne_today()
    races = data.get("RACES") or []
    current = [r for r in races if str(r.get("date", "")) >= today]
    history = [r for r in races if str(r.get("date", "")) < today]
    iso = data.get("RUN_ISO") or datetime.now(timezone.utc).isoformat()
    _write_data_json(out_dir / HISTORY_JSON_NAME,
                     json.dumps({"RACES": history, "RUN_ISO": iso}, separators=(",", ":")))
    _write_data_json(out_dir / "toprate_data.json",
                     json.dumps({**data, "RACES": current, "HISTORY_ISO": iso}, separators=(",", ":")))


def projection_stale():
    """True when the projection log holds a projection made after the newest one applied to toprate_runners.csv (its wprp_made column).
    Cheap (the log is small and only one CSV column is read), so tab_results_poller.py checks it every cycle: projection_daily.yml commits
    the log but nothing else carries it into the payload between full rebuilds."""
    try:
        from projection import projlog
        lg = projlog.load()
        if lg.empty or "made" not in lg.columns:
            return False
        _live = runners_io.live_path()
        if not _live.exists():
            return False
        head = pd.read_csv(_live, nrows=0).columns
        if "wprp_made" not in head:
            return True
        cur = pd.read_csv(_live, usecols=["run_id", "wprp_made"], dtype=str)
        # only log rows for runners in the live file count (the log also holds runners that are no longer in it, which would
        # keep this true forever)
        ids = set(pd.to_numeric(cur["run_id"], errors="coerce").dropna().astype("int64"))
        lg = lg[lg["run_id"].isin(ids)]
        if lg.empty:
            return False
        applied = cur["wprp_made"].dropna()
        return len(applied) == 0 or str(lg["made"].dropna().astype(str).max()) > str(applied.max())
    except Exception as e:
        print(f"  projection_stale check failed ({e}); not refreshing")
        return False


def refresh_projection(runners_df):
    """Re-apply the projection log to runners_df (every wprp_* projection column, fair price and rank), then recompute the edge columns for
    today and later only (past dates keep theirs). Returns the updated frame."""
    runners_df = apply_new_projection(runners_df, recompute_edges=False)
    return runners_df


# payload key -> (runners column, kind) for the projection fields a refresh rewrites (same mapping as rebuild_html's runner dict)
_PROJ_PAYLOAD_FIELDS = {
    "wpjp": ("wprp_proj", "f"), "wpjsd": ("wprp_sd", "f"), "wpjmd": ("wprp_made", "s"), "wpjm": ("wprp_model", "s"), "wpjb": ("wprp_base", "f"), "wpjadj": ("wprp_adj", "f"),
    "wpjcb": ("wprp_contrib", "j"), "wpjpr": ("wprp_price", "f"), "wpjr": ("wprp_rank", "i"),
    "wpje": ("wprp_edge", "f"), "wpjd": ("wprp_desc", "s"),
}   # (14 Oct 2026: wpjc, wpjbp, wpjbr, wpjbpr, wpjep, wpjem dropped, nothing reads them, see _DEAD_RUNNER_KEYS)


def _proj_payload_value(v, kind):
    if kind in ("f", "i"):
        try:
            f = float(v)
        except Exception:
            return None
        if math.isnan(f):
            return None
        return round(f, 3) if kind == "f" else int(f)
    if v is None or (isinstance(v, float) and math.isnan(v)) or str(v) in ("", "nan", "None"):
        return None
    if kind == "j":
        if isinstance(v, dict):
            return v
        try:
            return json.loads(v)
        except Exception:
            return None
    return str(v)


def _patch_projection_fields(race_list, proj_rows):
    """Rewrite the projection fields of every runner in race_list that has a row in proj_rows (run_id -> row). Returns how many changed."""
    n = 0
    for race in race_list:
        for run in race.get("runners") or []:
            row = proj_rows.get(run.get("rid"))
            if row is None:
                continue
            for key, (col, kind) in _PROJ_PAYLOAD_FIELDS.items():
                run[key] = _proj_payload_value(row.get(col), kind)
            n += 1
    return n


def patch_data_json(price_updates=None, result_updates=None, scratch_updates=None, start_time_updates=None, proj_df=None, condition_df=None):
    """Lightweight, fast alternative to --rebuild-only for a cycle that only
    touched fixed_win_price/finish_position/won/scratched (TAB's live
    prices + fast results, see tab_results_poller.py) - NOT going/
    track_grading/rail_position, which still needs the full pipeline via a
    WPR recompute (tab_results_poller.py only calls this when there was no
    going change this cycle).

    Patches ONLY the touched runners' "fx"/"f"/"won"/"scr" keys directly
    into the existing toprate_data.json on disk (keyed by "rid" = run_id,
    matching how each runner is identified in the payload - see
    rebuild_html()'s runner dict), and flips a race's "done" flag to 1 (and
    "prov" to 1 alongside it - this function only ever runs from TAB's fast
    path, never the authoritative one, so any race it transitions to done
    is provisional by construction; a race already done before this patch
    is left exactly as-is, never downgraded back to provisional) once
    every one of its runners now has a finish position. Skips the
    expensive form-history/settling-band/per-race-payload build that
    dominates --rebuild-only's ~2.5-3 min cost entirely - none of those
    depend on any of these fields. RUN_ISO/RUN_DATE are refreshed too, so
    the dashboard's "as of" freshness indicator doesn't lag behind data
    that's actually current. PICKS_TODAY/MODEL_PICKS and every other
    derived field are left exactly as they were at the last full rebuild -
    price_refresh.yml's own periodic rebuild keeps those from staying
    stale indefinitely.

    price_updates/result_updates/scratch_updates: run_id -> value, as
    produced by tab_results_poller.py's apply_prices()/apply_results()
    `patches` return value.

    Returns True if the patch was applied (or there was nothing to patch),
    False if the caller should fall back to a full rebuild - missing/
    unparseable toprate_data.json, or any touched run_id not found in it
    (a brand-new runner that hasn't been through a full rebuild yet; safer
    to fall back than ship a half-patched payload).
    """
    price_updates = price_updates or {}
    result_updates = result_updates or {}
    scratch_updates = scratch_updates or {}
    # start_time_updates: race_id -> start_time (TAB moved the race, tab_results_poller.apply_start_times)
    start_time_updates = {str(k): v for k, v in (start_time_updates or {}).items()}
    touched = set(price_updates) | set(result_updates) | set(scratch_updates)
    if not touched and not start_time_updates and proj_df is None and condition_df is None:
        return True

    data_path = OUTPUT_HTML.parent / "toprate_data.json"
    hist_path = OUTPUT_HTML.parent / HISTORY_JSON_NAME
    if not data_path.exists():
        print("  patch_data_json: toprate_data.json doesn't exist yet, falling back to full rebuild")
        return False
    try:
        data = json.loads(data_path.read_text(encoding="utf-8"))
    except Exception as e:
        print(f"  patch_data_json: could not read/parse toprate_data.json ({e}), falling back to full rebuild")
        return False

    races = data.get("RACES")
    if not isinstance(races, list):
        return False

    def _patch(race_list, remaining):
        """Patch the touched runners in race_list; returns True if any runner in it was touched."""
        hit = False
        for race in race_list:
            runners = race.get("runners")
            if not isinstance(runners, list):
                continue
            for run in runners:
                rid = run.get("rid")
                if rid in price_updates:
                    run["fx"] = price_updates[rid]
                    remaining.discard(rid)
                if rid in result_updates:
                    run.update(result_updates[rid])
                    remaining.discard(rid)
                if rid in scratch_updates:
                    run["scr"] = scratch_updates[rid]
                    remaining.discard(rid)
            was_done = race.get("done") == 1
            if any(rr.get("rid") in touched for rr in runners) and runners:
                hit = True
                if not was_done:
                    # A runner's outcome counts as known either way: an exact "f"
                    # (finish position), or tab_results_poller.py's "assume
                    # unplaced" rule (won=0 with f still None, for a runner
                    # confirmed outside the reported top 4 - see apply_results()).
                    # A scratched runner never gets a finish or a won value, so it must not hold the race open (11 Oct 2026:
                    # Seymour R3/R4 had every runner that ran resolved but 3 to 4 scratchings, so done never flipped)
                    if all(rr.get("f") is not None or rr.get("won") is not None or rr.get("scr") == 1
                           for rr in runners):
                        race["done"] = 1
                        # This function only ever runs from tab_results_poller.py's
                        # fast path (see its own docstring) - the authoritative
                        # resulted pass always goes through the full rebuild
                        # instead, so a race genuinely TRANSITIONING to done here
                        # is by construction provisional. A race that was already
                        # done before this patch (however it got there) is left
                        # exactly as-is - this function never downgrades an
                        # already-confirmed "done" back to provisional.
                        race["prov"] = 1
        return hit

    remaining = set(touched)
    _patch(races, remaining)
    races_left = set(start_time_updates)
    for race in races:
        rid = str(race.get("race_id"))
        if rid in start_time_updates:
            race["start_time"] = start_time_updates[rid]
            races_left.discard(rid)
    if races_left:
        # a race not in the current payload yet (e.g. tomorrow's, before its first full rebuild) - the runners
        # file has the new time and the next full rebuild carries it, so this is not a reason to fall back
        print(f"  patch_data_json: start time for {len(races_left)} race(s) not in the current payload, skipped")
    # A touched runner not in the current file (e.g. a late result for yesterday) is looked for in the
    # history file (split payload, see _write_payload)
    hist, hist_hit = None, False
    if remaining and hist_path.exists():
        try:
            hist = json.loads(hist_path.read_text(encoding="utf-8"))
            hist_hit = _patch(hist.get("RACES") or [], remaining)
        except Exception as e:
            print(f"  patch_data_json: could not read/parse {HISTORY_JSON_NAME} ({e})")

    if remaining:
        print(f"  patch_data_json: {len(remaining)} touched runner(s) not found in current "
              f"payload, falling back to full rebuild")
        return False

    if proj_df is not None:
        # projection_daily.yml committed a newer projection log: carry it into the runners in this file (today and later;
        # earlier days are in the history file and keep the projection they were made with)
        cols = [col for col, _ in _PROJ_PAYLOAD_FIELDS.values()]
        sub = proj_df[["run_id"] + [c for c in cols if c in proj_df.columns]].copy()
        sub["run_id"] = sub["run_id"].astype(str)
        rows = {r["run_id"]: r for r in sub.to_dict("records")}
        n_proj = _patch_projection_fields(races, rows)
        print(f"  patch_data_json: refreshed the projection on {n_proj} runner(s)")

    if condition_df is not None:
        # going / track grading / rail changed at some meetings: copy them onto those meetings' races (race-level keys),
        # instead of a 4+ minute full rebuild (the projection now comes from the log, so nothing else depends on going here)
        cd = condition_df.drop_duplicates("race_id", keep="first")
        by_race = {str(r["race_id"]): r for r in cd[["race_id", "going", "track_grading", "rail_position"]].to_dict("records")}
        def _s(v):
            return "" if v is None or str(v) in ("nan", "None") else str(v)
        n_cond = 0
        for race in races:
            row = by_race.get(str(race.get("race_id")))
            if row is None:
                continue
            new_c = (_s(row["going"]), _s(row["track_grading"]), _s(row["rail_position"]))
            if new_c != (race.get("going"), race.get("track_grading"), race.get("rail")):
                race["going"], race["track_grading"], race["rail"] = new_c
                n_cond += 1
        print(f"  patch_data_json: updated going/grading/rail on {n_cond} race(s)")

    now_utc = datetime.now(timezone.utc)
    data["RUN_ISO"] = now_utc.isoformat()
    data["RUN_DATE"] = now_utc.strftime("%d %b %Y %H:%M UTC")
    if hist_hit:
        hist["RUN_ISO"] = data["RUN_ISO"]
        data["HISTORY_ISO"] = data["RUN_ISO"]
        _write_data_json(hist_path, json.dumps(hist, separators=(",", ":")))

    _write_data_json(data_path, json.dumps(data, separators=(",", ":")))
    return True


def _slugify_venue(venue):
    """URL/filename-safe slug for a venue name, for horse_history/ filenames."""
    s = re.sub(r"[^a-z0-9]+", "-", str(venue).strip().lower()).strip("-")
    return s or "venue"


_TR_ACTUAL = {}


def _tr_actual():
    """TopRate's plain-scale rating by (lowercased horse, date), cached; {} if the store is unreadable."""
    if "v" not in _TR_ACTUAL:
        try:
            from projection import features as _F
            _TR_ACTUAL["v"] = _F.tr_actual_by_name()
        except Exception as e:
            print(f"  TopRate actual lookup unavailable: {e}")
            _TR_ACTUAL["v"] = {}
    return _TR_ACTUAL["v"]


def _compute_atw_offsets(fh):
    """Moved to atw_offsets.py (shared with projection/run.py)."""
    return _atw_offsets_mod.compute_atw_offsets(fh)


def build_horse_history_files(runners_df, full_runs_lookup):
    """Write horse_history/<date>_<venue-slug>.json, one per (date, venue)
    meeting in runners_df (already windowed to the same range as the RACES
    payload by the time rebuild_html() calls this - see its own windowing
    step). Each file bundles the FULL (uncapped) form history for every
    horse racing at that meeting, keyed by horse_lc, in the exact same
    shape as the embedded payload's own formRuns (see _run_record()) so
    the frontend's existing toFormRun() mapper works unmodified. Carries
    only "runs" (RawFormRun[], including field_size) - NOT a second,
    formAll-shaped copy of the same rows: everything a consumer might have
    wanted from that (tempo, relativeSettlePosition) is derivable from
    fields already in "runs", so embedding both was pure duplication (see
    git history for the real numbers this measurably cost before it was
    trimmed - about half the payload for zero new information).

    This is the static replacement for the dropped Supabase live fetch
    RecentRunsTable.tsx used to depend on for anything past the embedded
    payload's last-N cap (see CLAUDE.md's Current state note - that fetch
    silently failed once Supabase was decommissioned, with no visible
    error, capping every horse's "Recent runs" panel at _FORM_RUNS_SHOWN
    regardless of real career length).

    One file per MEETING, not per horse (would be thousands of tiny files,
    most never fetched in a given day) or one combined file (the exact
    mistake that blew toprate_data.json past GitHub's 100MB limit once
    already) - real numbers measured before choosing this (Sep 2026): 222
    meetings in a 25-day window, largest single file ~1MB (safely under
    the 100MB PER-FILE limit that actually matters here - GitHub has no
    equivalent hard limit on file COUNT or combined size). Every runner at
    a meeting shares one fetch, so opening several horses from the same
    field (the common case - comparing a whole race) costs one request,
    not one per horse.

    Only writes a file when its content actually changed, and removes
    stale files for meetings that rolled out of the window - this runs on
    every rebuild_html() call, including price_refresh.yml's frequent
    cycles, and horse form history only changes once a day at most, so
    rewriting ~200 identical files every few minutes would be pure git
    churn for no reason. Fail-safe: any error here is logged and swallowed
    rather than breaking the rest of the rebuild - a missing/stale meeting
    file just means that meeting's Recent runs falls back to the embedded
    capped data, same as before this existed.
    """
    try:
        HORSE_HISTORY_DIR.mkdir(exist_ok=True)
        needed = set()
        for (d, venue), grp in runners_df.groupby(["date", "venue"]):
            fname = f"{str(d)[:10]}_{_slugify_venue(venue)}.json"
            needed.add(fname)
            blob = {}
            for horse_lc in grp["horse"].astype(str).str.strip().str.lower().unique():
                runs = full_runs_lookup.get(horse_lc)
                if not runs:
                    continue
                blob[horse_lc] = [_drop_nulls(r) for r in runs]
            if not blob:
                continue
            # sort_keys so identical content always serializes identically -
            # the unchanged-file skip below depends on that determinism.
            content = json.dumps(blob, separators=(",", ":"), sort_keys=True)
            path = HORSE_HISTORY_DIR / fname
            if path.exists() and path.read_text(encoding="utf-8") == content:
                continue
            path.write_text(content, encoding="utf-8")

        n_removed = 0
        for existing in HORSE_HISTORY_DIR.glob("*.json"):
            if existing.name not in needed:
                existing.unlink()
                n_removed += 1
        print(f"  horse_history/: {len(needed)} meeting files current"
              f"{f', {n_removed} stale removed' if n_removed else ''}")
    except Exception as e:
        print(f"  build_horse_history_files skipped: {e}")


def rebuild_html(runners_df, model_pick_rows=None):
    """
    Render the v3 dashboard HTML.

    Builds the data payload from runners_df and model_pick_rows, then delegates
    to toprate_html_v3.render_html() for the actual template work.
    """
    if runners_df is None or len(runners_df) == 0:
        print("No runners data - skipping HTML rebuild.")
        return

    # Import the template renderer (kept in a separate module for clarity)
    try:
        from toprate_html_v3 import render_html
    except ImportError as e:
        print(f"  Cannot import toprate_html_v3 module: {e}")
        print("  Make sure toprate_html_v3.py is in the same directory.")
        return

    # ── Build per-race data structure with full runner detail ────────────────

    # Lightweight step timing - the rebuild has several phases and the
    # form-history step in particular can run ~60s, during which the
    # script looks hung. These prints make progress visible. import time
    # locally to avoid touching module-level imports.
    import time as _time
    _t0 = _time.time()
    def _step(msg):
        print(f"  [{_time.time() - _t0:5.1f}s] {msg}", flush=True)

    # ── Window runners_df to the same recent range render_html() keeps ───────
    # render_html() (toprate_html_v3.py) already discards any race older than
    # TOPRATE_RACES_WINDOW_DAYS (default 25, reduced from 30 Sep 2026 - the
    # 30-day payload had grown to 94.4MB and was closing in on GitHub's
    # 100MB file limit; 25 days measured out at 81.3MB, ~19MB of headroom
    # for continued organic per-runner payload growth) from the final
    # payload - but only AFTER this function has spent most of its runtime
    # building the form-history lookup, settling-band lookup, and full
    # per-race runner payload for EVERY race ever recorded (39k+ runners
    # across 4k+ races as of 2026-08), not just the ~1k that survive the
    # window. Pre-filter here so that work is never done in the first
    # place. +2 day buffer so this is always a superset of whatever
    # render_html() keeps - never narrower - so the final HTML/JSON output
    # is unaffected, just faster to build.
    _orig_runner_count = len(runners_df)
    try:
        _win_days = int(os.environ.get("TOPRATE_RACES_WINDOW_DAYS", "25")) + 2
        _win_cut = (datetime.now() - timedelta(days=_win_days)).strftime("%Y-%m-%d")
        _windowed = runners_df[runners_df["date"].astype(str).str[:10] >= _win_cut]
        if len(_windowed) > 0:
            runners_df = _windowed
    except Exception as _e:
        print(f"  runners_df windowing skipped ({_e})")
    _step(f"Windowed runners_df for HTML build: {_orig_runner_count:,} -> {len(runners_df):,} runners")
    # The feed sometimes carries no silks for a whole meeting (11 Oct 2026: Halidon, Cairns). A horse's colours rarely change, so a
    # runner with no silk gets the latest one the same horse had in this window. Payload only: the runners file keeps what the feed gave.
    try:
        _sk = runners_df[runners_df["silk_url"].notna() & (runners_df["silk_url"].astype(str) != "")]
        _last_silk = _sk.sort_values("date").groupby("horse_id")["silk_url"].last()
        _miss = runners_df["silk_url"].isna() | (runners_df["silk_url"].astype(str) == "")
        if _miss.any():
            runners_df = runners_df.copy()
            runners_df.loc[_miss, "silk_url"] = runners_df.loc[_miss, "horse_id"].map(_last_silk)
            print(f"  Silks filled from earlier runs for {int((_miss & runners_df['silk_url'].notna()).sum())} of {int(_miss.sum())} runners without one")
    except Exception as _e:
        print(f"  silk fallback skipped ({_e})")
    # New-model projections (projection/): re-applied on every rebuild so a fresh wpr_projection_log.csv.gz reaches the payload within
    # one price-refresh cycle. Works on this windowed copy only; the persisted CSV is written by the daily/poller paths.
    runners_df = apply_new_projection(runners_df.copy())

    _FORM_RUNS_SHOWN = 10  # rows kept per horse for the detail-panel form table

    _step(f"Building form-history lookup (last {_FORM_RUNS_SHOWN} + peak + tendency)...")

    # ── Form-history lookup for the runner detail panel ──────────────────────
    # Attach each runner's last _FORM_RUNS_SHOWN race runs (newest first) so
    # the Race-tab detail panel has a fast-painting, always-available form
    # table. Re-capped at 10 (Aug 2026) after a brief stint showing FULL
    # history embedded here - that blew toprate_data.json well past GitHub's
    # 100MB push limit even at a 10-day race window (see git history for the
    # real numbers measured). The frontend now fetches a horse's complete
    # history live from Supabase's wpr_form_history table when its detail
    # panel opens (RecentRunsTable.tsx) instead of needing it embedded here -
    # this capped list is just the instant-paint fallback shown before that
    # live fetch resolves (or if it fails). Scoped to the horses running in
    # runners_df only - never the whole 90k-row history - so the HTML
    # payload stays small. Fail-safe: any error leaves form_lookup empty and
    # runners simply get no formRuns (the live fetch still works either way).
    form_lookup = {}
    form_all_lookup = {}
    _peak_run_lookup = {}
    _tend_lookup = {}
    _full_runs_lookup = {}  # uncapped form_lookup, feeds build_horse_history_files()
    _atw_off_lookup = {}  # horse_lc -> ATW offset (see _compute_atw_offsets)
    # run_id -> expected (results-file atw minus plain wpr) for this run's weight/age/sex/month (atw_results_scale.py): puts the plain projection on the
    # scale of wpr_actual so the Review / result-card miss compares like with like. Fail-safe: {} = no shift.
    try:
        from atw_results_scale import results_scale_offsets
        _rso_lookup = results_scale_offsets(runners_df)
    except Exception as _e:
        print(f"  results-scale offsets skipped: {_e}")
        _rso_lookup = {}

    def _atwo_for_row(row):
        """ATW offset for the payload. The offset frozen in the projection log (wprp_atwo) wins, so a race that has run keeps the weight it ran at.
        Without one, only a race still to run takes the horse's latest offset (it is for its next start, so it would be wrong for a past race).
        13 Oct 2026: DISABLED. The form history is now our own plain rating (own_ratings/replace_form_ratings.py), so there is no shift to apply and the
        values frozen in the projection log (measured against TopRate's form feed) are stale."""
        return None
        try:
            v = float(row.get("wprp_atwo"))
            if v == v:
                return round(v, 1)
        except (TypeError, ValueError):
            pass
        ran = any(str(row.get(c)) in ("1", "1.0") for c in ("resulted", "interim_resulted"))
        return None if ran else _atw_off_lookup.get(str(row.get("horse", "")).strip().lower())
    try:
        if tr_form_store.DIR.exists():
            _today_horses = set(
                str(h).strip().lower() for h in runners_df.get("horse", []) if h)
            # Pending horses only - formAll (the heavy full-history
            # comparison-table data) is built for these alone, since the
            # comparison tables matter for upcoming races, not the
            # hundreds of old resulted ones. formRuns (cheap last-N) is
            # still built for every horse so resulted races keep a form
            # table.
            if "resulted" in runners_df.columns:
                _pending_horses = set(
                    str(h).strip().lower() for h in
                    runners_df[runners_df["resulted"] != 1].get("horse", [])
                    if h)
            else:
                _pending_horses = _today_horses
            # Recent runs / form history now come from TopRate's own past-run store (data/tr_form, 14 Oct 2026), not our wpr_form_history.csv.gz
            # rating chain: TopRate's wpr (rated at the weight of the horse's upcoming race), positions, margins, race shape, weights, prices, comments.
            _fh = tr_form_store.frame(_today_horses)
            if _fh.empty:
                _fh = pd.DataFrame(columns=["horse", "horse_lc", "date", "wpr"])
            _fh["wpr"] = pd.to_numeric(_fh["wpr"], errors="coerce")
            _fh["date"] = pd.to_datetime(_fh["date"], errors="coerce")
            _fh = _fh.dropna(subset=["date", "wpr"])
            if "isBarrierTrial" in _fh.columns:
                _fh = _fh[_fh["isBarrierTrial"].fillna(0).astype(int) == 0]
            # Dedupe: the same run can appear more than once in the form
            # history (a race scraped on two dates - the WPR rebaseline
            # issue). Without this the detail-panel form table shows each
            # run twice. Keep the latest scrape of each (horse, run date).
            # kind="stable" matters here: some rows share the exact same
            # scrape_date (a same-day re-scrape), so pandas' default
            # quicksort can break that tie differently depending on which
            # OTHER rows are present in the frame being sorted (e.g. after
            # filtering to a smaller horse set) - a latent bug that made
            # this pick a different "latest" row from one build to the
            # next for no data reason. A stable sort always preserves the
            # original file order for tied rows regardless of what else is
            # in the frame, so the same duplicate wins every time.
            _dedup_keys = ["horse_lc", "date"]
            if "track" in _fh.columns:
                _dedup_keys.append("track")
            if "scrape_date" in _fh.columns:
                _fh = _fh.sort_values("scrape_date", kind="stable")
            _fh = _fh.drop_duplicates(subset=_dedup_keys, keep="last")
            _fh = _fh.sort_values(["horse_lc", "date"])
            if "scrape_date" in _fh.columns and "horse_id" in _fh.columns:
                _atw_off_lookup = _compute_atw_offsets(_fh)
            # formAll derived columns - computed VECTORISED on the whole
            # frame ONCE, before the per-horse loop. The earlier version
            # used iterrows() over all ~90k rows, which was the rebuild
            # slowdown. iterrows is a pandas anti-pattern; this avoids it.
            _fa = _fh.copy()
            _fa["_w"] = pd.to_numeric(_fa["wpr"], errors="coerce").round(1)
            _fa["_ds"] = pd.to_numeric(_fa.get("distance"), errors="coerce")
            # The Fast/Even/Slow tempo label of a past run was derived from TopRate's sectional indexes (sect_i_early, sect_i_l600), which
            # are TopRate's analysis and no longer used; the label is left blank.
            _fa["_tmp"] = None
            _ps = pd.to_numeric(_fa.get("positionSettled"), errors="coerce")
            _fs = pd.to_numeric(_fa.get("field_size"), errors="coerce")
            _rel = (_ps / _fs).clip(upper=1.0).round(3)
            _rel = _rel.where((_fs > 0) & (_ps > 0))
            _fa["_rel"] = _rel
            _fa["_go"] = _fa.get("going", "").astype(str).where(
                _fa.get("going").notna(), "")
            # void flag (Sep 2026): same comment-only void test the
            # projection model itself uses to discount a compromised run
            # (vet/eased/checked/fell/etc, see wpr_void.void_from_comment_
            # only and wpr_projection._compute_base's own void-masking of
            # w) - exposed here so the dashboard's own career/condition
            # table can exclude the same runs from ITS averages instead of
            # silently disagreeing with the model's adjustment (found Sep
            # 2026: a horse's displayed "First-up avg" and the model's own
            # own_first_up figure diverged because only the model discounted
            # a checked run). Best-effort: any import/column failure leaves
            # every row void=False (unchanged prior behaviour).
            try:
                from wpr_void import void_from_comment_only as _void_fn
                _cv = _fa.get("comments_video")
                _cs = _fa.get("comments_steward")
                if _cv is None:
                    _cv = pd.Series([None] * len(_fa), index=_fa.index)
                if _cs is None:
                    _cs = pd.Series([None] * len(_fa), index=_fa.index)
                _fa["_void"] = [
                    _void_fn(a, b)[0] for a, b in zip(_cv, _cs)
                ]
            except Exception:
                _fa["_void"] = False
            # against-shape per run = horse late sectional minus race late
            # shape. Higher = ran home stronger than the race late shape.
            # Tendency per horse = mean over the LAST 5 runs (min 3),
            # date-sorted. Used by the panel "step-up form-reading" flag.
            # Honestly characterised - see FINDINGS_distance_suitability.md:
            # mean effect is +0.65 WPR (below the 1.0 materiality threshold
            # in the scoping doc and well inside the model's ~6 WPR error).
            # Built as DISPLAY-ONLY context, not a predictive claim.
            _tend_lookup = {}   # the "against the race shape" tendency came from TopRate sectional indexes; not computed any more
            # pre-group _fa by horse so the per-horse slice below is a
            # dict access, not a full-frame filter (the mistake that has
            # bitten this rebuild before).
            _fa_by_horse = dict(tuple(_fa.groupby("horse_lc")))

            def _shape(v):
                return round(float(v), 1) if pd.notna(v) else None

            # One run -> one form-table row dict. Shared by form_lookup's
            # capped last-N (below) and build_horse_history_files' full,
            # uncapped per-meeting export (rebuild_html's caller) - same
            # shape either way, so the frontend's toFormRun() mapper works
            # unmodified on both sources.
            def _run_record(_r, _peak_wpr, _extra=False):
                _w = float(_r["wpr"])
                # NOTE on sectionals - two different things, both kept:
                #  - se/sm/sl  = raceShapeEarly/Mid/Late: the RACE-WIDE
                #    tempo shape (how the race was run), NOT this horse.
                #  - ie/im/il  = sect_i_early / sect_i_to800 / sect_i_l600:
                #    THIS HORSE's own early/mid/late sectional figures.
                # Keeping both lets the panel show the horse's run and
                # (future work) compare it against the race shape.
                _rec = {
                    "d":  str(_r["date"].date()),
                    "trk": str(_r.get("track", "")) if _r.get("track") else "",
                    "dist": int(_r["distance"]) if pd.notna(_r.get("distance")) else None,
                    "go": str(_r.get("going", "")) if _r.get("going") else "",
                    "fin": int(_r["positionFinish"]) if pd.notna(_r.get("positionFinish")) else None,
                    "wpr": round(_w, 1),
                    "se": None,  # race shape early
                    "sm": None,    # race shape mid
                    "sl": None,   # race shape late
                    "ie": None,    # horse early sectional
                    "im": None,    # horse mid sectional
                    "il": None,     # horse late sectional
                    "bar": int(_r["barrier"]) if pd.notna(_r.get("barrier")) else None,
                    "mgn": _shape(_r.get("marginFinish")),   # finish margin
                    # running line: settled -> 800m -> 400m -> finish.
                    # gives the in-running position progression per run.
                    "psl": int(_r["positionSettled"]) if pd.notna(_r.get("positionSettled")) else None,
                    "p8": int(_r["position800m"]) if pd.notna(_r.get("position800m")) else None,
                    "p4": int(_r["position400m"]) if pd.notna(_r.get("position400m")) else None,
                    "cls": str(_r.get("race_class", "")) if _r.get("race_class")
                           and str(_r.get("race_class")) != "nan" else "",
                    # Jockey name for the form-table Jockey column. Present
                    # on rich-enriched runs; blank where form history has
                    # no jockey captured. No per-run jockey RATING exists
                    # in the form history (it is a current-race-only stat).
                    "jck": (str(_r.get("jockey")).strip()
                            if _r.get("jockey") and str(_r.get("jockey")) != "nan" else ""),
                    "pk": 1 if abs(_w - _peak_wpr) < 0.05 else 0,  # peak run flag
                    # field_size (Sep 2026): lets a consumer derive
                    # relativeSettlePosition (positionSettled/fieldSize)
                    # itself, same formula form_all_lookup's own "_rel"
                    # already uses - added so build_horse_history_files()'s
                    # export doesn't need a second, redundant copy of every
                    # run just to carry that one extra derived value.
                    "fs": int(_r["field_size"]) if pd.notna(_r.get("field_size")) else None,
                }
                if _extra:
                    # Weight carried and starting price per run (Oct 2026): only on the
                    # uncapped horse_history/ export, NOT the embedded payload, whose
                    # history file is already close to GitHub's 100MB limit.
                    _wt = pd.to_numeric(_r.get("weightCarried"), errors="coerce")
                    _sp = pd.to_numeric(_r.get("priceStarting"), errors="coerce")
                    _rec["wt"] = round(float(_wt), 1) if pd.notna(_wt) and 40 <= _wt <= 80 else None
                    _rec["sp"] = round(float(_sp), 2) if pd.notna(_sp) and _sp > 1 else None
                    # race number, so the dashboard can link that run's Sky replay (replay_codes.py)
                    _rn = pd.to_numeric(_r.get("raceNumber"), errors="coerce")
                    _rec["rn"] = int(_rn) if pd.notna(_rn) and 1 <= _rn <= 15 else None
                return _rec

            for _hlc, _g in _fh.groupby("horse_lc"):
                _last = _g.tail(_FORM_RUNS_SHOWN)
                _peak_wpr = _g["wpr"].max()
                # Find the most recent run at peak WPR that is OUTSIDE
                # the visible-runs window. If the peak is already visible,
                # leave peakRun null - the panel only needs the extra row
                # when the peak is older. Tolerance 0.05 mirrors the pk flag.
                _last_ids = set(_last.index.tolist())
                _peak_rows = _g[
                    (_g["wpr"] - _peak_wpr).abs() < 0.05]
                _peak_outside = _peak_rows[~_peak_rows.index.isin(_last_ids)]
                _peak_run_record = None
                form_lookup[_hlc] = [
                    _run_record(_r, _peak_wpr) for _, _r in _last.iloc[::-1].iterrows()  # newest first
                ]
                # Uncapped, full-career version of the same rows - feeds
                # build_horse_history_files() below, never the embedded
                # payload (which stays capped at _FORM_RUNS_SHOWN).
                _full_runs_lookup[_hlc] = [
                    _run_record(_r, _peak_wpr, _extra=True) for _, _r in _g.iloc[::-1].iterrows()  # newest first
                ]
                # peakRun: a single rich record for the most recent
                # career-peak run that falls OUTSIDE the visible-runs window.
                # Used by the detail panel to surface the peak as a full
                # form-table row when the visible runs do not include it.
                if not _peak_outside.empty:
                    _pr = _peak_outside.sort_values("date").iloc[-1]
                    def _shape_pr(v):
                        return round(float(v), 1) if pd.notna(v) else None
                    _peak_run_record = {
                        "d":  str(_pr["date"].date()),
                        "trk": str(_pr.get("track", "")) if _pr.get("track") else "",
                        "dist": int(_pr["distance"]) if pd.notna(_pr.get("distance")) else None,
                        "go": str(_pr.get("going", "")) if _pr.get("going") else "",
                        "fin": int(_pr["positionFinish"]) if pd.notna(_pr.get("positionFinish")) else None,
                        "wpr": round(float(_pr["wpr"]), 1),
                        "se": _shape_pr(_pr.get("raceShapeEarly")),
                        "sm": _shape_pr(_pr.get("raceShapeMid")),
                        "sl": _shape_pr(_pr.get("raceShapeLate")),
                        "ie": _shape_pr(_pr.get("sect_i_early")),
                        "im": _shape_pr(_pr.get("sect_i_to800")),
                        "il": _shape_pr(_pr.get("sect_i_l600")),
                        "bar": int(_pr["barrier"]) if pd.notna(_pr.get("barrier")) else None,
                        "mgn": _shape_pr(_pr.get("marginFinish")),
                        "psl": int(_pr["positionSettled"]) if pd.notna(_pr.get("positionSettled")) else None,
                        "p8": int(_pr["position800m"]) if pd.notna(_pr.get("position800m")) else None,
                        "p4": int(_pr["position400m"]) if pd.notna(_pr.get("position400m")) else None,
                        "cls": str(_pr.get("race_class", "")) if _pr.get("race_class")
                               and str(_pr.get("race_class")) != "nan" else "",
                        "jck": (str(_pr.get("jockey")).strip()
                                if _pr.get("jockey") and str(_pr.get("jockey")) != "nan" else ""),
                        "pk": 1,
                    }
                _peak_run_lookup[_hlc] = _peak_run_record
                # formAll: a COMPACT record of EVERY run, for the
                # detail-panel comparison tables. Built from the
                # pre-computed _fa frame - no iterrows, just a grouped
                # slice and a single zip. Built for all horses.
                _fa_g = _fa_by_horse.get(_hlc)
                if _fa_g is None:
                    form_all_lookup[_hlc] = []
                    continue
                _fa_g = _fa_g[_fa_g["_w"].notna()]
                _recs = []
                _fa_dates = (_fa_g["date"].astype(str).str[:10]
                             if "date" in _fa_g.columns
                             else [""] * len(_fa_g))
                _fa_void = (_fa_g["_void"] if "_void" in _fa_g.columns
                            else [False] * len(_fa_g))
                for _w, _go, _ds, _tmp, _rel, _dt, _vd in zip(
                        _fa_g["_w"], _fa_g["_go"], _fa_g["_ds"],
                        _fa_g["_tmp"], _fa_g["_rel"], _fa_dates, _fa_void):
                    _recs.append({
                        "w": float(_w),
                        "go": _go if isinstance(_go, str) else "",
                        "ds": int(_ds) if pd.notna(_ds) else None,
                        "tmp": _tmp if (_tmp is not None
                                        and _tmp == _tmp) else None,
                        "rel": float(_rel) if pd.notna(_rel) else None,
                        "d": _dt,   # run date - lets the payload exclude the
                                    # current race from the comparison tables,
                                    # same as formRuns (display-only).
                        # void (Sep 2026): True if this run was compromised
                        # (vet/eased/checked/fell/etc per steward/video
                        # comments) - same test the projection model itself
                        # uses to discount a run's WPR from own-history
                        # averages. Only emitted True (never False) to keep
                        # the payload from growing a redundant key on every
                        # one of a horse's runs - falsy/absent means valid.
                        **({"void": True} if bool(_vd) else {}),
                    })
                form_all_lookup[_hlc] = _recs
    except Exception as _e:
        print(f"  Form-history lookup skipped: {_e}")
        form_lookup = {}
        form_all_lookup = {}
        _peak_run_lookup = {}
        _tend_lookup = {}
        _full_runs_lookup = {}
        _atw_off_lookup = {}

    build_horse_history_files(runners_df, _full_runs_lookup)

    # Predicted settling band per runner, for the detail-panel settling
    # comparison table (this IS the live speed map's data source). Uses
    # settling_estimate's TRAINED MODEL (Sep 2026 rebuild - see that
    # module's docstring for why a hand-tuned linear formula was replaced:
    # the exact same 5 inputs, fit by a small LightGBM model instead of a
    # linear combination, cut held-out MAE by roughly 10x every other
    # improvement found in that investigation - a deliberate trade of the
    # old design's formula-level auditability for that size of gain).
    #
    # VECTORISED: a horse's run-style tendency etc. are stable per-horse
    # numbers. The pre-Sep-2026 version date-filtered the horse's history
    # per runner (~thousands of pandas ops, ~130s) - these are each
    # computed once via one groupby/rolling pass, then the model predicts
    # every runner in ONE batched call, not per-row.
    #
    # BUG FIX (Sep 2026): _sfh was never deduped before this groupby -
    # 42% of (horse, date) row-pairs are duplicated from a WPR rebaseline
    # re-scrape issue (this session's own established, mandatory-dedup
    # finding - every other trailing-history computation in this codebase
    # already applies it, this one spot didn't). Quantified impact on
    # this exact computation: mean |difference| 0.013 across 18,185
    # horses, 25% of horses shifted by >0.02, 5.5% by >0.05 (enough to
    # flip the displayed band) - a real, live, user-facing accuracy bug
    # in the speed map, not just a research-script issue.
    _step("Building settling-band lookup...")
    _settle_band_lookup = {}
    # _settle_rel_lookup (Sep 2026): the CONTINUOUS 0-1 value _band_of()
    # buckets into psBand's 4 strings - was computed here already
    # (_rel_est_all) and discarded. Exposed for the grid-style speed map
    # (frontend/src/features/race/SpeedMapGrid.tsx), which needs finer
    # placement than 4 bands give.
    _settle_rel_lookup = {}
    try:
        import settling_estimate as _se_mod
        if WPR_FORM_HISTORY_CSV.exists():
            _sfh = pd.read_csv(WPR_FORM_HISTORY_CSV,
                               dtype={"horse": str}, low_memory=False)
            _sfh["horse_lc"] = _sfh["horse"].astype(str).str.strip().str.lower()
            if "isBarrierTrial" in _sfh.columns:
                _sfh = _sfh[_sfh["isBarrierTrial"].fillna(0).astype(int) == 0]
            if "scrape_date" in _sfh.columns:
                _sfh = _sfh.sort_values("scrape_date").drop_duplicates(
                    subset=["horse_lc", "date", "track"], keep="last")
            _sfh["date"] = pd.to_datetime(_sfh["date"], errors="coerce")
            _sfh = _sfh.dropna(subset=["date"]).sort_values(["horse_lc", "date"])

            # run-style tendency per horse (ALL-TIME mean relative settle,
            # same definition settling_estimate.run_style_tendency uses).
            _ps = pd.to_numeric(_sfh.get("positionSettled"), errors="coerce")
            _fs = pd.to_numeric(_sfh.get("field_size"), errors="coerce")
            _rel = (_ps / _fs).clip(0, 1)
            _rel = _rel.where((_ps > 0) & (_fs > 0))
            _sfh = _sfh.assign(_rel=_rel)

            # Tactical-variance exclusion (settling_estimate.TACTICAL_MARKERS) -
            # a run deliberately ridden further back than normal doesn't
            # represent this horse's usual style, so it shouldn't count
            # toward run_style_tendency/last5_tendency here either - must
            # mirror settling_estimate.train()'s own exclusion or this
            # dashboard-facing lookup silently diverges from the live model.
            _cv = _sfh.get("comments_video", pd.Series("", index=_sfh.index)).fillna("").astype(str).str.lower()
            _is_tactical = _cv.apply(lambda t: any(m in t for m in _se_mod.TACTICAL_MARKERS))
            _rel_for_tendency = _rel.where(~_is_tactical)
            _sfh = _sfh.assign(_rel_tend=_rel_for_tendency)
            _grp = _sfh.dropna(subset=["_rel_tend"]).groupby("horse_lc")["_rel_tend"]
            _tendency = _grp.mean().to_dict()

            # last5_tendency per horse - same definition as
            # settling_estimate.last5_tendency, vectorised via rolling(5)
            # over each horse's own full (deduped, date-sorted) history.
            _last5 = (_sfh.dropna(subset=["_rel_tend"]).groupby("horse_lc")["_rel_tend"]
                          .apply(lambda s: s.rolling(5, min_periods=1).mean().iloc[-1]).to_dict())

            # trailing early-speed rating per horse, winsorized at the
            # fitted population bounds (settling_estimate.SECT_EARLY_LO/HI).
            _sect_raw = pd.to_numeric(_sfh.get("sect_i_early"), errors="coerce")
            _sect_clipped = _sect_raw.clip(_se_mod.SECT_EARLY_LO, _se_mod.SECT_EARLY_HI)
            _sfh = _sfh.assign(_sect=_sect_clipped)
            _sect_tendency = _sfh.dropna(subset=["_sect"]).groupby("horse_lc")["_sect"].mean().to_dict()

            # 3 extra trailing sectionals per horse (Sep 2026, see
            # settling_estimate.py's module docstring for the validated
            # result) - same winsorize-then-mean pattern as sect_i_early
            # above, one per field.
            _extra_tendency = {}
            for _col, _lo, _hi in [
                ("sect_ld_early", _se_mod.SECT_LD_EARLY_LO, _se_mod.SECT_LD_EARLY_HI),
                ("sect_i_to800", _se_mod.SECT_I_TO800_LO, _se_mod.SECT_I_TO800_HI),
                ("margin800m", _se_mod.MARGIN800M_LO, _se_mod.MARGIN800M_HI),
            ]:
                _raw = pd.to_numeric(_sfh.get(_col), errors="coerce")
                _clipped = _raw.clip(_lo, _hi)
                _tmp = _sfh.assign(_v=_clipped)
                _extra_tendency[_col] = _tmp.dropna(subset=["_v"]).groupby("horse_lc")["_v"].mean().to_dict()

            def _band_of(rel):
                if rel <= 0.20:
                    return "Leader"
                if rel <= 0.45:
                    return "On-pace"
                if rel <= 0.70:
                    return "Midfield"
                return "Back"

            # sect_rank_in_race: rank each runner's trailing early-speed
            # rating against the OTHER runners in the SAME today's race -
            # one vectorised groupby-rank over all runners at once, not a
            # per-race Python loop. Scratched runners are masked out of the
            # ranking POOL (a scratched horse isn't part of the field that
            # actually races) - found (Sep 2026) suppressing the genuinely-
            # best active runner's percentile in a real case.
            _runners_hlc = runners_df["horse"].astype(str).str.strip().str.lower()
            _runners_scratched = pd.to_numeric(runners_df.get("scratched"), errors="coerce").fillna(0) == 1
            _runners_sect = _runners_hlc.map(_sect_tendency)
            _runners_sect_active = _runners_sect.where(~_runners_scratched)
            _sect_rank_by_race = _runners_sect_active.groupby(runners_df["race_id"]).rank(pct=True)

            # sect_margin_to_rest: how CLEAR a runner's trailing early-speed
            # rating is of the rest of TODAY's active field, not just its
            # rank (see settling_estimate.SECT_MARGIN_LO's own docstring -
            # a rank alone can't tell "narrowly best" from "uncontested").
            def _margin_to_rest_group(s):
                vals = s.dropna()
                out = pd.Series(np.nan, index=s.index)
                if len(vals) < 2:
                    return out
                top_idx = vals.idxmax()
                field_max = vals.max()
                rest_max = vals.drop(top_idx).max()
                for idx in vals.index:
                    out[idx] = (vals[idx] - rest_max) if idx == top_idx else (vals[idx] - field_max)
                return out
            _sect_margin_by_race = _runners_sect_active.groupby(runners_df["race_id"]).transform(_margin_to_rest_group)
            _sect_margin_by_race = _sect_margin_by_race.clip(_se_mod.SECT_MARGIN_LO, _se_mod.SECT_MARGIN_HI)

            _runners_tend = _runners_hlc.map(_tendency)
            _runners_last5 = _runners_hlc.map(_last5)
            _runners_barrier = pd.to_numeric(runners_df.get("barrier"), errors="coerce")
            _runners_fsz = pd.to_numeric(runners_df.get("field_size"), errors="coerce")
            _draw_frac = ((_runners_barrier - 1) / (_runners_fsz - 1)).clip(0, 1)
            _draw_signal = (_draw_frac - 0.5) * 2
            _sect_signal = (_sect_rank_by_race - 0.5) * 2
            _runners_ld_early = _runners_hlc.map(_extra_tendency["sect_ld_early"])
            _runners_i_to800 = _runners_hlc.map(_extra_tendency["sect_i_to800"])
            _runners_margin800m = _runners_hlc.map(_extra_tendency["margin800m"])

            _has_tend = _runners_tend.notna()
            if _has_tend.any():
                _se_mod._load_model()
                _feat_df = pd.DataFrame({
                    "run_style_tendency": _runners_tend, "last5_tendency": _runners_last5,
                    "draw_signal": _draw_signal, "sect_signal": _sect_signal,
                    "field_size": _runners_fsz,
                    "trailing_sect_ld_early": _runners_ld_early,
                    "trailing_sect_i_to800": _runners_i_to800,
                    "trailing_margin800m": _runners_margin800m,
                    "sect_margin_to_rest": _sect_margin_by_race,
                })
                _med = _se_mod._CFG["medians"]
                _feat_df = _feat_df[_se_mod._CFG["features"]].apply(
                    lambda col: col.fillna(_med.get(col.name, 0.0)))
                _rel_est_all = _se_mod._MODEL.predict(_feat_df).clip(0, 1)

                _run_ids = runners_df["run_id"].astype(str)
                for _pos in np.where(_has_tend.to_numpy())[0]:
                    _rel_val = float(_rel_est_all[_pos])
                    _settle_band_lookup[_run_ids.iloc[_pos]] = _band_of(_rel_val)
                    _settle_rel_lookup[_run_ids.iloc[_pos]] = _rel_val
    except Exception as _e:
        print(f"  Settling-band lookup skipped: {_e}")
        _settle_band_lookup = {}
        _settle_rel_lookup = {}

    _step("Building per-race runner payload...")
    races_data = []
    for race_id, rdf in runners_df.groupby("race_id"):
        rdf = rdf.copy().reset_index(drop=True)
        if len(rdf) == 0:
            continue
        first = rdf.iloc[0]
        # start_time specifically needs to coalesce across the WHOLE race
        # group, not just trust row 0: a race_id can carry rows from more
        # than one fetch of differing completeness (e.g. an early
        # discovery pass before full detail was available, alongside a
        # later, complete re-fetch) - if the incomplete row happens to
        # sort first, first.get("start_time") silently returns its missing
        # value even though a good one exists elsewhere in the same
        # group. Found live Sep 2026: several meetings showed the literal
        # string "nan" as start_time (a still-separate bug - a missing
        # value is truthy in Python, so `if first.get(...)` didn't catch
        # it - fixed below at the payload line) purely because row 0
        # happened to be the incomplete fetch.
        _race_start_time = None
        if "start_time" in rdf.columns:
            _sst = rdf["start_time"].dropna().astype(str)
            _sst = _sst[_sst != "nan"]
            # a date-only placeholder (midnight written with seven fractional zeros, 15 Oct 2026 Hawkesbury R8 showed as 'jumping soon' at 13:00)
            # is not a start time: leave it blank, the page shows no time for the race
            _sst = _sst[~_sst.str.endswith(".0000000Z")]
            if len(_sst):
                _race_start_time = _sst.iloc[0]
        # Active (non-scratched) field size - a scratched runner stays in
        # rdf (its row is kept for history) but shouldn't count toward the
        # field the dashboard displays.
        _active_field_size = int((rdf.get("scratched").fillna(0).astype(int) != 1).sum()
                                  if "scratched" in rdf.columns else len(rdf))

        # Feeds both "done" and "prov" below - computed once here rather
        # than inline in the dict literal so both can reference it cleanly.
        # Scratched runners never run and never get a result row, so only the runners still in the field decide whether the race is done
        # (12 Oct 2026: races settled by own_ratings/apply_results showed "Interim result" for ever because their scratched rows stayed unresulted).
        _act = rdf[rdf["scratched"].fillna(0).astype(float) != 1] if "scratched" in rdf.columns else rdf
        if len(_act) == 0:
            _act = rdf
        _all_resulted = (_act["resulted"] == 1).all() if _act["resulted"].notna().any() else False
        _all_interim_resulted = (
            (_act.get("interim_resulted") == 1).all()
            if "interim_resulted" in _act.columns and _act["interim_resulted"].notna().any()
            else False
        )

        # Per-race cumulative score: predictive composite for quaddie/exotic use
        # Cumulative score removed (Stage 2) - WPR projection ranks runners.
        # Empty dict kept so the HTML payload code degrades gracefully until
        # the dashboard rework (Stage 4) removes the score UI.
        cum_lookup = {}

        # Review "actual" (14 Oct 2026): a projection made by the TopRate-rating models is on TopRate's scale, so it is compared with TopRate's own rating
        # for the run (runner pages, plain scale), not our chain's wpr_actual. None until that rating arrives; earlier (own-scale) projections keep wpr_actual.
        def _review_actual(row):
            if str(row.get("wprp_scale")) != "toprate":
                return row.get("wpr_actual")
            return _tr_actual().get((str(row.get("horse", "")).strip().lower(), str(row.get("date"))[:10]))

        # Build runner list with all the fields the template needs
        runners = []
        for _, row in rdf.iterrows():
            def sf(v):
                try:
                    f = float(v)
                    return None if math.isnan(f) else round(f, 3)
                except: return None
            def si(v):
                try:
                    f = float(v)
                    return None if math.isnan(f) else int(f)
                except: return None

            # Parse going_breakdown JSON if present (stored as string in CSV)
            gb = row.get("going_breakdown")
            if isinstance(gb, str) and gb.strip() and gb != "nan":
                try: gb_parsed = json.loads(gb)
                except: gb_parsed = {}
            elif isinstance(gb, dict):
                gb_parsed = gb
            else:
                gb_parsed = {}

            # Parse the WPR adjustment per-feature breakdown (also stored
            # as a JSON string in CSV, same convention as going_breakdown).
            contrib = row.get("wprp_contrib")
            if isinstance(contrib, str) and contrib.strip() and contrib != "nan":
                try: contrib_parsed = json.loads(contrib)
                except: contrib_parsed = None
            elif isinstance(contrib, dict):
                contrib_parsed = contrib
            else:
                contrib_parsed = None

            # Cumulative predictive score + rank within race (for quaddie/exotic aid)
            _cs = cum_lookup.get(str(row.get("run_id", "")), {})

            runners.append({
                "rid":  str(row.get("run_id", "")),
                "h":    str(row.get("horse", "")) if row.get("horse") else "",
                "j":    str(row.get("jockey", "")) if row.get("jockey") else "",
                "tn":   str(row.get("trainer", "")) if row.get("trainer") else "",
                "tab":  si(row.get("tab_number")),
                "t":    si(row.get("tab_number")),
                "b":    si(row.get("barrier")),
                # TopRate-authored values (rating, price, form factor, speed scores, trend, jockey/trainer rating) are no longer put in the payload;
                # the keys stay so the frontend types are unchanged (12 Oct 2026).
                "trr":  None,
                "trp":  None,
                # External "form factor" score (Sep 2026) - pfm_score in
                # toprate_runners.csv, never exposed here before now
                # (speedmap_jockey_tracker.py was the only prior consumer,
                # reading it straight from the CSV). 0-100, no in-race rank
                # needed for display purposes (unlike the tracker script's
                # own pfm_score_rank use).
                "ff":   None,
                "spd":  None,
                # All four sectional speed scores (the user wants Mid+Late+Total visible)
                "es":   None,
                "ms":   None,
                "ls":   None,
                "ts":   None,
                "wtr":  sf(row.get("weight_trend")),
                # TopRate's own forward rating (wpr_nett, from toprate.au race pages since 14 Oct 2026); blended into Proj by computeEffectiveRace
                "wn":   sf(row.get("wpr_nett")),
                # Distance performance: starts/wins/places at this distance ±10%
                "ds":   si(row.get("starts_at_dist")),
                "dw":   si(row.get("wins_at_dist")),
                "dp":   si(row.get("places_at_dist")),
                "wd":   None,
                # ATW offset (Oct 2026): form-feed rating minus results-file rating for this horse (see _compute_atw_offsets). The chart adds it
                # to the projection and the winning line so they sit on the same scale as the ATW history dots. None = no shift.
                "atwo": _atwo_for_row(row),
                # Results-scale offset (Oct 2026): add to the plain projection to compare it with wpr_actual (the results-file atw). See atw_results_scale.py.
                "rso": None if str(row.get("wprp_scale")) == "toprate" else _rso_lookup.get(si(row.get("run_id"))),  # TopRate-scale actual is the plain rating: no results-scale shift
                # Going performance breakdown - dict by category
                "gb":   gb_parsed,
                # Form string: last 4 finishes (e.g. "3-1-7-2")
                "fm":   str(row.get("form_string")) if row.get("form_string") and str(row.get("form_string")) != "nan" else None,
                # Finish margin in lengths - distinct from "fm" above which
                # is the form string. Keyed mgnL to avoid that collision.
                "mgnL": sf(row.get("margin_finish")),
                "asp":  sf(row.get("avg_settled_pos")),
                "wpr1": None,
                "wpra": None,
                "wprt": None,
                "wprp": None,
                "w":    None,
                "wt":   sf(row.get("weight_carried")),
                # Strike rates (already in CSV)
                "jw":   sf(row.get("jockey_win_pct_90d")),
                "tw":   sf(row.get("trainer_win_pct_365d")),
                # Ride/start counts behind jw/tw above (Sep 2026) - lets the
                # dashboard flag a strike rate built on a thin sample, same
                # reasoning as wpr_projection.py's own jockey_merit/
                # trainer_merit shrink (see that module's _merit_term
                # docstring). None until the API is confirmed to expose it.
                "jwN":  sf(row.get("jockey_starts_90d")),
                "twN":  sf(row.get("trainer_starts_365d")),
                # Jockey/trainer combination win% and ride count together.
                # DO NOT use for scoring/strategy - confirmed data leak, see
                # this field's definition comment above in SIGNALS. Kept for
                # display/reference only; the frontend's Strategy tiers that
                # used to gate on this are hard-disabled (jtComboStrategy.ts).
                "jcp":  sf(row.get("jt_combo_win_pct")),
                "jcr":  si(row.get("jt_combo_rides")),
                # TopRate's own jockey/trainer ratings (separate from strike rates)
                "jrt":  None,
                "trt":  None,
                "fx":   sf(row.get("fixed_win_price")),
                # Fixed price at first capture (the daily 9am AEST fetch),
                # frozen and never overwritten by the 5-min price refresh -
                # see the open_price freeze block near the daily fetch's
                # runner-dict merge. Lets the dashboard show how far today's
                # live "fx" has moved from this morning's price.
                "op":   sf(row.get("open_price")),
                # Silks image URL (full https URL ending in _front.png).
                # Dashboard renders an <img> on Race + Summary cards.
                "sk":   str(row.get("silk_url")) if row.get("silk_url") and str(row.get("silk_url")) != "nan" else None,
                "sp":   sf(row.get("starting_price_sp")),
                "top":  sf(row.get("price_top")),
                "f":    si(row.get("finish_position")),
                "won":  si(row.get("won")),
                "fs":   _active_field_size,
                # Late scratch (see toprate_price_refresh.py) - distinct from
                # the manual, this-device-only scratch toggle the frontend
                # already has; this is the real data-driven signal. si()
                # (not `row.get(...) or 0`) because a NaN is truthy in
                # Python - `NaN or 0` evaluates to NaN, not 0, and int(NaN)
                # raises. Every row captured before this column existed
                # reads back from CSV as float NaN, not None.
                "scr":  1 if si(row.get("scratched")) == 1 else 0,
                # Cumulative score keys: the model was removed so these are
                # null, but the dashboard JS still references u.cs/crk/csc in
                # several places; emit them (null) so those reads stay safe.
                "cs":   _cs.get("score"),
                "crk":  _cs.get("rank"),
                "csc":  _cs.get("conf"),
                # ── WPR projection (Step 2c) ─────────────────────────────────
                # wpj* keys deliberately distinct from existing "wprp"
                # (wpr_peak_rank_1yr) and "w"/"wpra" to avoid collisions.
                # None on fallback runners (under 3 prior runs).
                "wpjp":  sf(row.get("wprp_proj")),    # projected run-day WPR (new model)
                "wpjsd": sf(row.get("wprp_sd")),      # typical error of the projection (WPR points)
                "wpjmd": (str(row.get("wprp_made")) if row.get("wprp_made") not in (None, "", "nan") and str(row.get("wprp_made")) != "nan" else None),  # when the logged projection was made (after the race = back-filled)
                "wpjm":  (str(row.get("wprp_model")) if row.get("wprp_model") not in (None, "", "nan") and str(row.get("wprp_model")) != "nan" else None),  # main / light
                "wpjb":  sf(row.get("wprp_base")),    # base WPR (pre-adjustment)
                "wpjadj": sf(row.get("wprp_adj")),    # adjustment (base -> projected)
                "wpjcb": contrib_parsed,              # adjustment breakdown by feature
                "wpjc":  si(row.get("wprp_conf")),    # confidence 0-100
                "wpjpr": sf(row.get("wprp_price")),   # fair-value WPR price
                "wpjr":  si(row.get("wprp_rank")),    # WPR rank within race
                "wpjpk": sf(row.get("wprp_peak")),    # career peak WPR
                # Blend score (Step 2c2): the PRIMARY ranking as of Aug
                # 2026 (promoted from wpr_rank/wprp_rank - a held-out
                # backtest found it beats WPR-alone ranking on both top-1
                # strike rate and ROI, see wpr_projection.compute_edge_scores).
                # Needs no market price, same as wpjpr/wpjr.
                "wpjbp": sf(row.get("wprp_blend_prob")),   # blend win probability
                "wpjbr": si(row.get("wprp_blend_rank")),   # blend rank within race
                "wpjbpr": sf(row.get("wprp_blend_price")), # blend fair price
                # Edge score: blend win prob vs market implied win prob,
                # a bet-SELECTION filter on top of the blend ranking above
                # (not the same question as "which horse is best" - see
                # wpr_projection.compute_edge_scores). wpje is model_prob -
                # market_prob (0.08-0.10+ is where the held-out backtest
                # showed a real edge). None when there's no usable market
                # price (e.g. too early pre-race) or fewer than 2 priced
                # runners in the field.
                "wpje":  sf(row.get("wprp_edge")),
                "wpjep": sf(row.get("wprp_edge_prob")),
                "wpjem": sf(row.get("wprp_edge_mkt_prob")),
                # what-if projection for the opposite going (wet<->dry).
                # Lets the going override show a real model number, not a guess.
                "wpjpA": sf(row.get("wprp_proj_alt")),
                "wpjcA": si(row.get("wprp_conf_alt")),
                "wpjd":  str(row.get("wprp_desc")) if row.get("wprp_desc")
                         and str(row.get("wprp_desc")) != "nan" else None,
                # actual run-day WPR for resulted runners (Step 2e), and the
                # actual rank within the field. None until the form history
                # settles (~5 days post-race). Lets the dashboard show how
                # far the projection and ranking actually missed.
                "wpja":  sf(_review_actual(row)),
                "wpjar": si(row.get("wpr_actual_rank")),
                # Running (video) and stewards comments for resulted runners.
                # Drive the post-race variance subtab's auto-reason + display.
                # None until the result feed supplies them (post-race).
                "cmtV":  (str(row.get("comments_video"))
                          if row.get("comments_video") is not None
                          and str(row.get("comments_video")) not in ("", "nan") else None),
                "cmtS":  (str(row.get("comments_steward"))
                          if row.get("comments_steward") is not None
                          and str(row.get("comments_steward")) not in ("", "nan") else None),
                # Auto-generated explanation for a MATERIAL miss (|actual -
                # projected| >= 4 WPR, see wpr_miss.py's explain_miss()).
                # None when the miss isn't material, or the result hasn't
                # settled yet. wpjmc is one of comment/ceiling/untried/price/
                # unexplained; the frontend offers a manual-note fallback
                # when wpjmc is "unexplained" (nothing in the data explains it).
                "wpjmc": (str(row.get("wprp_miss_category"))
                          if row.get("wprp_miss_category") is not None
                          and str(row.get("wprp_miss_category")) not in ("", "nan") else None),
                "wpjmr": (str(row.get("wprp_miss_reason"))
                          if row.get("wprp_miss_reason") is not None
                          and str(row.get("wprp_miss_reason")) not in ("", "nan") else None),
                # Last 6 race runs (newest first) for the detail-panel form
                # table. Empty list if no history matched. We EXCLUDE any run
                # dated the same day as THIS race: TopRate's form feed includes
                # the current race once it resolves, which otherwise shows the
                # race as its own most-recent prior run ("0 days since last
                # run"). A horse races at most once per day (AU rules), so a
                # same-date run is always the current race, never a legitimate
                # earlier one. The full run stays in form history for
                # modelling; this filter is display-only.
                "formRuns": [
                    _fr for _fr in form_lookup.get(
                        str(row.get("horse", "")).strip().lower(), [])
                    if str(_fr.get("d", ""))[:10] != str(row.get("date", ""))[:10]
                ],
                # peakRun: a single rich record for the most recent
                # career-peak run when it falls OUTSIDE the visible runs.
                # None when the peak is already visible in formRuns.
                "peakRun": _peak_run_lookup.get(
                    str(row.get("horse", "")).strip().lower()),
                # formAll: compact full-history records for the detail-panel
                # comparison tables (WPR by tempo/settling/going/distance).
                # Exclude the current race (same date) so today's run does not
                # skew the "all races" averages - consistent with formRuns.
                "formAll": [
                    _fa_r for _fa_r in form_all_lookup.get(
                        str(row.get("horse", "")).strip().lower(), [])
                    if str(_fa_r.get("d", ""))[:10] != str(row.get("date", ""))[:10]
                ],
                # predicted settling band for THIS race (Leader/On-pace/
                # Midfield/Back) - lets the settling comparison table
                # highlight today's bucket. None if not estimable.
                "psBand": _settle_band_lookup.get(
                    str(row.get("run_id", ""))),
                # Same estimate, continuous 0-1 (0=leads, 1=settles last) -
                # see _settle_rel_lookup's own comment above. None if not
                # estimable (same gate as psBand).
                "psr": _settle_rel_lookup.get(
                    str(row.get("run_id", ""))),
                # Against-shape tendency over last 5 prior runs (min 3).
                # Display-only - the panel step-up flag derives a faint
                # "could stretch out" hint from this. NOT a predictive
                # claim. See FINDINGS_distance_suitability.md.
                "asTend": _tend_lookup.get(
                    str(row.get("horse", "")).strip().lower()),
            })

        # Get price drift fields (open/current) from price history if available
        # We attach to runner dicts so the race detail can show drift columns
        # (computed in JS from fxo and fxc)

        races_data.append({
            "race_id":   str(race_id),
            "date":      str(first.get("date", ""))[:10],
            "venue":     str(first.get("venue", "")) if first.get("venue") else "",
            "state":     str(first.get("state", "")) if first.get("state") else "",
            "race":      int(first.get("race") or 0),
            "race_name": str(first.get("race_name", "")) if first.get("race_name") else "",
            "distance":  int(pd.to_numeric(first.get("distance"), errors="coerce") if pd.notna(pd.to_numeric(first.get("distance"), errors="coerce")) else 0),
            "going":     str(first.get("going", "")) if first.get("going") and str(first.get("going")) != "nan" else "",
            "track_grading": str(first.get("track_grading", "")) if first.get("track_grading") else "",
            "rail":      str(first.get("rail_position", "")) if first.get("rail_position") and str(first.get("rail_position")) != "nan" else "",
            "prize":     int(first.get("prize_money") or 0),
            "start_time": str(_race_start_time) if _race_start_time else "",
            "rse":       None,
            "rsm":       None,
            "rsl":       None,
            # Automated pre-race tempo estimate (compute_race_speed() ->
            # race_speed_estimate.py's trained model) - a 0-1 pressure
            # score and Hot/Fast/Even/Slow label. LOW CONFIDENCE (held-out
            # correlation with actual raceShapeEarly ~+0.24) - the frontend
            # should treat this as context, not a firm prediction, and
            # prefer rse/rsm/rsl above once the race has actually run.
            "rs_score":  sf(first.get("rs_score")) if callable(sf) else None,
            "rs_label":  str(first.get("rs_label")) if first.get("rs_label") and str(first.get("rs_label")) != "nan" else None,
            "hfs":       int(bool(first.get("has_first_starter"))),  # has first starter
            "fs":        _active_field_size,
            "done":      int(_all_resulted or _all_interim_resulted),
            # True when "done" above was only satisfied via TAB's fast,
            # provisional feed (interim_resulted), not the authoritative
            # resulted pass - lets the dashboard show "Interim Result"
            # instead of a confirmed "Resulted" badge until update_results()
            # actually lands. Always 0 once _all_resulted is true, even if
            # interim_resulted also happens to be set (real trumps interim).
            "prov":      int(_all_interim_resulted and not _all_resulted),
            # Cumulative score formula path used for this race ('A' or 'B').
            # 'A' = jt_combo + tr (better, 44% rk-1 WR). 'B' = tr + wpr3 + late (33% rk-1 WR).
            # JS uses this to pick the right coverage curve in the Quaddie tab.
            "cs_path":   next(iter(cum_lookup.values()), {}).get("path", "B") if cum_lookup else "B",
            "runners":   runners,
        })

    # Sort races by date then start time then venue
    races_data.sort(key=lambda r: (r.get("date", ""), r.get("start_time", ""),
                                     r.get("venue", ""), r.get("race", 0)))

    # ── Build model picks structure: race_id -> model_key -> [picks] ─────────
    model_picks_by_race = {}
    if model_pick_rows:
        for r in model_pick_rows:
            rid = str(r.get("race_id"))
            mk  = r.get("model")
            if not rid or not mk:
                continue
            model_picks_by_race.setdefault(rid, {}).setdefault(mk, []).append({
                "run_id":   str(r.get("run_id")),
                "horse":    r.get("horse"),
                "tab":      r.get("tab_number"),
                "fxprice":  r.get("fixed_win_price"),
                # Post-race prices - null until results sync. Used to show
                # SP and Top Fluc on settled picks (Today tab shows result + TF).
                "starting_price_sp": r.get("starting_price_sp"),
                "price_top":         r.get("price_top"),
                "tr_rank":  r.get("tr_rank"),
                "mid_rank": r.get("mid_rank"),
                "late_rank": r.get("late_rank"),
                "total_rank": r.get("total_rank"),
                "wpr_rank":  r.get("wpr_rank"),
            })

    # ── Model meta removed (WPR-only refactor) ───────────────────────────────
    # MODEL_DEFS and the Edge/Volume model rule were removed. model_meta is
    # now empty and primary_key a placeholder; the HTML still accepts these
    # args and degrades gracefully (no picks). The dashboard rework (Stage 4)
    # removes the picks UI entirely.
    primary_key = "edge"
    model_meta = {}

    # ── Build price history map: run_id -> {o, oat, r, rat, n, s} ────────────
    # s: the full intraday snapshot series (fixed_win_price only, one point
    # per pipeline run - roughly every 5-30 min depending on schedule
    # reliability, see price_refresh.yml), as [minutes-since-open, price]
    # pairs so the dashboard can render a real movement trend rather than
    # just an open-vs-current comparison. No date filter (used to be
    # today-only) - PRICE_HISTORY_CSV itself is already capped to 7 days
    # by snapshot_prices(), which is bound enough; a runner captured by the
    # multi-day pre-fetch can now show its trend too, not just today's races.
    price_hist_map = {}
    if PRICE_HISTORY_CSV.exists():
        try:
            ph = pd.read_csv(PRICE_HISTORY_CSV, dtype={"run_id": str, "race_id": str})
            ph = ph[ph["fixed_win_price"].notna() & (ph["fixed_win_price"] > 0)].copy()
            ph["snapshot_time"] = pd.to_datetime(ph["snapshot_time"], errors="coerce", utc=True)
            ph = ph.dropna(subset=["snapshot_time"])
            for run_id, grp in ph.groupby("run_id"):
                grp = grp.sort_values("snapshot_time")
                first_p = grp.iloc[0]
                last_p  = grp.iloc[-1]
                t0 = first_p["snapshot_time"]
                # Collapse consecutive equal prices (a flat run between real
                # moves) down to just the endpoints - a sparkline only needs
                # the points where the line actually bends.
                series = []
                prev_price = None
                times = grp["snapshot_time"].tolist()
                prices = grp["fixed_win_price"].tolist()
                for i, (t, p) in enumerate(zip(times, prices)):
                    p = round(float(p), 2)
                    is_last = i == len(prices) - 1
                    if p != prev_price or is_last:
                        mins = int(round((t - t0).total_seconds() / 60))
                        series.append([mins, p])
                        prev_price = p
                price_hist_map[run_id] = {
                    "o":   float(first_p["fixed_win_price"]),
                    "oat": first_p["snapshot_time"].isoformat(),
                    "r":   float(last_p["fixed_win_price"]),
                    "rat": last_p["snapshot_time"].isoformat(),
                    "n":   int(len(grp)),
                    "s":   series,
                }
        except Exception as e:
            print(f"  Warning: could not load price history for HTML ({e})")

    # ── Render and write ─────────────────────────────────────────────────────
    _step("Rendering HTML template and writing file...")
    # run_iso MUST be timezone-aware. GitHub runners are UTC and
    # datetime.now() returns naive UTC; a naive ISO string (no offset) is
    # parsed by the browser's new Date() as LOCAL time, so a build "now" in
    # UTC reads as ~10h off in Melbourne (the UTC offset) - which made the
    # price-freshness dot show 10h-stale right after a fresh refresh. Emit
    # an explicit UTC offset so the browser computes age correctly.
    now_utc  = datetime.now(timezone.utc)
    now_iso  = now_utc.isoformat()
    run_date = now_utc.strftime("%d %b %Y %H:%M UTC")
    # render_html()'s `html` return value (the old toprate_html_v3.py-
    # templated page) is intentionally UNUSED from here on. The live
    # dashboard is now the frontend/ React+Vite build, committed at
    # toprate_live.html as a static artifact that doesn't change per data
    # refresh (it fetches toprate_data.json at runtime) - so this function,
    # called by both the daily run and the every-5-minutes price refresh,
    # must not keep overwriting it with the old generator's output. Only
    # rebuild toprate_live.html deliberately, by running `npm run build` in
    # frontend/ and committing the result. render_html() is still called
    # for its data_json half - that payload is the real per-run output.
    try:
        price_beta = float(json.load(open(Path(__file__).parent / "projection" / "models" / "config.json")).get("beta", 0.2))
    except Exception as e:
        print(f"  Could not read price beta ({e}); dashboard override "
              f"recompute will fall back to its own default.")
        price_beta = None

    html, data_json = render_html(
        races=races_data,
        model_picks_by_race=model_picks_by_race,
        model_meta=model_meta,
        price_hist=price_hist_map,
        run_date=run_date,
        run_iso=now_iso,
        model_pick_rows=model_pick_rows or [],
        primary_model_key=primary_key,
        price_beta=price_beta,
    )
    del html
    # Data payload the frontend fetches at boot instead of inlining it
    # (keeps the JS compile cost off the load path).
    OUTPUT_DATA = OUTPUT_HTML.parent / "toprate_data.json"
    _write_payload(json.loads(data_json), OUTPUT_HTML.parent)   # split: current + history (see _write_payload)
    del data_json
    _step("Data write complete.")

    n_total   = len(races_data)
    n_done    = sum(1 for r in races_data if r["done"] == 1)
    n_pending = n_total - n_done
    n_picks   = sum(len(picks_by_model.get(primary_key, []))
                    for picks_by_model in model_picks_by_race.values())
    print(f"Data refreshed -> {OUTPUT_DATA}")
    print(f"  {n_total} races ({n_done} resulted, {n_pending} pending)")
    print(f"  {n_picks} primary model picks across all races")


def serve(port=8080):
    """Start a local HTTP server so the HTML is accessible on iPhone over WiFi."""
    import http.server, socket, threading, webbrowser

    directory = str(OUTPUT_HTML.parent)

    class Handler(http.server.SimpleHTTPRequestHandler):
        def __init__(self, *args, **kwargs):
            super().__init__(*args, directory=directory, **kwargs)
        def log_message(self, fmt, *args):
            pass  # suppress per-request noise

    # Find local IP
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("8.8.8.8", 80))
        local_ip = s.getsockname()[0]
        s.close()
    except Exception:
        local_ip = "localhost"

    url = f"http://{local_ip}:{port}/toprate_live.html"

    server = http.server.HTTPServer(("", port), Handler)

    print(f"\n{'='*60}")
    print(f"  TopRate server running")
    print(f"{'='*60}")
    print(f"\n  On your iPhone (same WiFi):")
    print(f"  → {url}\n")
    print(f"  Tip: bookmark it in Safari for one-tap access.")
    print(f"\n  Press Ctrl+C to stop.\n")

    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nServer stopped.")


def publish():
    """
    Push updated toprate_live.html and CSVs to GitHub.

    Lets git speak directly to the terminal so credential prompts work
    (the previous version used capture_output=True which silently swallowed
    auth prompts and hung forever).

    Auto-resolves CSV conflicts by taking the local version (we just
    regenerated the data, so ours is canonical).
    """
    import subprocess as sp
    print("\n── Publishing to GitHub ──")
    script_dir = Path(__file__).parent

    def git(cmd, check=False):
        """Run git with output going straight to the terminal."""
        result = sp.run(["git"] + cmd, cwd=script_dir)
        return result.returncode == 0

    # Files we care about. Was missing wpr_form_history.csv.gz and
    # horse_history/ (found 2026-09-18 auditing for the same bug class that
    # broke tab_results.yml's own git add - see that workflow's comment):
    # a plain `python toprate_daily.py` full run (deploy.bat's step 5,
    # before this function's own --publish call) writes both, so a deploy
    # could leave real generated data sitting as an uncommitted, unstaged
    # working-tree change after this function returns - the same failure
    # mode (a later `git pull --rebase` refuses to run at all with
    # unstaged changes present) as the automated bug, just triggered
    # locally instead of every 5 minutes.
    files_to_push = []
    for f in ["toprate_live.html", "toprate_data.json", "toprate_data.json.gz",
              "toprate_history.json", "toprate_history.json.gz",
              "runners.csv", "runners_archive.csv.gz",
              "toprate_model_picks.csv", "toprate_price_history.csv",
              "wpr_form_history.csv.gz", "horse_history"]:
        if (script_dir / f).exists():
            files_to_push.append(f)

    # Stage changes
    git(["add"] + files_to_push)

    # Check if anything actually changed
    status = sp.run(["git", "diff", "--staged", "--quiet"], cwd=script_dir)
    if status.returncode == 0:
        print("  No changes to publish.")
        return

    # Commit
    msg = f"TopRate update {datetime.now():%Y-%m-%d %H:%M}"
    if not git(["commit", "-m", msg]):
        print("  Commit failed.")
        return

    # Try push - if rejected, pull --rebase, take ours on conflicts, retry
    print("  Pushing...")
    if git(["push"]):
        print(f"  Published: {msg}")
        return

    # Push rejected. Pull with rebase, auto-resolve conflicts (prefer ours).
    print("  Push rejected. Pulling latest and retrying...")

    # -X ours during rebase: when conflicts occur, prefer our version (we just generated)
    if not git(["pull", "--rebase", "-X", "ours"]):
        print("  Pull-rebase failed. Manual resolution needed:")
        print("    git status")
        print("    git checkout --theirs <conflicted-files>")
        print("    git add -A && git rebase --continue && git push")
        return

    if git(["push"]):
        print(f"  Published: {msg}")
    else:
        print("  Push still failing. Run manually:")
        print("    git push")


def main():
    parser = argparse.ArgumentParser(description="Daily runner database + dashboard payload (racing.com fields, TAB prices, own ratings)")
    parser.add_argument("--no-html",    action="store_true", help="Skip HTML rebuild")
    parser.add_argument("--date",       help="Merge the racing.com fields of one date (YYYY-MM-DD); default is every date from today on")
    parser.add_argument("--publish",    action="store_true", help="After rebuilding, push HTML to GitHub Pages")
    parser.add_argument("--rebuild-only", action="store_true",
                        help="Skip the field merge and the projection step and just rebuild the payload from the existing CSV, then "
                             "(with --publish) push it.")
    parser.add_argument("--serve",      action="store_true", help="After rebuilding, serve HTML on local network for iPhone access")
    parser.add_argument("--serve-only", action="store_true", help="Skip fetch/rebuild, just start the server (use existing HTML)")
    parser.add_argument("--port",       type=int, default=8080, help="Port for --serve (default 8080)")
    args = parser.parse_args()

    if args.serve_only:
        serve(args.port)
        return

    print(f"\n{'='*60}")
    print(f"Daily — {datetime.now():%Y-%m-%d %H:%M}")
    print(f"{'='*60}\n")

    runners_df = load_runners()
    n_existing = len(runners_df)
    n_races    = runners_df["race_id"].nunique() if n_existing else 0
    print(f"Runners DB: {n_existing:,} runners across {n_races:,} races ({RUNNERS_CSV})")

    if args.rebuild_only:
        print("── Rebuild-only: rebuilding the payload from the existing CSV ──")
        rebuild_html(runners_df, model_pick_rows=[])
        if args.publish:
            publish()
        print(f"\n{'='*60}")
        print("Done (rebuild-only).")
        if args.serve:
            serve(args.port)
        return

    _main_t0 = time.time()
    _last_t = [_main_t0]
    def _main_step(label):
        now = time.time()
        print(f"  [{now - _main_t0:6.1f}s total, +{now - _last_t[0]:5.1f}s this step] {label}", flush=True)
        _last_t[0] = now

    # Step 1: declared fields from racing.com (data/rc_fields/<date>.json, written by rc_fields_daily.yml). Results, prices and ratings
    # arrive from other jobs (rc_results_daily + own_ratings_daily, tab_results_poller); nothing here calls toprate.au any more.
    print("── Step 1: declared fields (toprate.au first, racing.com as backup) ──")
    import rc_field_rows
    import tr_field_rows
    if args.date:
        dates = [args.date]
    else:
        today = _melbourne_today()
        dates = sorted({f.stem for d_ in (rc_field_rows.DIR, tr_field_rows.DIR) for f in d_.glob("*.json") if f.stem >= today})
    for d in dates:
        # toprate.au first (data/tr_fields, written by toprate_race_fetch.py; ignored when older than MAX_AGE_HOURS), then racing.com:
        # in a race toprate.au owns, racing.com only fills gear / previous weight / win price and scratchings; elsewhere it builds the rows.
        try:
            runners_df, tr_stats = tr_field_rows.merge_tr_fields(runners_df, d)
        except Exception as e:                       # never lose the day to a TopRate problem: racing.com carries on
            print(f"  {d}: toprate.au merge failed ({type(e).__name__}: {e}), racing.com only")
            tr_stats = {"tr_rows": 0, "updated": 0, "added_rows": 0}
        runners_df, n_add, n_upd = rc_field_rows.merge_rc_fields(runners_df, d)
        try:       # after both merges: racing.com's pre-declaration nominations that toprate.au does not list are scratched (restorable)
            runners_df, fl = tr_field_rows.flag_unlisted(runners_df, d)
        except Exception as e:
            print(f"  {d}: flag_unlisted failed ({type(e).__name__}: {e}), nominations left as they are")
            fl = {"unlisted_scratched": 0, "duplicate_rows_scratched": 0}
        try:       # runner pages (stats splits, rating profiles, pedigree): upcoming, unresulted rows only
            runners_df, rp = tr_field_rows.merge_tr_runners(runners_df, d)
        except Exception as e:
            print(f"  {d}: runner-page merge failed ({type(e).__name__}: {e}), skipped")
            rp = {"records": 0, "filled": 0}
        print(f"  {d}: runner pages {rp['records']} records, {rp['filled']} rows filled")
        print(f"  {d}: toprate.au {tr_stats['tr_rows']} rows ({tr_stats['updated']} updated, {tr_stats['added_rows']} added); "
              f"racing.com {n_add} runners added, {n_upd} updated; nominations scratched: {fl['unlisted_scratched']} unlisted, "
              f"{fl['duplicate_rows_scratched']} duplicate")
    if "distance" in runners_df.columns:       # a source that wrote "1700m" must not reach the payload (14 Oct 2026, daily run #730 failed on it)
        runners_df["distance"] = pd.to_numeric(runners_df["distance"].astype(str).str.extract(r"(\d+)", expand=False), errors="coerce")
    try:       # TopRate numbers for races that have already run (data/tr_past, toprate_past_fetch.py): blanks only
        runners_df, id_map = tr_field_rows.remap_ids(runners_df)
        if id_map:
            print(f"  past races: {len(id_map)} runners re-keyed to TopRate ids, {tr_field_rows.remap_projection_log(id_map)} projection-log rows")
        runners_df, n_past = tr_field_rows.merge_tr_past(runners_df)
        print(f"  past races: {n_past} TopRate cells filled from data/tr_past")
    except Exception as e:
        print(f"  past-race TopRate merge failed ({type(e).__name__}: {e}), skipped")
    _main_step("Step 1: racing.com fields")
    print()

    # Step 2: the logged projections (projection/ pipeline) applied to the runner rows.
    print("── Step 2: projections ──")
    runners_df = compute_wpr_projection(runners_df, args.date)
    _main_step("Step 2: projections")
    print()

    # Step 3: race-speed (tempo) estimate. Additive and fail-safe.
    print("── Step 3: race-speed estimate ──")
    runners_df = compute_race_speed(runners_df, args.date)
    _main_step("Step 3: race-speed estimate")
    print()

    # Step 4: steward and video comments onto resulted runners from the form history, and the explanation of material misses.
    print("── Step 4: comments and miss explanations ──")
    runners_df = fill_comments_from_history(runners_df)
    runners_df = compute_miss_explanations(runners_df)
    _main_step("Step 4: comments and miss explanations")
    print()

    save_runners(runners_df)
    print(f"Saved -> {RUNNERS_CSV} ({len(runners_df):,} runners, {runners_df['race_id'].nunique():,} races)")
    _main_step("Saved runners")

    print("  Snapshotting prices for drift tracking…")
    snapshot_prices(runners_df)
    _main_step("Snapshotting prices")
    print()

    if not args.no_html:
        print("── Step 5: Rebuilding the payload ──")
        rebuild_html(runners_df, model_pick_rows=[])
        _main_step("Step 5: Rebuilding the payload")

    if args.publish:
        publish()
        _main_step("Publish")

    print(f"\n{'='*60}")
    print(f"Done. Total: {time.time() - _main_t0:.1f}s")

    if args.serve:
        serve(args.port)

if __name__ == "__main__":
    main()
