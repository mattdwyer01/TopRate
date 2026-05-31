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
  toprate_live.html      — rebuilt each run

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
import numpy as np
import argparse
import sys
import time
import math
import json
import os
import warnings
import urllib3
from datetime import datetime, timedelta, date, timezone
from pathlib import Path
from collections import defaultdict, Counter
from statistics import mean, stdev

urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)
VERIFY_SSL = False

# -----------------------------------------------------------------------
# CONFIG
# -----------------------------------------------------------------------
API_BASE  = "https://api.toprate.au"
ANON_KEY  = "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.ewogICJyb2xlIjogImFub24iLAogICJpc3MiOiAic3VwYWJhc2UiLAogICJpYXQiOiAxNjkxNjc2MDAwLAogICJleHAiOiAxODQ5NTI4ODAwCn0.MsNV6VIGz0f4K-wgKSwv1b2cnb76x7OcvrHm8HosHT4"
EMAIL     = os.environ.get("TOPRATE_EMAIL", "matt.dwyer.01@gmail.com")
PASSWORD  = os.environ.get("TOPRATE_PASSWORD", "P@ssword1996")

# Full Supabase session object from the last login() call. Populated by
# login(); read by the SvelteKit __data.json cookie-pair builder. None
# until login() has run.
_SESSION_OBJ = None

RUNNERS_CSV    = Path(__file__).parent / "toprate_runners.csv"
SELECTIONS_CSV = Path(__file__).parent / "toprate_selections.csv"
PRICE_HISTORY_CSV = Path(__file__).parent / "toprate_price_history.csv"
OUTPUT_HTML    = Path(__file__).parent / "toprate_live.html"
BT_RUNNERS_CSV = Path(__file__).parent / "toprate_runners_backtest.csv"

# WPR form-history dump. Each daily scrape's get_race_wpr_chart response
# carries, per runner, a `form` array of all that horse's past runs (wpr,
# distance, going, weight, sectional margins, settling positions, etc).
# build_wpr_history_lookup() consumes that array to compute summary signals
# but the raw per-run rows were previously discarded. We now persist them
# here, one row per (horse run), so a forward WPR-projection model can be
# trained later. This file is APPEND-ONLY and deduplicated on a stable key.
# It is not read by the daily pipeline or the dashboard - purely a data
# capture sink for offline modelling.
WPR_FORM_HISTORY_CSV = Path(__file__).parent / "wpr_form_history.csv"

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
    "run_id","tab_number","barrier","horse","jockey","trainer","runs_with_wpr",
    # Signal values (raw)
    "wpr_nett","wpr_rank","wpr_last1","wpr_avg_last3","wpr_trend","wpr_consistency",
    "wpr_peak_rank_1yr","wpr_dist","wpr_going",
    "avg_settled_pos","avg_800m_pos","avg_400m_pos","early_speed_score",
    "mid_speed_score","late_speed_score","total_speed_score",
    "toprate_rating","toprate_price","speed_rating",
    "fixed_win_price","jockey_win_pct_90d","trainer_win_pct_365d",
    # TopRate's own jockey and trainer rating numbers (separate from win % strike rates)
    "jockey_rating","trainer_rating",
    # Jockey/trainer combo - strongest single predictor in backtest. May be None
    # if live API doesn't expose it; the cumulative score formula falls back when
    # missing. Once populated, switch SCORE_WEIGHTS to use jt_combo_win_pct for
    # the Path A upgrade (44% rk-1 WR vs 33% with proxy formula).
    "jt_combo_win_pct","jt_combo_rides",
    # New signals supporting v3 core models (weight trajectory, distance specialty)
    "weight_trend","wins_at_dist","starts_at_dist","places_at_dist",
    "going_breakdown","form_string",
    # Per-runner weight carried today (was being collected but never saved)
    "weight_carried",
    # Pre-race market (starting_price_sp and price_top filled post-race)
    "starting_price_sp","price_top",
    # Result fields
    "finish_position","margin_finish","won","placed","resulted",
]

# -----------------------------------------------------------------------
# AUTH
# -----------------------------------------------------------------------
def login():
    resp = requests.post(
        f"{API_BASE}/auth/v1/token?grant_type=password",
        headers={"apikey": ANON_KEY, "Content-Type": "application/json"},
        json={"email": EMAIL, "password": PASSWORD}, verify=VERIFY_SSL)
    resp.raise_for_status()
    data = resp.json()
    token = data.get("access_token")
    if not token:
        raise ValueError(f"Login failed: {data}")
    # Stash the FULL session object (not just the token). The SvelteKit
    # __data.json endpoint - used by the rich form-history capture - needs
    # the sb-api-auth-token cookie pair, which is built from the whole
    # session object. login()'s return value is left as the bare token so
    # existing callers are untouched; the cookie builder reads this global.
    global _SESSION_OBJ
    _SESSION_OBJ = data
    print(f"Logged in | token expires {datetime.fromtimestamp(data.get('expires_at',0)):%H:%M:%S}")
    return token

def make_headers(jwt):
    return {"apikey": ANON_KEY, "Authorization": f"Bearer {jwt}",
            "Content-Type": "application/json"}

def rpc(jwt, name, params=None):
    resp = requests.post(f"{API_BASE}/rest/v1/rpc/{name}",
                         headers=make_headers(jwt), json=params or {},
                         verify=VERIFY_SSL)
    if resp.status_code == 401:
        raise PermissionError("JWT expired")
    resp.raise_for_status()
    return resp.json()

def api_calendar_upcoming(jwt):    return rpc(jwt, "get_calendar_upcoming")
def api_race_detail(jwt, rc_id):   return rpc(jwt, "get_race_detail",       {"rc_id": rc_id})
def api_race_wpr(jwt, rc_id):      return rpc(jwt, "get_race_wpr_chart",    {"rc_id": rc_id})
def api_race_stats(jwt, rc_id):    return rpc(jwt, "get_race_stats",        {"rc_id": rc_id})
def api_race_cache(jwt, rc_id):    return rpc(jwt, "get_user_cache_race",   {"rc_id": rc_id})
def api_race_results(jwt, rc_id):  return rpc(jwt, "get_race_results",      {"rc_id": rc_id})

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

def _fetch_one_race(jwt, rc_id):
    """Fetch all 4 API responses for a single race. Returns a dict, or an
    'error' entry if anything fails - the caller handles errors per-race
    exactly as the old sequential code did."""
    try:
        return {
            "rc_id":     rc_id,
            "detail":    api_race_detail(jwt, rc_id) or [],
            "cache":     api_race_cache(jwt, rc_id) or {},
            "wpr_chart": api_race_wpr(jwt, rc_id) or [],
            "stats":     api_race_stats(jwt, rc_id) or [],
        }
    except Exception as e:
        return {"rc_id": rc_id, "error": str(e)}

def prefetch_races(jwt, rc_ids, workers=DEFAULT_FETCH_WORKERS, label="races"):
    """Concurrently fetch API responses for many races.

    Returns {rc_id: {detail, cache, wpr_chart, stats}} (or {..., error}).
    workers=1 runs fully sequential (safety fallback). Order of the input
    list is irrelevant - the caller indexes the result dict by rc_id and
    processes in whatever order it wants."""
    results = {}
    rc_ids = list(rc_ids)
    if not rc_ids:
        return results
    if workers <= 1:
        for rc_id in rc_ids:
            results[rc_id] = _fetch_one_race(jwt, rc_id)
        return results
    from concurrent.futures import ThreadPoolExecutor, as_completed
    done = 0
    total = len(rc_ids)
    with ThreadPoolExecutor(max_workers=workers) as pool:
        futures = {pool.submit(_fetch_one_race, jwt, rid): rid for rid in rc_ids}
        for fut in as_completed(futures):
            res = fut.result()
            results[res["rc_id"]] = res
            done += 1
            if done % 20 == 0 or done == total:
                print(f"  prefetched {done}/{total} {label}")
    return results


# -----------------------------------------------------------------------
# DATA BUILDERS
# -----------------------------------------------------------------------
def safe(v, default=None):
    try:
        f = float(v)
        return default if math.isnan(f) else f
    except: return default

def build_wpr_lookup(cache):
    lookup = {}
    for entry in cache.get("runAdjustments", []):
        rid      = entry.get("runId")
        defaults = entry.get("defaults", {})
        adjs     = entry.get("adjustments", {})
        base     = defaults.get("wprBase")
        adj      = adjs.get("wprAdjustment") or defaults.get("wprAdjustment") or 0
        nett     = round(base + adj, 1) if base is not None else None
        lookup[rid] = {"wpr_nett": nett}
    ranked = sorted([(r, v) for r, v in lookup.items() if v["wpr_nett"] is not None],
                    key=lambda x: x[1]["wpr_nett"], reverse=True)
    for rank, (rid, _) in enumerate(ranked, 1):
        lookup[rid]["wpr_rank"] = rank
    return lookup

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

def collect_wpr_form_history(wpr_chart, detail, scrape_date):
    """Append every runner's raw form-history rows to the module accumulator.

    One output row per (runner past-run). `run_id` ties the row back to the
    runner in the current race card; `scrape_date` records when it was
    captured. The full form array is dumped UNFILTERED - no race_date cutoff -
    because for offline modelling we want every run, and the model code
    applies its own point-in-time discipline.

    Horse identity: the wpr_chart runner objects carry only runId + form.
    Horse name AND horseId are resolved from the `detail` list (which maps
    runId -> both). horseId is the stable dedup key - far more reliable than
    the name (handles horses that share or change names).
    """
    # Build runId -> (horse name, horseId) from the race detail
    name_by_rid = {}
    hid_by_rid  = {}
    for d in (detail or []):
        rid = d.get("runId")
        if rid is not None:
            name_by_rid[rid] = d.get("horse")
            hid_by_rid[rid]  = d.get("horseId")

    # (one-time WPR form-history structural diagnostic removed - it had
    #  served its purpose and was cluttering every run)

    for runner in (wpr_chart or []):
        rid   = runner.get("runId")
        hname = name_by_rid.get(rid)
        hid   = hid_by_rid.get(rid)
        # Record this runner-page id for the rich __data.json capture pass
        # (Step 2b). One id per runner; the rich fetch runs once after all
        # races are collected, not inline here.
        if rid is not None:
            _WPR_RICH_RUNIDS.add(rid)
        for f in (runner.get("form") or []):
            row = {
                "run_id":      rid,
                "horse_id":    hid,
                "horse":       hname,
                "scrape_date": scrape_date,
            }
            for k in _WPR_FORM_FIELDS:
                row[k] = f.get(k)
            _WPR_FORM_ROWS.append(row)

def _enrich_form_history_rich(new_df):
    """Fetch the rich per-runner __data.json for today's runners and merge
    its fields (field_size, 13 sectionals, class, gear, comments, jockey,
    trainer, campaign flags) into new_df, joined on (horse_id, date).

    Full fetch: every run_id collected today. Stage 2 measured ~0.28s per
    call, so a ~400-runner day costs ~2 minutes - acceptable serially.

    Fail-safe: on any failure (import, fetch, parse) the function returns
    new_df unchanged. The rich capture must never break the daily run -
    same discipline as compute_wpr_projection.
    """
    if not _WPR_RICH_RUNIDS:
        return new_df
    try:
        import toprate_json_capture as cap
    except Exception as e:
        print(f"  Rich capture skipped: cannot import toprate_json_capture ({e})")
        return new_df

    run_ids = sorted(_WPR_RICH_RUNIDS)
    print(f"  Rich __data.json capture: {len(run_ids)} runner pages ...")

    # (horse_id, date_str) -> dict of rich fields
    rich = {}
    n_ok = n_empty = n_fail = 0
    t0 = time.time()
    for i, rid in enumerate(run_ids, 1):
        if i % 100 == 0:
            print(f"    ... {i}/{len(run_ids)} ({time.time()-t0:.0f}s)")
        try:
            horse_id, runs = cap.fetch_runner(rid)
        except Exception:
            horse_id, runs = None, []
        if horse_id == "EMPTY":
            n_empty += 1
            continue
        if horse_id is None:
            n_fail += 1
            continue
        n_ok += 1
        for run in runs:
            # date strings: __data.json gives ISO dates; the form-history
            # date column is also ISO. Slice to 10 chars on both sides of
            # the join so a time component never breaks the match.
            d = str(run.get("date", ""))[:10]
            if d:
                rich[(str(horse_id), d)] = run.get("fields", {})

    if not rich:
        print(f"  Rich capture: no data merged "
              f"(ok {n_ok}, empty {n_empty}, fail {n_fail})")
        return new_df

    # ensure every rich column exists on new_df
    for col in cap.ALL_COLS:
        if col not in new_df.columns:
            new_df[col] = None

    # fill rich columns row by row, matched on (horse_id, date)
    filled = 0
    for idx in new_df.index:
        hid = str(new_df.at[idx, "horse_id"])
        d = str(new_df.at[idx, "date"])[:10]
        fields = rich.get((hid, d))
        if not fields:
            continue
        for col in cap.ALL_COLS:
            v = fields.get(col)
            if v is not None:
                new_df.at[idx, col] = v
        filled += 1

    print(f"  Rich capture: {filled:,}/{len(new_df):,} rows enriched "
          f"(pages ok {n_ok}, empty {n_empty}, fail {n_fail}, "
          f"{time.time()-t0:.0f}s)")
    return new_df


def flush_wpr_form_history():
    """Write accumulated form rows to WPR_FORM_HISTORY_CSV (append + dedup).

    Dedup key is (dedup_key, formNumber, date) where dedup_key is horse_id
    when available, else the horse name. A horse's run is uniquely identified
    by which horse it is, which run number in its career it was, and the date.
    Re-scraping the same horse on later days refreshes the same rows rather
    than duplicating them. keep='last' so the most recent capture wins (a past
    run's wpr can be revised by TopRate up to ~5 days post-race). Rows with
    neither a horse_id nor a name are dropped - without a stable identity they
    cannot be safely deduped or used for modelling."""
    if not _WPR_FORM_ROWS:
        print("WPR form history: nothing to write")
        return
    new_df = pd.DataFrame(_WPR_FORM_ROWS)
    before = len(new_df)
    # Keep rows that have at least one form of identity
    has_id   = new_df["horse_id"].notna() & (new_df["horse_id"].astype(str) != "")
    has_name = new_df["horse"].notna() & (new_df["horse"].astype(str) != "")
    new_df = new_df[has_id | has_name]
    dropped = before - len(new_df)
    if dropped:
        print(f"WPR form history: dropped {dropped:,} rows with no horse identity")
    if new_df.empty:
        print("WPR form history: no identifiable rows - nothing written")
        return

    # ── Rich __data.json capture (Step 2b) ──────────────────────────────
    # Enrich new_df with field_size, sectionals, class, gear, comments etc.
    # from the per-runner __data.json endpoint. Joined on (horse_id, date),
    # which is unique (a horse races at most once a day). Fail-safe: any
    # error leaves new_df with thin rows and the daily run still completes.
    new_df = _enrich_form_history_rich(new_df)

    if WPR_FORM_HISTORY_CSV.exists():
        try:
            old = pd.read_csv(WPR_FORM_HISTORY_CSV,
                              dtype={"run_id": str, "horse_id": str})
            combined = pd.concat([old, new_df], ignore_index=True)
        except Exception as e:
            print(f"WPR form history: could not read existing file ({e}); starting fresh")
            combined = new_df
    else:
        combined = new_df
    # dedup_key: horse_id where present, else fall back to the name
    combined["_dedup"] = combined["horse_id"].astype(str)
    blank = combined["_dedup"].isin(["", "nan", "None"])
    combined.loc[blank, "_dedup"] = combined.loc[blank, "horse"].astype(str)
    key = ["_dedup", "formNumber", "date"]
    # Prefer ENRICHED rows when deduping. The rich __data.json enrichment
    # fills the per-horse sectionals (sect_i_*) and class; a plain re-scrape
    # of the same run produces a THIN row with those columns NaN. With a
    # naive keep="last", a later thin re-scrape would overwrite a previously
    # enriched row and silently wipe the sectionals (the bug that blanked
    # horse sectionals in the detail panel). Fix: sort so rows that HAVE
    # sectional data sort AFTER thin rows within each dup group, so
    # keep="last" keeps the enriched one. Ties (both enriched or both thin)
    # fall back to scrape recency.
    if "sect_i_early" in combined.columns:
        _has_sect = combined["sect_i_early"].notna().astype(int)
    else:
        _has_sect = 0
    combined["_enriched"] = _has_sect
    # _enriched is the PRIMARY sort key so enriched rows always sort AFTER
    # thin rows (and win keep="last"), regardless of scrape date. scrape_date
    # is only a tiebreaker among rows with the SAME enrichment status (e.g.
    # two enriched scrapes - keep the newer). Getting this order wrong (date
    # first) lets a later thin re-scrape beat an older enriched row, which is
    # exactly the bug being fixed.
    _sort_cols = ["_enriched"]
    if "scrape_date" in combined.columns:
        _sort_cols = ["_enriched", "scrape_date"]
    # stable sort ascending: thin (0) before enriched (1); within each,
    # older scrape before newer. keep="last" then keeps enriched-and-newest.
    combined = combined.sort_values(_sort_cols, kind="stable")
    combined = combined.drop_duplicates(subset=key, keep="last").reset_index(drop=True)
    combined = combined.drop(columns=["_dedup", "_enriched"])
    combined.to_csv(WPR_FORM_HISTORY_CSV, index=False)
    print(f"WPR form history: {len(new_df):,} rows captured, "
          f"{len(combined):,} total unique runs -> {WPR_FORM_HISTORY_CSV.name}")


def build_wpr_history_lookup(wpr_chart, race_date=None, race_distance=None, race_going=None):
    lookup = {}
    for runner in (wpr_chart or []):
        rid      = runner.get("runId")
        all_form = [f for f in runner.get("form", [])
                    if f.get("wpr") and not f.get("isBarrierTrial")]
        form     = [f for f in all_form
                    if not race_date or f.get("date", "9999") < race_date]
        wprs     = [f["wpr"] for f in form]
        trend    = None
        if len(wprs) >= 3:   trend = round(wprs[0] - mean(wprs[1:3]), 1)
        elif len(wprs) == 2: trend = round(wprs[0] - wprs[1], 1)
        consistency = round(stdev(wprs[:5]), 1) if len(wprs) >= 3 else None
        # NOTE: peak1Rank from the API is point-in-time-of-scrape, not point-in-time-
        # of-race, so it leaks future results into backtests. We instead use
        # peak1FormNumber to look up the peak run in the date-filtered `form` list,
        # and read its positionFinish. If the peak run is not in our filtered form
        # list, the peak occurred on or after race_date and is correctly excluded.
        # For LIVE picks (no race_date filter applied) this still works correctly
        # because no future races exist yet.
        peak1_rank  = None
        for p in runner.get("peak", []):
            d = p.get("domain", {})
            if (d.get("period") == "1 year" and d.get("jumpsOrFlats") == "flatsOnly"
                    and d.get("distances") == "all"):
                peak_fn = p.get("peak1FormNumber")
                if peak_fn is not None:
                    peak_entry = next((f for f in form if f.get("formNumber") == peak_fn), None)
                    if peak_entry is not None:
                        peak1_rank = peak_entry.get("positionFinish")
                break

        # WPR at distance (within ±10% of today's race distance)
        wpr_dist = None
        wpr_dist_n = 0
        dist_starts = 0
        dist_wins = 0
        dist_places = 0
        if race_distance:
            lo, hi = race_distance * 0.9, race_distance * 1.1
            dist_form = [f for f in form
                         if f.get("distance") and lo <= f["distance"] <= hi]
            dist_runs = [f["wpr"] for f in dist_form]
            wpr_dist_n = len(dist_runs)
            wpr_dist = round(mean(dist_runs), 1) if dist_runs else None
            dist_starts = len(dist_form)
            dist_wins   = sum(1 for f in dist_form if f.get("positionFinish") == 1)
            dist_places = sum(1 for f in dist_form
                              if f.get("positionFinish") in (1, 2, 3))

        # WPR on going (matching today's going condition)
        wpr_going = None
        if race_going:
            going_runs = [f["wpr"] for f in form
                          if f.get("going") and f["going"].lower() == race_going.lower()]
            wpr_going = round(mean(going_runs), 1) if going_runs else None

        # Going-category breakdown: collapse Firm/Good/Soft/Heavy
        # Aggregate starts/wins/places per category from full form history.
        def _going_category(g):
            if not g:
                return None
            g = g.lower()
            if g.startswith("firm"): return "firm"
            if g.startswith("good"): return "good"
            if g.startswith("soft"): return "soft"
            if g.startswith("heavy"): return "heavy"
            if g.startswith("synth"): return "synth"
            return None
        going_breakdown = {}
        for f in form:
            cat = _going_category(f.get("going"))
            if not cat:
                continue
            if cat not in going_breakdown:
                going_breakdown[cat] = {"starts": 0, "wins": 0, "places": 0}
            going_breakdown[cat]["starts"] += 1
            pos = f.get("positionFinish")
            if pos == 1:
                going_breakdown[cat]["wins"] += 1
            if pos in (1, 2, 3):
                going_breakdown[cat]["places"] += 1

        # Form string: last 4 finishing positions, most recent first
        # Format: "3-1-7-2"  ('x' for unplaced/scratched, '?' for unknown)
        form_pos = []
        for f in form[:4]:
            pos = f.get("positionFinish")
            if pos is None:
                form_pos.append("?")
            elif pos == 0 or pos > 9:
                form_pos.append("x")
            else:
                form_pos.append(str(pos))
        form_string = "-".join(form_pos) if form_pos else None

        # ── Historical settling & early speed from actual race data ──────────
        # Use last 5 runs with valid position data
        pos_form  = [f for f in form[:5] if f.get("positionSettled") is not None]
        p800_form = [f for f in form[:5] if f.get("position800m") is not None]
        p400_form = [f for f in form[:5] if f.get("position400m") is not None]

        # Average settled position (lower = closer to lead)
        avg_settled = round(mean([f["positionSettled"] for f in pos_form]), 1) if pos_form else None

        # Average 800m position — position at halfway, genuine settling/pace indicator
        avg_800m = round(mean([f["position800m"] for f in p800_form]), 1) if p800_form else None

        # Average 400m position — position in the straight, momentum indicator
        avg_400m = round(mean([f["position400m"] for f in p400_form]), 1) if p400_form else None

        # ── Blended margin + race shape sectional scores ─────────────────────
        # Margins measure what THIS horse did; raceShape gives tempo context.
        # All scores: higher = better (more speed/improvement in that phase).
        #
        # Normalisation:
        #   margin_gain  = margin at start of phase - margin at end (positive = gaining)
        #   shape_bonus  = race shape for that phase (negative shape = fast race,
        #                  which makes gaining margins harder, so we ADD the negative)
        #   blended      = margin_gain - shape_score  (subtract shape to reward
        #                  gains made in fast-tempo sections)

        blend_form = [f for f in form[:5]
                      if f.get("margin800m") is not None
                      and f.get("marginFinish") is not None]

        early_scores, mid_scores, late_scores, total_scores = [], [], [], []

        for f in blend_form:
            m800  = f.get("margin800m",  0)
            m600  = f.get("margin600m",  0)
            m400  = f.get("margin400m",  0)
            m200  = f.get("margin200m",  0)
            mfin  = f.get("marginFinish", 0)
            se    = f.get("raceShapeEarly", 0)
            sm    = f.get("raceShapeMid",   0)
            sl    = f.get("raceShapeLate",  0)

            # Early: how close to the lead at 800m, adjusted for race tempo
            # Lower margin800m = closer to lead = better early position
            # Fast early race (negative se) = harder to be close, so reward it
            early = round((-m800) - se, 2)           # negate margin so higher=closer

            # Mid: margin gain from 800m to 400m, adjusted for mid tempo
            # Positive = gaining on leader through middle section
            mid   = round((m800 - m400) - sm, 2)

            # Late: margin gain from 400m to finish, adjusted for late tempo
            # Positive = finishing strongly / running on
            late  = round((m400 - mfin) - sl, 2)

            # Total: overall improvement from 800m to finish vs race tempo
            total = round((m800 - mfin) - (se + sm + sl), 2)

            early_scores.append(early)
            mid_scores.append(mid)
            late_scores.append(late)
            total_scores.append(total)

        early_speed_score = round(mean(early_scores), 2) if early_scores else None
        mid_speed_score   = round(mean(mid_scores),   2) if mid_scores   else None
        late_speed_score  = round(mean(late_scores),  2) if late_scores  else None
        total_speed_score = round(mean(total_scores), 2) if total_scores else None

        # ── Weight trajectory (today's weight vs avg of last 5 runs) ─────────
        # Trainers reveal confidence via weight - heavier today than recent
        # average is often a fitness/improvement signal
        weights = [f.get("weightCarried") for f in form[:5]
                   if f.get("weightCarried") is not None]
        weight_trend = (round(weights[0] - mean(weights[1:]), 1)
                        if len(weights) >= 3 else None)

        # ── Distance specialty (count of wins at this distance ±10%) ─────────
        if race_distance:
            lo_d, hi_d = race_distance * 0.9, race_distance * 1.1
            dist_runs_full = [f for f in form
                              if f.get("distance") and lo_d <= f["distance"] <= hi_d]
            wins_at_dist = sum(1 for f in dist_runs_full
                               if f.get("positionFinish") == 1)
            starts_at_dist = len(dist_runs_full)
        else:
            wins_at_dist = None
            starts_at_dist = None

        lookup[rid] = {
            "wpr_last1":         wprs[0] if wprs else None,
            "wpr_avg_last3":     round(mean(wprs[:3]), 1) if wprs else None,
            "wpr_trend":         trend,
            "wpr_consistency":   consistency,
            "wpr_peak_rank_1yr": peak1_rank,
            "runs_with_wpr":     len(wprs),
            "wpr_dist":          wpr_dist,
            "wpr_dist_n":        wpr_dist_n,
            "wpr_going":         wpr_going,
            # Settling & position signals
            "avg_settled_pos":   avg_settled,
            "avg_800m_pos":      avg_800m,
            "avg_400m_pos":      avg_400m,
            # Blended sectional speed signals (margin gain adjusted for race tempo)
            "early_speed_score": early_speed_score,
            "mid_speed_score":   mid_speed_score,
            "late_speed_score":  late_speed_score,
            "total_speed_score": total_speed_score,
            # v3 model signals
            "weight_trend":      weight_trend,
            "wins_at_dist":      wins_at_dist,
            "starts_at_dist":    starts_at_dist,
            # Distance places (in addition to wins/starts already saved above)
            "places_at_dist":    dist_places,
            # Going breakdown (full career, by category): {firm: {starts, wins, places}, good: {...}}
            "going_breakdown":   going_breakdown,
            # Last 4 finishes as string: "3-1-7-2"
            "form_string":       form_string,
        }
    return lookup

def build_stats_lookup(race_stats):
    lookup = {}
    _logged_filters = set()  # track unique filter combos seen, for one-time diagnostic
    for runner in (race_stats or []):
        rid = runner.get("runId")

        def pick(lst, region, price, days, jumps):
            # Case-insensitive match — TopRate sometimes returns "All" vs "all"
            for s in (lst or []):
                d = s.get("domain", {})
                d_region = (d.get("region") or "").lower()
                d_price  = (d.get("startingPrice") or "").lower() if isinstance(d.get("startingPrice"), str) else d.get("startingPrice")
                d_jumps  = (d.get("jumpsOrFlats") or "").lower() if isinstance(d.get("jumpsOrFlats"), str) else d.get("jumpsOrFlats")
                if (d_region == region.lower() and d_price == price.lower()
                        and d.get("periodDays") == days and d_jumps == jumps.lower()):
                    return s
            return {}
        j90  = pick(runner.get("jockeyStats",  []), "all", "all",  90, "flatsOnly")
        t365 = pick(runner.get("trainerStats", []), "all", "all", 365, "flatsOnly")
        # Diagnostic: if no match found, log available domains once for debugging
        if not j90 and runner.get("jockeyStats") and "jockey_no_match" not in _logged_filters:
            _logged_filters.add("jockey_no_match")
            available = [s.get("domain", {}) for s in runner.get("jockeyStats", [])[:3]]
            print(f"  WARNING: no jockey stat match for filter (region=all, price=all, days=90, jumps=flatsOnly). "
                  f"First few available domains: {available}")

        # Try to extract jockey/trainer combo win% (the strongest single predictor in
        # the backtest at 44% rank-1 WR). Try several plausible field locations.
        # Path A: a dedicated array similar to jockeyStats/trainerStats
        jt_combo_win_pct = None
        jt_combo_rides   = None
        for arr_key in ("jockeyTrainerStats", "jockeyTrainerComboStats",
                        "comboStats", "jtComboStats", "jtStats"):
            arr = runner.get(arr_key)
            if isinstance(arr, list) and arr:
                # Try matching same domain filter we use for other stats
                jt_match = pick(arr, "all", "all", 365, "flatsOnly")
                if not jt_match:
                    # fallback: just take the first entry
                    jt_match = arr[0] if isinstance(arr[0], dict) else {}
                jt_combo_win_pct = jt_match.get("winPercent")
                jt_combo_rides   = jt_match.get("rides") or jt_match.get("starts")
                break

        # Path B: scalar fields on the runner object directly
        if jt_combo_win_pct is None:
            for k in ("jtComboWinPct", "jt_combo_win_pct", "comboWinPct",
                      "jockeyTrainerWinPct"):
                if runner.get(k) is not None:
                    jt_combo_win_pct = runner.get(k)
                    break

        lookup[rid] = {
            "jockey_win_pct_90d":   j90.get("winPercent"),
            "trainer_win_pct_365d": t365.get("winPercent"),
            # jockeyRating/trainerRating sit at the runner level inside get_race_stats[]
            # (NOT inside the filtered stats domain entries which only have winPercent etc)
            "jockey_rating":   runner.get("jockeyRating"),
            "trainer_rating":  runner.get("trainerRating"),
            # Jockey/trainer combo - new for v3 score upgrade. May be None if API
            # doesn't expose this; the score formula falls back to other signals.
            "jt_combo_win_pct": jt_combo_win_pct,
            "jt_combo_rides":   jt_combo_rides,
        }
    return lookup

# -----------------------------------------------------------------------
# SIGNAL SCORING — compute per-race vote counts across all runners
# -----------------------------------------------------------------------
def compute_votes(runners_df):
    """
    Given a DataFrame of runners for one race, compute signal vote counts.
    Returns dict: {run_id: vote_count}, and total signals available.
    """
    sc    = Counter()
    total = 0
    for sig in SIGNALS_HIGHER:
        col = "fixed_win_price" if sig == "starting_price_sp" else sig
        if col not in runners_df.columns or not runners_df[col].notna().any():
            continue
        best = runners_df[runners_df[col].notna()][col].idxmax()
        sc[runners_df.loc[best, "run_id"]] += 1
        total += 1
    for sig in SIGNALS_LOWER:
        col = "fixed_win_price" if sig == "starting_price_sp" else sig
        if col == "price_top":   # not available pre-race
            continue
        if col not in runners_df.columns or not runners_df[col].notna().any():
            continue
        best = runners_df[runners_df[col].notna()][col].idxmin()
        sc[runners_df.loc[best, "run_id"]] += 1
        total += 1
    return sc, total


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

    done = 0
    for race_id, race in today.groupby("race_id"):
        try:
            race_date = pd.to_datetime(race["date"].iloc[0], errors="coerce")
            res = rse.estimate_race_speed(race, race_date, fh)
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


def compute_wpr_projection(runners_df, target_date_str=None):
    """Add wprp_proj, wprp_conf, wprp_price, wprp_rank, wprp_peak, wprp_desc
    columns to the runners DataFrame.

    Only processes races for target_date_str (the date just fetched). The
    runners DataFrame is the whole accumulated database - projecting all of
    it every run is both wasteful and grows unbounded, so the work is scoped
    to today's races. Past runners keep whatever wprp_* values they already
    had.

    Additive and fail-safe: returns the DataFrame unchanged on any failure -
    the projection must never break the daily pipeline.
    """
    import time as _time
    try:
        import wpr_projection as wpr
    except Exception as e:
        print(f"  WPR projection skipped: cannot import wpr_projection ({e})")
        return runners_df

    if not WPR_FORM_HISTORY_CSV.exists():
        print(f"  WPR projection skipped: {WPR_FORM_HISTORY_CSV.name} not found")
        return runners_df

    # ensure the target columns exist even if projection fails partway
    for col in ["wprp_proj", "wprp_conf", "wprp_price", "wprp_rank",
                "wprp_peak", "wprp_desc", "wprp_proj_alt", "wprp_conf_alt"]:
        if col not in runners_df.columns:
            runners_df[col] = None

    # scope to today's races only - never project the whole history
    if target_date_str is None:
        target_date_str = date.today().strftime("%Y-%m-%d")
    day_mask = runners_df["date"].astype(str).str[:10] == target_date_str
    today = runners_df[day_mask]
    if len(today) == 0:
        print(f"  WPR projection: no runners for {target_date_str}, skipping")
        return runners_df

    # form history - read once, then keep only the horses running today
    try:
        today_horses = set(today["horse"].astype(str).str.strip().str.lower())
        fh = pd.read_csv(WPR_FORM_HISTORY_CSV,
                         dtype={"horse": str, "horse_id": str})
        fh["horse_lc"] = fh["horse"].astype(str).str.strip().str.lower()
        fh = fh[fh["horse_lc"].isin(today_horses)]   # only today's horses
        fh["date"] = pd.to_datetime(fh["date"], errors="coerce")
        fh["wpr"] = pd.to_numeric(fh["wpr"], errors="coerce")
        fh = fh.dropna(subset=["date", "wpr"])
        if "isBarrierTrial" in fh.columns:
            fh = fh[fh["isBarrierTrial"].fillna(0).astype(int) == 0]
        fh = fh.sort_values(["horse_lc", "date"])
        form_by_horse = dict(tuple(fh.groupby("horse_lc")))
    except Exception as e:
        print(f"  WPR projection skipped: could not read form history ({e})")
        return runners_df

    projected = 0
    fallback = 0
    races = 0
    race_groups = list(today.groupby("race_id"))
    n_races = len(race_groups)
    t0 = _time.time()
    for gi, (race_id, race) in enumerate(race_groups):
        # progress line every 20 races so the step is never silent
        if gi > 0 and gi % 20 == 0:
            print(f"    ... {gi}/{n_races} races ({_time.time()-t0:.0f}s)")
        try:
            race_date = pd.to_datetime(race["date"].iloc[0], errors="coerce")
        except Exception:
            continue
        if pd.isna(race_date):
            continue

        runners = []
        runners_alt = []   # same field, going flipped wet<->dry
        idx_order = []
        for idx, r in race.iterrows():
            horse_lc = str(r.get("horse", "")).strip().lower()
            hist = form_by_horse.get(horse_lc)
            prior = hist[hist["date"] < race_date] if hist is not None else None
            going = r.get("going") or "Good 4"
            # the model reads going only as wet vs dry (today_wet). Flip it
            # so the dashboard can show a what-if projection for the other
            # going state. Good/Firm = dry, Soft/Heavy = wet.
            gl = str(going).lower()
            is_wet = gl.startswith("soft") or gl.startswith("heavy")
            going_alt = "Good 4" if is_wet else "Heavy 9"
            base = {
                "prior_runs": prior,
                "cur_distance": r.get("distance") or 1400,
                "cur_track": r.get("venue") or "",
                "cur_track_grading": r.get("track_grading"),
                # cur_race_class drives class_move / peak_at_class;
                # cur_field_size drives the field_size feature. Both
                # degrade gracefully to neutral in project_race if None.
                "cur_race_class": r.get("race_class"),
                "cur_field_size": len(race),
            }
            runners.append(dict(base, cur_going=going))
            runners_alt.append(dict(base, cur_going=going_alt))
            idx_order.append(idx)

        try:
            results = wpr.project_race(runners, race_date=race_date)
        except Exception as e:
            print(f"  WPR projection error on race {race_id}: {e}")
            continue
        # alternate-going projection - non-fatal if it fails
        try:
            results_alt = wpr.project_race(runners_alt, race_date=race_date)
        except Exception:
            results_alt = [None] * len(idx_order)
        races += 1

        for k, (idx, res) in enumerate(zip(idx_order, results)):
            runners_df.at[idx, "wprp_peak"] = res.get("peak_wpr")
            runners_df.at[idx, "wprp_desc"] = res.get("description")
            if res.get("has_projection"):
                runners_df.at[idx, "wprp_proj"] = res.get("projected_wpr")
                runners_df.at[idx, "wprp_conf"] = res.get("confidence")
                runners_df.at[idx, "wprp_price"] = res.get("wpr_price")
                runners_df.at[idx, "wprp_rank"] = res.get("wpr_rank")
                # alternate-going projection (wet if today dry, dry if wet)
                ra = results_alt[k]
                if ra and ra.get("has_projection"):
                    runners_df.at[idx, "wprp_proj_alt"] = ra.get("projected_wpr")
                    runners_df.at[idx, "wprp_conf_alt"] = ra.get("confidence")
                projected += 1
            else:
                fallback += 1

    print(f"  WPR projection: {projected} runners projected, "
          f"{fallback} fallback (too few runs), across {races} races "
          f"in {_time.time()-t0:.0f}s")
    return runners_df


def compute_wpr_actual(runners_df):
    """Add wpr_actual and wpr_actual_rank to RESULTED runners.

    The projected WPR (wprp_proj) is a pre-race figure. Once a race is
    run, the runner earns an ACTUAL WPR - and that lands in
    wpr_form_history.csv when the horse is next scraped (the rich form
    capture writes the now-past run with its wpr). This step joins that
    actual WPR back onto resulted runners so the dashboard can show
    predicted vs actual, and how far the projection and ranking missed.

    Join key is (horse, date) - the same key the project uses elsewhere
    (a horse races at most once per day, so it is unique).

    TIMING - read this. The actual WPR is NOT available on results day.
    It appears 1+ days later, once the horse is re-scraped, and TopRate
    revises a run's WPR for up to ~5 days post-race. So wpr_actual fills
    in PROGRESSIVELY over the days after a race - a freshly-resulted race
    will have wpr_actual blank until the form history catches up. That is
    expected, not a fault.

    Additive and fail-safe: returns the DataFrame unchanged on any error.
    """
    for col in ["wpr_actual", "wpr_actual_rank"]:
        if col not in runners_df.columns:
            runners_df[col] = None

    if not WPR_FORM_HISTORY_CSV.exists():
        print(f"  WPR actual skipped: {WPR_FORM_HISTORY_CSV.name} not found")
        return runners_df

    # only resulted runners can have an actual WPR
    resulted_mask = runners_df.get("resulted") == 1
    if resulted_mask.sum() == 0:
        print("  WPR actual: no resulted runners")
        return runners_df

    try:
        fh = pd.read_csv(WPR_FORM_HISTORY_CSV,
                         dtype={"horse": str, "horse_id": str},
                         low_memory=False)
        fh["horse_lc"] = fh["horse"].astype(str).str.strip().str.lower()
        fh["date_s"] = fh["date"].astype(str).str[:10]
        fh["wpr"] = pd.to_numeric(fh["wpr"], errors="coerce")
        fh = fh.dropna(subset=["wpr"])
        if "isBarrierTrial" in fh.columns:
            fh = fh[fh["isBarrierTrial"].fillna(0).astype(int) == 0]
        # latest scrape wins if a (horse,date) appears more than once -
        # WPR is revised post-race, so the most recent capture is freshest
        if "scrape_date" in fh.columns:
            fh = fh.sort_values("scrape_date")
        fh = fh.drop_duplicates(subset=["horse_lc", "date_s"], keep="last")
        # (horse_lc, date) -> actual wpr
        wpr_lookup = {(r["horse_lc"], r["date_s"]): r["wpr"]
                      for _, r in fh.iterrows()}
    except Exception as e:
        print(f"  WPR actual skipped: could not read form history ({e})")
        return runners_df

    # fill wpr_actual on resulted runners
    # DISABLED: this used to fill wpr_actual from the form-history `wpr`
    # column, but that is the RAW run-day WPR, not the weight-adjusted `atw`
    # that aligns to the projection. wpr_actual is now sourced from the
    # result feed's `atw` field in update_results() (timely, correct metric)
    # and the historical backfill (backfill_atw.py). Filling from form-history
    # wpr here would (a) be the wrong metric and (b) clobber the correct atw
    # values every run. The lookup build above is retained only in case a
    # future fallback is wanted; the fill loop is intentionally a no-op.
    filled = 0
    # for idx in runners_df[resulted_mask].index:
    #     hlc = str(runners_df.at[idx, "horse"]).strip().lower()
    #     d = str(runners_df.at[idx, "date"])[:10]
    #     v = wpr_lookup.get((hlc, d))
    #     if v is not None:
    #         runners_df.at[idx, "wpr_actual"] = round(float(v), 1)
    #         filled += 1

    # actual rank within each resulted race (1 = highest actual WPR)
    ranked_races = 0
    for race_id, race in runners_df[resulted_mask].groupby("race_id"):
        actuals = race["wpr_actual"].dropna()
        if len(actuals) < 2:
            continue
        # rank: highest actual WPR = rank 1
        order = actuals.sort_values(ascending=False)
        rank_map = {i: r for r, i in enumerate(order.index, start=1)}
        for i, rk in rank_map.items():
            runners_df.at[i, "wpr_actual_rank"] = rk
        ranked_races += 1

    print(f"  WPR actual: {filled} resulted runners matched, "
          f"{ranked_races} races ranked "
          f"(fills in over ~5 days as the form history settles)")
    return runners_df


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



def compute_signal_rankings(rdf):
    """
    For a single race DataFrame (already reset_index'd to 0-based),
    return per-signal top-3 positional indices and the runner u-list.
    rdf must have contiguous 0-based index matching positional order.
    """
    n = len(rdf)
    run_id_to_pos = {str(rdf.loc[i, "run_id"]): i for i in range(n)}

    signal_rankings = []
    # Track per-runner ranks for each signal (for custom-threshold model anchors)
    # Stored as: per_runner_ranks[runner_idx] = {sig_short: rank_within_race or None}
    SIG_SHORT_KEYS = {  # map ALL_SIGNALS index → short JS key
        "jockey_win_pct_90d":   "jky",
        "wpr_peak_rank_1yr":    "peak",
        "speed_rating":         "speed",
        "toprate_rating":       "tr",
        "trainer_win_pct_365d": "trn",
    }
    per_runner_ranks = [{} for _ in range(n)]
    field_size_by_sig = {}

    for sig in ALL_SIGNALS:
        col = "fixed_win_price" if sig == "starting_price_sp" else sig
        if col == "price_top" or col not in rdf.columns or not rdf[col].notna().any():
            signal_rankings.append([-1, -1, -1, -1, -1])
            continue
        valid = rdf[rdf[col].notna()]
        ascending = sig not in SIGNALS_HIGHER
        sorted_valid = valid.sort_values(col, ascending=ascending)
        sorted_idx = sorted_valid.index.tolist()
        top5 = sorted_idx[:5]
        while len(top5) < 5:
            top5.append(-1)
        signal_rankings.append(top5[:5])
        # If this is one of our anchor candidate signals, record per-runner rank
        if sig in SIG_SHORT_KEYS:
            short = SIG_SHORT_KEYS[sig]
            field_size_by_sig[short] = len(sorted_idx)
            for rank_pos, runner_idx in enumerate(sorted_idx, start=1):
                per_runner_ranks[runner_idx][short] = rank_pos

    u_list = []
    for i in range(n):
        row = rdf.loc[i]
        def safe_float(v):
            try:
                f = float(v)
                return None if f != f else round(f, 3)
            except: return None
        def safe_int(v):
            try:
                f = float(v)
                return None if f != f else int(f)
            except: return None
        u_list.append({
            "h": str(row.get("horse", "")),
            "rid": str(row.get("run_id", "")),
            "j": str(row.get("jockey", "")),
            "tn": str(row.get("trainer", "")) if row.get("trainer") else None,
            "f": safe_int(row.get("finish_position")),
            "mgnL": safe_float(row.get("margin_finish")),   # finish margin in lengths
            "sp": safe_float(row.get("starting_price_sp")),
            "fx": safe_float(row.get("fixed_win_price")),
            "trp": safe_float(row.get("toprate_price")),
            "trr": safe_float(row.get("toprate_rating")),
            "tr": safe_float(row.get("wpr_trend")),
            "w": safe_float(row.get("wpr_nett")),
            "b": safe_int(row.get("barrier")),
            "tab": safe_int(row.get("tab_number")),
            "st": str(row.get("_settling", "")) if row.get("_settling") else None,
            "ps": str(row.get("_pace_scenario", "")) if row.get("_pace_scenario") else None,
            "es": safe_float(row.get("early_speed_score")),
            "ms": safe_float(row.get("mid_speed_score")),
            "ls": safe_float(row.get("late_speed_score")),
            "ts": safe_float(row.get("total_speed_score")),
            "ap": safe_float(row.get("avg_settled_pos")),
            "a8": safe_float(row.get("avg_800m_pos")),
            "wd": safe_float(row.get("wpr_dist")),
            "dn": safe_int(row.get("wpr_dist_n")),
            # Per-runner ranks for anchor candidate signals (None if signal missing)
            "rnk": {
                "jky":   per_runner_ranks[i].get("jky"),
                "peak":  per_runner_ranks[i].get("peak"),
                "speed": per_runner_ranks[i].get("speed"),
                "tr":    per_runner_ranks[i].get("tr"),
                "trn":   per_runner_ranks[i].get("trn"),
            },
            # Field sizes per signal (for percentage thresholds)
            "fsz": {
                "jky":   field_size_by_sig.get("jky"),
                "peak":  field_size_by_sig.get("peak"),
                "speed": field_size_by_sig.get("speed"),
                "tr":    field_size_by_sig.get("tr"),
                "trn":   field_size_by_sig.get("trn"),
            },
        })

    return signal_rankings, u_list

# -----------------------------------------------------------------------
# LOAD / SAVE
# -----------------------------------------------------------------------
# Prize money threshold for TAB filter. Races with prize_money below this
# are bush/country meetings that the user can't bet on at TAB and so are
# excluded from all outputs (HTML, picks, watchlist).
TAB_PRIZE_MIN = 20000

def load_runners():
    if RUNNERS_CSV.exists():
        df = pd.read_csv(RUNNERS_CSV, dtype={"run_id": str, "race_id": str})
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
    cols = [c for c in RUNNER_COLS if c in df.columns]
    extras = [c for c in df.columns if c not in RUNNER_COLS]
    # Always save deduplicated
    df = df.drop_duplicates(subset=["run_id"], keep="last")
    df[cols + extras].to_csv(RUNNERS_CSV, index=False)

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

def runners_to_selections(runners_df):
    """
    From the full runners DB, compute per-race top selections with vote counts.
    Returns DataFrame with one row per race (top vote-getter).
    """
    # Safety dedup — handles any duplicates that slipped through
    runners_df = runners_df.drop_duplicates(subset=["run_id"], keep="last")
    rows = []
    for race_id, rdf in runners_df.groupby("race_id"):
        rdf = rdf.copy().reset_index(drop=True)
        sc, total = compute_votes(rdf)
        if not sc:
            continue
        top_id    = sc.most_common(1)[0][0]
        top_votes = sc[top_id]
        top       = rdf[rdf["run_id"].astype(str) == str(top_id)]
        top_idx = next((i for i in range(len(rdf)) if str(rdf.loc[i, "run_id"]) == str(top_id)), 0)
        if top.empty:
            continue
        r = top.iloc[0]
        has_fs = bool(rdf["runs_with_wpr"].notna().any() and
                      (rdf["runs_with_wpr"] == 0).any())
        sp = safe(r.get("starting_price_sp")) or safe(r.get("fixed_win_price"))
        # Compute speed rank of top selection within field (pre-race)
        top_speed = safe(r.get("speed_rating"))
        all_speeds = rdf['speed_rating'].dropna()
        if top_speed is not None and len(all_speeds) > 0:
            speed_rank_in_race = int((all_speeds > top_speed).sum()) + 1
            is_on_pace = speed_rank_in_race <= 2
        else:
            speed_rank_in_race = safe(r.get("speed_rank_in_race"))
            is_on_pace = (speed_rank_in_race is not None and speed_rank_in_race <= 2)
        # Contested pace from field
        contested_pace = r.get("contested_pace")
        if contested_pace is None and len(all_speeds) >= 3:
            top3 = sorted(all_speeds, reverse=True)[:3]
            contested_pace = (top3[0] - top3[-1]) < 5
        # Settling position — use actual historical data if available
        avg_settled_top = safe(r.get("avg_settled_pos"))
        field_size = len(rdf)
        if avg_settled_top is not None:
            settling = ("leader"     if avg_settled_top <= 2.5 else
                        "on-pace"    if avg_settled_top <= 4.5 else
                        "midfield"   if avg_settled_top <= 8.0 else
                        "backmarker")
        elif speed_rank_in_race is not None and field_size > 1:
            settle_pct = (speed_rank_in_race - 1) / (field_size - 1)
            settling = ("leader"     if speed_rank_in_race <= 2 else
                        "on-pace"    if speed_rank_in_race <= 4 else
                        "midfield"   if settle_pct <= 0.6 else
                        "backmarker")
        else:
            settling = "unknown"
        # Backmarker flag with pace context (key finding: backmarker+fast = avoid)
        if settling == "backmarker":
            pace_sc = r.get("pace_scenario")
            if pace_sc == "fast":
                backmarker_flag = "caution"   # -45% ROI backtest
            elif pace_sc in ("neutral", "slow"):
                backmarker_flag = "watch"     # +141% ROI backtest
            else:
                backmarker_flag = "unknown"   # no speed data
        else:
            backmarker_flag = None

        # Barrier advantage: inside (1-4) in sprint/mile is meaningful
        barrier = safe(r.get("barrier"))
        distance = safe(r.get("distance")) or 0
        barrier_pos = ("inside" if barrier and barrier <= 4 else
                       "mid" if barrier and barrier <= 8 else
                       "wide" if barrier else None)

        # Inject per-runner context using actual historical settling positions
        # Fall back to speed rank estimate if no historical data available
        pace_horses = 0  # count of horses with avg_800m_pos <= 3 (genuine early speed)
        for i in range(field_size):
            row_i = rdf.loc[i]
            # Use actual historical avg_settled_pos if available
            avg_sp = safe(row_i.get("avg_settled_pos"))
            avg_200 = safe(row_i.get("avg_800m_pos"))
            if avg_sp is not None:
                # Use actual settled position history
                st_i = ("leader"     if avg_sp <= 2.5 else
                        "on-pace"    if avg_sp <= 4.5 else
                        "midfield"   if avg_sp <= 8.0 else
                        "backmarker")
            else:
                # Fall back to speed rank estimate
                spd_i = safe(row_i.get("speed_rating"))
                if spd_i is not None and len(all_speeds) > 0:
                    sr_i = int((all_speeds > spd_i).sum()) + 1
                else:
                    sr_i = safe(row_i.get("speed_rank_in_race"))
                if sr_i is not None and field_size > 1:
                    pct_i = (sr_i - 1) / (field_size - 1)
                    st_i = ("leader"    if sr_i <= 2 else
                            "on-pace"   if sr_i <= 4 else
                            "midfield"  if pct_i <= 0.6 else
                            "backmarker")
                else:
                    st_i = "unknown"
            # Count horses with genuine early speed for race pace score
            if avg_200 is not None and avg_200 <= 3.0:
                pace_horses += 1
            elif avg_200 is None and st_i in ("leader", "on-pace"):
                pace_horses += 1  # fallback estimate
            rdf.loc[i, "_settling"]      = st_i
            rdf.loc[i, "_pace_scenario"] = row_i.get("pace_scenario")

        # Race pace score from actual historical early speed data
        # More reliable than speed-rating estimate
        if pace_horses <= 1:
            race_pace_score = "slow"
        elif pace_horses <= 3:
            race_pace_score = "neutral"
        else:
            race_pace_score = "fast"

        sig_rankings, u_list = compute_signal_rankings(rdf)

        rows.append({
            "date":           r.get("date"),
            "venue":          r.get("venue"),
            "race":           r.get("race"),
            "race_id":        race_id,
            "horse":          r.get("horse"),
            "jockey":         r.get("jockey"),
            "trainer":        r.get("trainer"),
            "votes":          top_votes,
            "total_signals":  total,
            "sp":             sp,
            "prize_money":    r.get("prize_money"),
            "wpr_nett":       safe(r.get("wpr_nett")),
            "wpr_trend":      safe(r.get("wpr_trend")),
            "wpr_rank":       safe(r.get("wpr_rank")),
            "wpr_peak_rank_1yr": safe(r.get("wpr_peak_rank_1yr")),
            "toprate_rating": safe(r.get("toprate_rating")),
            "toprate_price":  safe(r.get("toprate_price")),
            "speed_rating":   top_speed,
            "speed_rank_in_race": speed_rank_in_race,
            "is_on_pace":     is_on_pace,
            "barrier":        barrier,
            "barrier_pos":    barrier_pos,
            "distance":       distance,
            "going":          r.get("going") if r.get("going") and str(r.get("going","")) != "nan" else None,
            "pace_scenario":  r.get("pace_scenario"),
            "contested_pace": bool(contested_pace) if contested_pace is not None else None,
            "settling":       settling,
            "backmarker_flag": backmarker_flag,
            "has_first_starter": has_fs,
            "finish":         safe(r.get("finish_position")),
            "won":            safe(r.get("won")),
            "placed":         safe(r.get("placed")),
            "returned":       (sp if safe(r.get("won")) else 0) if safe(r.get("resulted")) else None,
            "resulted":       int(safe(r.get("resulted")) or 0),
            "run_id":         top_id,
            "top_idx":        top_idx,
            "sig_rankings":   sig_rankings,
            "u_list":         u_list,
            "start_time":     r.get("start_time"),
        })
    return pd.DataFrame(rows) if rows else pd.DataFrame()

# -----------------------------------------------------------------------
# STEP 1: UPDATE RESULTS
# -----------------------------------------------------------------------
def update_results(jwt, runners_df, fetch_workers=DEFAULT_FETCH_WORKERS):
    today = date.today()
    pending = runners_df[
        (runners_df["resulted"] != 1) &
        runners_df["race_id"].notna()
    ].copy()

    if pending.empty:
        print("No pending runners to update.")
        return runners_df

    # Ensure comment columns exist so result writes have a target even on a
    # fresh CSV. Stay NaN until a result feed supplies them.
    for col in ["comments_video", "comments_steward"]:
        if col not in runners_df.columns:
            runners_df[col] = np.nan

    race_ids = pending["race_id"].astype(str).unique()
    updated  = 0
    skipped_future = 0
    skipped_old = 0
    api_calls = 0

    # ── Build start-time lookup so we can skip races that haven't started ──
    # We compute "now" with a 5-minute buffer (results aren't immediate)
    now = datetime.now()
    five_min_ago = now - timedelta(minutes=5)
    cutoff_old = today - timedelta(days=14)  # don't keep retrying ancient races

    # ── First pass: decide which races are actually eligible to fetch ──
    # (skip future + ancient races BEFORE hitting the API). Then prefetch
    # all eligible result-calls concurrently. This is the same skip-logic
    # as before, just separated from the API call so the calls can run in
    # parallel rather than one-at-a-time.
    eligible = []
    for race_id in race_ids:
        mask = runners_df["race_id"].astype(str) == str(race_id)
        sample = runners_df[mask].iloc[0]
        race_date = pd.to_datetime(sample["date"]).date() if sample.get("date") else None
        if race_date and race_date > today:
            skipped_future += 1
            continue
        if race_date and race_date < cutoff_old:
            skipped_old += 1
            continue
        if race_date == today:
            start_time_str = sample.get("start_time")
            if start_time_str:
                try:
                    hh, mm = str(start_time_str).split(":")[:2]
                    race_start = datetime.combine(today, datetime.min.time()).replace(
                        hour=int(hh), minute=int(mm))
                    if race_start > five_min_ago:
                        skipped_future += 1
                        continue
                except Exception:
                    pass
        eligible.append(race_id)

    # Concurrently fetch results for all eligible races.
    if eligible:
        from concurrent.futures import ThreadPoolExecutor, as_completed
        def _fetch_result(rid):
            try:
                return rid, (api_race_results(jwt, int(rid)) or {})
            except Exception as e:
                return rid, {"_error": str(e)}
        result_by_race = {}
        if fetch_workers <= 1:
            for rid in eligible:
                result_by_race[rid] = _fetch_result(rid)[1]
        else:
            with ThreadPoolExecutor(max_workers=fetch_workers) as pool:
                for fut in as_completed(pool.submit(_fetch_result, rid) for rid in eligible):
                    rid, res = fut.result()
                    result_by_race[rid] = res
        api_calls = len(eligible)
    else:
        result_by_race = {}

    for race_id in eligible:
        try:
            mask = runners_df["race_id"].astype(str) == str(race_id)
            result_raw = result_by_race.get(race_id) or {}
            if isinstance(result_raw, dict) and result_raw.get("_error"):
                print(f"  Error fetching results for race {race_id}: {result_raw['_error']}")
                continue
            result_runners = result_raw.get("runners", []) if isinstance(result_raw, dict) else []
            if not result_runners:
                continue

            # Build lookup: run_id -> {finish, margin, sp, price_top}
            # margin is captured if present in the results feed - the form
            # history flow already pulls 'marginFinish' from the same data
            # shape (see RICH_COLUMNS), so the field name should be the
            # same here. Missing field is fail-safe: stays None / NaN.
            result_map = {}
            for r in result_runners:
                rid = str(r.get("runId", ""))
                pos = r.get("positionFinish")
                sp  = r.get("priceStarting")
                pt  = r.get("priceTop")
                mgn = r.get("marginFinish")
                atw = r.get("atw")   # actual weight-adjusted WPR (the settled
                                     # run-day rating, aligns to the projection's
                                     # weight basis). Source of truth for
                                     # wpr_actual - captured here the moment a
                                     # race resolves, so the actual no longer
                                     # waits for the horse to be re-scraped into
                                     # form history (the lag that left recent
                                     # runs' actuals blank).
                # Running (video) and official stewards comments. Used by the
                # post-race adjudication to separate genuine model error from
                # void runs (vet/eased/checked/slow-away). Captured at result
                # time from the same feed; missing is fail-safe (stays None).
                cvid = r.get("commentsVideo")
                cstw = r.get("commentsSteward")
                if rid and pos:
                    result_map[rid] = {
                        "finish": pos, "margin": mgn,
                        "sp": sp, "price_top": pt, "atw": atw,
                        "comments_video": cvid, "comments_steward": cstw,
                    }

            # Update each runner in this race
            race_rows = runners_df[mask].index
            for idx in race_rows:
                rid = str(runners_df.loc[idx, "run_id"])
                if rid in result_map:
                    res = result_map[rid]
                    finish = res["finish"]
                    sp     = res["sp"]
                    runners_df.loc[idx, "finish_position"]  = finish
                    if res.get("margin") is not None:
                        runners_df.loc[idx, "margin_finish"] = res["margin"]
                    runners_df.loc[idx, "starting_price_sp"] = sp
                    runners_df.loc[idx, "price_top"]         = res.get("price_top")
                    # Actual weight-adjusted WPR straight from the result feed.
                    # This is the timely path: filled when the race resolves,
                    # not when the horse next races. Guarded so a missing atw
                    # leaves any existing value alone rather than nulling it.
                    if res.get("atw") is not None:
                        runners_df.loc[idx, "wpr_actual"] = round(float(res["atw"]), 1)
                    # Comments: write when present, leave existing alone when the
                    # feed omits them (some feeds populate stewards later).
                    if res.get("comments_video") is not None:
                        runners_df.loc[idx, "comments_video"] = res["comments_video"]
                    if res.get("comments_steward") is not None:
                        runners_df.loc[idx, "comments_steward"] = res["comments_steward"]
                    runners_df.loc[idx, "won"]    = 1 if finish == 1 else 0
                    runners_df.loc[idx, "placed"] = 1 if finish <= 3 else 0
                    runners_df.loc[idx, "resulted"] = 1
                    updated += 1
                else:
                    # Runner scratched or not in results — mark resulted but no finish
                    runners_df.loc[idx, "resulted"] = 1

            # Print top selection result
            sc, _ = compute_votes(runners_df[mask])
            if sc:
                top_id = str(sc.most_common(1)[0][0])
                top    = runners_df[mask & (runners_df["run_id"].astype(str) == top_id)]
                if not top.empty:
                    r     = top.iloc[0]
                    horse = r.get("horse", "?")
                    fin   = r.get("finish_position")
                    sp    = r.get("starting_price_sp")
                    venue = r.get("venue", "")
                    race  = r.get("race", "")
                    if fin:
                        status = "WON" if fin == 1 else (f"placed {int(fin)}th" if fin <= 3 else f"{int(fin)}th")
                        sp_str = f" @ ${float(sp):.2f}" if sp else ""
                        print(f"  Result: {venue} R{race} {horse} — {status}{sp_str}")

            # Previously time.sleep(0.1) here as anti-rate-limit precaution.
            # Removed 2026-05-16 - the comment said "API hasn't been rate-
            # limiting us" so this was cargo-cult slowness. Saves ~10s per
            # daily run on busy days. Add back if 429s appear.
        except Exception as e:
            print(f"  Error fetching results for race {race_id}: {e}")

    summary_bits = [f"Updated {updated} runner results"]
    if skipped_future:
        summary_bits.append(f"skipped {skipped_future} not-yet-run")
    if skipped_old:
        summary_bits.append(f"skipped {skipped_old} stale (>14 days)")
    summary_bits.append(f"{api_calls} API calls")
    print(", ".join(summary_bits) + ".")
    return runners_df

# -----------------------------------------------------------------------
# STEP 2: FETCH TODAY'S RACES (ALL RUNNERS)
# -----------------------------------------------------------------------
def fetch_todays_races(jwt, runners_df, target_date_str=None,
                       fetch_workers=DEFAULT_FETCH_WORKERS):
    today_str = target_date_str or date.today().strftime("%Y-%m-%d")

    # Check existing
    existing = runners_df[runners_df["date"].astype(str).str[:10] == today_str] if len(runners_df) else pd.DataFrame()
    pending_today = existing[existing["resulted"] != 1] if len(existing) else pd.DataFrame()

    if target_date_str is None and len(existing) > 0 and len(pending_today) == 0:
        print(f"All races for {today_str} already resulted — skipping fetch.")
        return runners_df
    elif target_date_str is None and len(existing) > 0:
        print(f"Already have {len(existing)} runners for {today_str} ({len(pending_today)} pending) — skipping fetch.")
        print(f"  (Use --date {today_str} to re-fetch)")
        return runners_df
    elif target_date_str is not None and len(pending_today) > 0:
        # Remove pending rows only, keep resulted
        n_remove = len(pending_today)
        runners_df = runners_df[
            ~((runners_df["date"].astype(str).str[:10] == today_str) & (runners_df["resulted"] != 1))
        ].copy()
        n_kept = len(runners_df[runners_df["date"].astype(str).str[:10] == today_str])
        print(f"Re-fetching {today_str} — removed {n_remove} pending rows, kept {n_kept} resulted")

    print(f"Fetching races for {today_str}...")
    calendar = api_calendar_upcoming(jwt)

    races_today = []
    for day in (calendar if isinstance(calendar, list) else []):
        if day.get("date", "") != today_str:
            continue
        for meeting in day.get("meetings", []):
            if meeting.get("isTrialMeeting") or meeting.get("isJumpout"):
                continue
            for race in meeting.get("races", []):
                if race.get("isAbandoned") or race.get("isBarrierTrial"):
                    continue
                if not race.get("prizeMoney") or race["prizeMoney"] < 1000:
                    continue
                races_today.append({
                    "date":        today_str,
                    "venue":       meeting.get("venue", ""),
                    "state":       meeting.get("state"),
                    "going":       meeting.get("going"),
                    "rail_position": meeting.get("railPosition"),
                    "track_grading": meeting.get("trackGrading"),
                    "raceId":      race.get("raceId"),
                    "number":      race.get("number"),
                    "name":        race.get("name"),
                    "distance":    race.get("distance"),
                    # race class string (BM64, CLS3, MAI...) for the
                    # model's class_move feature. None if not exposed -
                    # project_race handles None gracefully.
                    "class":       race.get("class"),
                    "prizeMoney":  race.get("prizeMoney"),
                    "startTime":   (race.get("startTime") or race.get("scheduledTime") or
                                    race.get("raceTime") or race.get("startAt") or
                                    race.get("time") or race.get("jumpTime")),
                    # raceShapeEarly/Mid/Late are post-race sectionals — omitted pre-race
                })

    print(f"  Found {len(races_today)} TAB races")
    # Debug: show start time format on first race so we can verify field name
    if races_today:
        sample = races_today[0]
        print(f"  Start time sample ({sample['venue']} R{sample['number']}): {sample.get('startTime')!r}")
    new_rows = []
    n_optimal = 0

    # Pre-fetch all races' API responses concurrently (network-bound work).
    # The processing loop below stays sequential - it just reads from this
    # dict instead of making blocking calls inline.
    prefetched = prefetch_races(jwt, [r["raceId"] for r in races_today],
                                workers=fetch_workers, label="races")

    for i, race_meta in enumerate(races_today, 1):
        rc_id = race_meta["raceId"]
        try:
            pf = prefetched.get(rc_id) or {}
            if pf.get("error"):
                print(f"  Error on {race_meta['venue']} R{race_meta['number']}: {pf['error']}")
                continue
            detail    = pf.get("detail") or []
            if not detail:
                continue
            cache     = pf.get("cache") or {}
            wpr_chart = pf.get("wpr_chart") or []
            stats     = pf.get("stats") or []

            # Capture raw per-run form history for offline WPR modelling.
            # Isolated side-effect: appends to module accumulator, does not
            # affect any downstream pipeline logic. `detail` is passed so the
            # collector can resolve horse names (wpr_chart lacks them).
            collect_wpr_form_history(wpr_chart, detail, today_str)

            wpr_lu    = build_wpr_lookup(cache)
            wpr_hist  = build_wpr_history_lookup(wpr_chart, race_date=today_str,
                                                   race_distance=race_meta.get("distance"),
                                                   race_going=race_meta.get("going"))
            stats_lu  = build_stats_lookup(stats)

            # has_fs: only if explicitly runs_with_wpr == 0
            has_fs = any(
                wpr_hist.get(d.get("runId")) is not None and
                wpr_hist[d.get("runId")].get("runs_with_wpr") == 0
                for d in detail if not d.get("isScratched")
            )

            race_runners = []
            for d in detail:
                if d.get("isScratched"):
                    continue
                rid = d.get("runId")
                w   = wpr_lu.get(rid, {})
                h   = wpr_hist.get(rid, {})
                s   = stats_lu.get(rid, {})
                race_runners.append({
                    # Race
                    "date":           today_str,
                    "venue":          race_meta["venue"],
                    "state":          race_meta["state"],
                    "race":           race_meta["number"],
                    "race_id":        str(rc_id),
                    "race_name":      race_meta["name"],
                    "distance":       race_meta["distance"],
                    "race_class":     race_meta.get("class"),
                    "prize_money":    race_meta["prizeMoney"],
                    "going":          race_meta.get("going"),
                    "track_grading":  race_meta.get("track_grading"),
                    "rail_position":  race_meta.get("rail_position"),
                    "start_time":     race_meta.get("startTime"),
                    # race_shape_early/mid/late are POST-RACE only — not stored pre-race
                    "race_shape_early": None,
                    "race_shape_mid":   None,
                    "race_shape_late":  None,
                    "has_first_starter": has_fs,
                    # Runner
                    "run_id":         str(rid),
                    "tab_number":     d.get("tabNumber"),
                    "barrier":        d.get("barrier"),
                    "horse":          d.get("horse"),
                    "jockey":         d.get("jockey"),
                    "trainer":        d.get("trainer"),
                    "runs_with_wpr":  h.get("runs_with_wpr"),
                    # Signals
                    "wpr_nett":           w.get("wpr_nett"),
                    "wpr_rank":           w.get("wpr_rank"),
                    "wpr_last1":          h.get("wpr_last1"),
                    "wpr_avg_last3":      h.get("wpr_avg_last3"),
                    "wpr_trend":          h.get("wpr_trend"),
                    "wpr_consistency":    h.get("wpr_consistency"),
                    "wpr_peak_rank_1yr":  h.get("wpr_peak_rank_1yr"),
                    "wpr_dist":           h.get("wpr_dist"),
                    "wpr_dist_n":         h.get("wpr_dist_n"),
                    "wpr_going":          h.get("wpr_going"),
                    "avg_settled_pos":    h.get("avg_settled_pos"),
                    "avg_800m_pos":       h.get("avg_800m_pos"),
                    "avg_400m_pos":       h.get("avg_400m_pos"),
                    "early_speed_score":  h.get("early_speed_score"),
                    "mid_speed_score":    h.get("mid_speed_score"),
                    "late_speed_score":   h.get("late_speed_score"),
                    "total_speed_score":  h.get("total_speed_score"),
                    # New v3 model signals (weight trajectory, distance specialty)
                    "weight_trend":       h.get("weight_trend"),
                    "wins_at_dist":       h.get("wins_at_dist"),
                    "starts_at_dist":     h.get("starts_at_dist"),
                    "places_at_dist":     h.get("places_at_dist"),
                    # Going breakdown serialised as JSON for CSV storage
                    "going_breakdown":    json.dumps(h.get("going_breakdown") or {}),
                    "form_string":        h.get("form_string"),
                    "toprate_rating":     d.get("topRateRating"),
                    "toprate_price":      d.get("topRatePrice"),
                    "speed_rating":       d.get("speed"),
                    # Pull jockey/trainer ratings from race_stats lookup
                    # (sit on runner level inside get_race_stats[], NOT on runner detail d)
                    "jockey_rating":      s.get("jockey_rating"),
                    "trainer_rating":     s.get("trainer_rating"),
                    "fixed_win_price":    d.get("fixedWinPrice"),
                    # Silks image URL from TopRate detail feed - full URL
                    # like https://silks.medialityracing.com.au/png/{hash}_front.png.
                    # Pre-built (100% coverage observed), so we just store and
                    # render directly in the dashboard.
                    "silk_url":           d.get("silksURL"),
                    "jockey_win_pct_90d": s.get("jockey_win_pct_90d"),
                    "trainer_win_pct_365d": s.get("trainer_win_pct_365d"),
                    # Jockey/trainer combo win % - new for v3 score upgrade.
                    # May be None if the live API doesn't expose it; the score
                    # formula falls back to other signals when missing.
                    "jt_combo_win_pct":   s.get("jt_combo_win_pct"),
                    "jt_combo_rides":     s.get("jt_combo_rides"),
                    # Contextual fields
                    "sect_early":         d.get("sectEarly"),
                    "weight_carried":     d.get("weightCarried"),
                    # Post-race (empty for now)
                    "starting_price_sp": None,
                    "price_top":         None,
                    "finish_position":   None,
                    "won":               None,
                    "placed":            None,
                    "resulted":          0,
                })

            if not race_runners:
                continue

            # Compute race-level context fields from speed ratings (genuine pre-race)
            rdf_ctx = pd.DataFrame(race_runners)
            # Speed rank within race
            if rdf_ctx['speed_rating'].notna().any():
                speed_ranks = rdf_ctx['speed_rating'].rank(ascending=False, method='min')
                for i in range(len(race_runners)):
                    sr = speed_ranks.iloc[i]
                    race_runners[i]['speed_rank_in_race'] = int(sr) if not math.isnan(sr) else None
            else:
                for i in range(len(race_runners)):
                    race_runners[i].setdefault('speed_rank_in_race', None)

            # Pace scenario: use actual historical early speed data if available
            # Count runners whose avg_800m_pos <= 3 (genuine early speed horses)
            pace_scenario = None
            contested_pace = None
            actual_pace_horses = rdf_ctx['avg_800m_pos'].dropna()
            speeds = rdf_ctx['speed_rating'].dropna()
            if len(actual_pace_horses) >= 3:
                # Use actual historical 200m positions
                n_pace_horses = int((actual_pace_horses <= 3.0).sum())
                pace_scenario = ("slow"    if n_pace_horses <= 1 else
                                 "fast"    if n_pace_horses >= 4 else
                                 "neutral")
                # Contested if 3+ horses have avg_800m_pos <= 2.5
                contested_pace = int((actual_pace_horses <= 2.5).sum()) >= 3
            elif len(speeds) >= 4:
                # Fall back to speed rating estimate
                mean_sp = speeds.mean()
                n_pace_horses = int((speeds > mean_sp + 5).sum())
                pace_scenario = ("slow"    if n_pace_horses <= 1 else
                                 "fast"    if n_pace_horses >= 4 else
                                 "neutral")
                top3 = sorted(speeds, reverse=True)[:3]
                contested_pace = (top3[0] - top3[-1]) < 5

            for i in range(len(race_runners)):
                race_runners[i]['pace_scenario']  = pace_scenario
                race_runners[i]['contested_pace'] = contested_pace

            # Per-runner settling: use actual avg_settled_pos if available
            field_size_rb = len(race_runners)
            rdf_ctx2 = pd.DataFrame(race_runners)
            speed_ranks_rb = (rdf_ctx2['speed_rating'].rank(ascending=False, method='min')
                              if rdf_ctx2['speed_rating'].notna().any() else None)
            for i in range(field_size_rb):
                avg_sp = race_runners[i].get('avg_settled_pos')
                if avg_sp is not None:
                    st_i = ("leader"     if avg_sp <= 2.5 else
                            "on-pace"    if avg_sp <= 4.5 else
                            "midfield"   if avg_sp <= 8.0 else
                            "backmarker")
                elif speed_ranks_rb is not None:
                    sr = speed_ranks_rb.iloc[i]
                    sr_i = int(sr) if not math.isnan(sr) else None
                    if sr_i is not None and field_size_rb > 1:
                        pct = (sr_i - 1) / (field_size_rb - 1)
                        st_i = ("leader"    if sr_i <= 2 else
                                "on-pace"   if sr_i <= 4 else
                                "midfield"  if pct <= 0.6 else
                                "backmarker")
                    else:
                        st_i = "unknown"
                else:
                    st_i = "unknown"
                race_runners[i]['_settling'] = st_i

            # Compute votes for reporting
            rdf = pd.DataFrame(race_runners)
            sc, total = compute_votes(rdf)
            top_id    = sc.most_common(1)[0][0] if sc else None
            top_votes = sc[top_id] if top_id else 0

            if top_id:
                top_row = rdf[rdf["run_id"].astype(str) == str(top_id)].iloc[0]
                sp_val  = top_row.get("fixed_win_price")
                trend_v = top_row.get("wpr_trend")
                prize_v = race_meta["prizeMoney"]

                # Check optimal filter (7+ signals, SP>=2, prize>=25k, trend>=0 or missing, no_fs)
                trend_is_missing = trend_v is None or (isinstance(trend_v, float) and math.isnan(trend_v))
                trend_ok = trend_is_missing or trend_v >= 0
                is_opt = (top_votes >= 7 and sp_val and sp_val >= 2.0
                          and prize_v >= 25000
                          and trend_ok and not has_fs)
                if is_opt:
                    n_optimal += 1

                sp_str   = f"${sp_val:.2f}" if sp_val else "N/A"
                trend_str = f"{trend_v:+.1f}" if trend_v is not None and not (isinstance(trend_v, float) and math.isnan(trend_v)) else "nan"
                flag      = "✓ OPTIMAL" if is_opt else "  saved  "
                print(f"  [{i:>2}/{len(races_today)}] {race_meta['venue']} R{race_meta['number']} "
                      f"— {flag} top: {top_row['horse']} {top_votes}/{total} "
                      f"{sp_str} trend={trend_str} prize=${prize_v:,.0f} runners={len(race_runners)}")

            new_rows.extend(race_runners)
            # Previously time.sleep(0.1) here as anti-rate-limit precaution.
            # Removed 2026-05-16 - the comment said "API hasn't been rate-
            # limiting" so this was cargo-cult slowness. Saves ~5s per day
            # on a typical new-race fetch. Add back if 429s appear.

        except Exception as e:
            print(f"  Error on {race_meta['venue']} R{race_meta['number']}: {e}")

    if new_rows:
        new_df = pd.DataFrame(new_rows)
        # Pandas emits a FutureWarning about dtype handling when concatenating
        # frames that contain all-NA columns. The warning is harmless here
        # (the result is correct); suppress just this one warning rather than
        # altering the frames, so no columns are accidentally dropped.
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", category=FutureWarning)
            runners_df = pd.concat([runners_df, new_df], ignore_index=True)
        # Deduplicate: keep last occurrence per run_id (latest fetch wins)
        runners_df = runners_df.drop_duplicates(subset=["run_id"], keep="last").reset_index(drop=True)
        total_runners = len(new_rows)
        total_races   = len(set(r["race_id"] for r in new_rows))
        print(f"\nAdded {total_runners} runners from {total_races} races for {today_str}")
        print(f"  {n_optimal} races meet optimal filter (7+ signals, SP≥$2, prize≥$25k, trend≥0 or missing)")

    return runners_df

# -----------------------------------------------------------------------
# STEP 3: REBUILD HTML
# -----------------------------------------------------------------------
def build_bt_races(bt_df):
    """
    Build BT_RACES JS array from the backtest runners CSV.
    Same compact format as RACES but for the full historical dataset.
    Only includes resulted races.
    """
    def sv(v):
        try:
            f = float(v)
            return None if math.isnan(f) else round(f, 3)
        except: return None
    def si(v):
        try:
            f = float(v)
            return None if math.isnan(f) else int(f)
        except: return None

    bt_races = []
    # Group by race
    race_cols = ['date','venue','race_id']
    for (date, venue, race_id), grp in bt_df.groupby(race_cols, sort=False):
        grp = grp.sort_values('tab_number', na_position='last')
        # Only include resulted races
        if not grp['finish_position'].notna().any():
            continue

        # Compute signal rankings for all 12 signals
        runner_list = []
        for _, row in grp.iterrows():
            runner_list.append({
                "h":  str(row.get("horse", "")),
                "j":  str(row.get("jockey", "")),
                "f":  si(row.get("finish_position")),
                "sp": sv(row.get("starting_price_sp")),
                "fx": sv(row.get("fixed_win_price")),
                "tr": sv(row.get("wpr_trend")),
                "w":  sv(row.get("wpr_nett")),
                "b":  si(row.get("barrier")),
                "st": str(row.get("_settling","")) if row.get("_settling") else None,
                "ps": str(row.get("pace_scenario","")) if row.get("pace_scenario") else None,
            })

        # Build signal rankings — same order as SIG_NAMES
        # wpr_nett, wpr_last1, wpr_avg_last3, wpr_dist, wpr_going,
        # jky_win90, trn_win365, tr_rating, speed,
        # trend(higher), peak_rank(lower), consistency(lower)
        sig_cols_higher = ["wpr_nett","wpr_last1","wpr_avg_last3","wpr_dist","wpr_going",
                           "jockey_win_pct_90d","trainer_win_pct_365d","toprate_rating","speed_rating",
                           "wpr_trend"]
        sig_cols_lower  = ["wpr_peak_rank_1yr","wpr_consistency"]

        sig_rankings = []
        for sig, asc in [(s, False) for s in sig_cols_higher] + [(s, True) for s in sig_cols_lower]:
            col = sig
            if col not in grp.columns:
                sig_rankings.append([-1,-1,-1,-1,-1])
                continue
            vals = grp[col].values
            valid = [(i, float(v)) for i, v in enumerate(vals) if v is not None and not (isinstance(v, float) and math.isnan(v))]
            if not valid:
                sig_rankings.append([-1,-1,-1,-1,-1])
                continue
            valid.sort(key=lambda x: x[1], reverse=not asc)
            top5 = [idx for idx, _ in valid[:5]]
            while len(top5) < 5:
                top5.append(-1)
            sig_rankings.append(top5)

        race_row = grp.iloc[0]
        bt_races.append({
            "d":    str(date)[:10],
            "v":    str(venue),
            "r":    si(race_row.get("race_number") or race_row.get("race")),
            "p":    si(race_row.get("prize_money")),
            "n":    0,
            "t":    1,
            "done": 1,
            "top":  0,
            "s":    sig_rankings,
            "u":    runner_list,
            "ps":   str(race_row.get("pace_scenario","")) if race_row.get("pace_scenario") else None,
            "rid":  si(race_id),
            "tm":   None,
            "dist": si(race_row.get("distance")),
            "going": str(race_row.get("going","")) if race_row.get("going") and str(race_row.get("going","")) != "nan" else None,
            "fs":   len(runner_list),
        })

    return bt_races


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
    today_str = date.today().isoformat()

    # Lightweight step timing - the rebuild has several phases and the
    # form-history step in particular can run ~60s, during which the
    # script looks hung. These prints make progress visible. import time
    # locally to avoid touching module-level imports.
    import time as _time
    _t0 = _time.time()
    def _step(msg):
        print(f"  [{_time.time() - _t0:5.1f}s] {msg}", flush=True)

    _step("Building form-history lookup (last 6 + peak + tendency)...")

    # ── Form-history lookup for the runner detail panel ──────────────────────
    # Attach each runner's last 6 race runs (newest first) so the Race-tab
    # detail panel can show a mini form table. Scoped to the horses running
    # in runners_df only - never the whole 90k-row history - so the HTML
    # payload stays small. Fail-safe: any error leaves form_lookup empty and
    # runners simply get no formRuns.
    form_lookup = {}
    form_all_lookup = {}
    _peak_run_lookup = {}
    _tend_lookup = {}
    try:
        if WPR_FORM_HISTORY_CSV.exists():
            _today_horses = set(
                str(h).strip().lower() for h in runners_df.get("horse", []) if h)
            # Pending horses only - formAll (the heavy full-history
            # comparison-table data) is built for these alone, since the
            # comparison tables matter for upcoming races, not the
            # hundreds of old resulted ones. formRuns (cheap last-6) is
            # still built for every horse so resulted races keep a form
            # table.
            if "resulted" in runners_df.columns:
                _pending_horses = set(
                    str(h).strip().lower() for h in
                    runners_df[runners_df["resulted"] != 1].get("horse", [])
                    if h)
            else:
                _pending_horses = _today_horses
            _fh = pd.read_csv(WPR_FORM_HISTORY_CSV,
                              dtype={"horse": str, "horse_id": str})
            _fh["horse_lc"] = _fh["horse"].astype(str).str.strip().str.lower()
            _fh = _fh[_fh["horse_lc"].isin(_today_horses)]
            _fh["wpr"] = pd.to_numeric(_fh["wpr"], errors="coerce")
            _fh["date"] = pd.to_datetime(_fh["date"], errors="coerce")
            _fh = _fh.dropna(subset=["date", "wpr"])
            if "isBarrierTrial" in _fh.columns:
                _fh = _fh[_fh["isBarrierTrial"].fillna(0).astype(int) == 0]
            # Dedupe: the same run can appear more than once in the form
            # history (a race scraped on two dates - the WPR rebaseline
            # issue). Without this the detail-panel form table shows each
            # run twice. Keep the latest scrape of each (horse, run date).
            _dedup_keys = ["horse_lc", "date"]
            if "track" in _fh.columns:
                _dedup_keys.append("track")
            if "scrape_date" in _fh.columns:
                _fh = _fh.sort_values("scrape_date")
            _fh = _fh.drop_duplicates(subset=_dedup_keys, keep="last")
            _fh = _fh.sort_values(["horse_lc", "date"])
            # formAll derived columns - computed VECTORISED on the whole
            # frame ONCE, before the per-horse loop. The earlier version
            # used iterrows() over all ~90k rows, which was the rebuild
            # slowdown. iterrows is a pandas anti-pattern; this avoids it.
            _fa = _fh.copy()
            _fa["_w"] = pd.to_numeric(_fa["wpr"], errors="coerce").round(1)
            _se_col = pd.to_numeric(_fa.get("sect_i_early"), errors="coerce")
            _il_col = pd.to_numeric(_fa.get("sect_i_l600"), errors="coerce")
            _diff = _se_col - _il_col
            _fa["_tmp"] = np.where(_diff >= 2, "Fast",
                          np.where(_diff <= -2, "Slow", "Even"))
            _fa.loc[_diff.isna(), "_tmp"] = None
            _ps = pd.to_numeric(_fa.get("positionSettled"), errors="coerce")
            _fs = pd.to_numeric(_fa.get("field_size"), errors="coerce")
            _rel = (_ps / _fs).clip(upper=1.0).round(3)
            _rel = _rel.where((_fs > 0) & (_ps > 0))
            _fa["_rel"] = _rel
            _fa["_ds"] = pd.to_numeric(_fa.get("distance"), errors="coerce")
            _fa["_go"] = _fa.get("going", "").astype(str).where(
                _fa.get("going").notna(), "")
            # against-shape per run = horse late sectional minus race late
            # shape. Higher = ran home stronger than the race late shape.
            # Tendency per horse = mean over the LAST 5 runs (min 3),
            # date-sorted. Used by the panel "step-up form-reading" flag.
            # Honestly characterised - see FINDINGS_distance_suitability.md:
            # mean effect is +0.65 WPR (below the 1.0 materiality threshold
            # in the scoping doc and well inside the model's ~6 WPR error).
            # Built as DISPLAY-ONLY context, not a predictive claim.
            _rsl = pd.to_numeric(_fa.get("raceShapeLate"), errors="coerce")
            _clip = _il_col.clip(-40.0, 40.0)
            _fa["_against"] = _clip - _rsl
            _fa_sorted = _fa.dropna(subset=["_against"]).sort_values(
                ["horse_lc", "date"])
            _last5 = _fa_sorted.groupby("horse_lc")["_against"].apply(
                lambda s: s.tail(5).mean() if len(s) >= 3 else np.nan)
            _tend_lookup = _last5.dropna().round(2).to_dict()
            # pre-group _fa by horse so the per-horse slice below is a
            # dict access, not a full-frame filter (the mistake that has
            # bitten this rebuild before).
            _fa_by_horse = dict(tuple(_fa.groupby("horse_lc")))
            for _hlc, _g in _fh.groupby("horse_lc"):
                _last = _g.tail(6)
                _peak_wpr = _g["wpr"].max()
                # Find the most recent run at peak WPR that is OUTSIDE
                # the last-6 window. If the peak is in the last 6, leave
                # peakRun null - the panel only needs the extra row when
                # the peak is older. Tolerance 0.05 mirrors the pk flag.
                _last_ids = set(_last.index.tolist())
                _peak_rows = _g[
                    (_g["wpr"] - _peak_wpr).abs() < 0.05]
                _peak_outside = _peak_rows[~_peak_rows.index.isin(_last_ids)]
                _peak_run_record = None
                _runs = []
                for _, _r in _last.iloc[::-1].iterrows():   # newest first
                    _w = float(_r["wpr"])
                    # NOTE on sectionals - two different things, both kept:
                    #  - se/sm/sl  = raceShapeEarly/Mid/Late: the RACE-WIDE
                    #    tempo shape (how the race was run), NOT this horse.
                    #  - ie/im/il  = sect_i_early / sect_i_to800 / sect_i_l600:
                    #    THIS HORSE's own early/mid/late sectional figures.
                    # Keeping both lets the panel show the horse's run and
                    # (future work) compare it against the race shape.
                    def _shape(v):
                        return round(float(v), 1) if pd.notna(v) else None
                    _runs.append({
                        "d":  str(_r["date"].date()),
                        "trk": str(_r.get("track", "")) if _r.get("track") else "",
                        "dist": int(_r["distance"]) if pd.notna(_r.get("distance")) else None,
                        "go": str(_r.get("going", "")) if _r.get("going") else "",
                        "fin": int(_r["positionFinish"]) if pd.notna(_r.get("positionFinish")) else None,
                        "wpr": round(_w, 1),
                        "se": _shape(_r.get("raceShapeEarly")),  # race shape early
                        "sm": _shape(_r.get("raceShapeMid")),    # race shape mid
                        "sl": _shape(_r.get("raceShapeLate")),   # race shape late
                        "ie": _shape(_r.get("sect_i_early")),    # horse early sectional
                        "im": _shape(_r.get("sect_i_to800")),    # horse mid sectional
                        "il": _shape(_r.get("sect_i_l600")),     # horse late sectional
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
                    })
                form_lookup[_hlc] = _runs
                # peakRun: a single rich record for the most recent
                # career-peak run that falls OUTSIDE the last-6 window.
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
                for _w, _go, _ds, _tmp, _rel, _dt in zip(
                        _fa_g["_w"], _fa_g["_go"], _fa_g["_ds"],
                        _fa_g["_tmp"], _fa_g["_rel"], _fa_dates):
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
                    })
                form_all_lookup[_hlc] = _recs
    except Exception as _e:
        print(f"  Form-history lookup skipped: {_e}")
        form_lookup = {}
        form_all_lookup = {}
        _peak_run_lookup = {}
        _tend_lookup = {}

    # Predicted settling band per runner, for the detail-panel settling
    # comparison table. Uses settling_estimate's logic (run-style
    # tendency + barrier nudge; validated MAE 0.207).
    #
    # VECTORISED: a horse's run-style tendency (mean relative settle) is
    # a stable per-horse number. The earlier version date-filtered the
    # horse's history per runner (~thousands of pandas ops, ~130s). Now
    # the tendency is computed once for every horse via one groupby, and
    # per runner it is just tendency + barrier_nudge - pure arithmetic.
    # Runs for ALL runners (no scoping), so every race's detail panel
    # gets its settling highlight.
    _step("Building settling-band lookup...")
    _settle_band_lookup = {}
    try:
        import settling_estimate as _se_mod
        if WPR_FORM_HISTORY_CSV.exists():
            _sfh = pd.read_csv(WPR_FORM_HISTORY_CSV,
                               dtype={"horse": str}, low_memory=False)
            _sfh["horse_lc"] = _sfh["horse"].astype(str).str.strip().str.lower()
            if "isBarrierTrial" in _sfh.columns:
                _sfh = _sfh[_sfh["isBarrierTrial"].fillna(0).astype(int) == 0]
            # run-style tendency per horse, vectorised: mean of
            # positionSettled / field_size over the horse's runs.
            _ps = pd.to_numeric(_sfh.get("positionSettled"), errors="coerce")
            _fs = pd.to_numeric(_sfh.get("field_size"), errors="coerce")
            _rel = (_ps / _fs).clip(0, 1)
            _rel = _rel.where((_ps > 0) & (_fs > 0))
            _sfh = _sfh.assign(_rel=_rel)
            _grp = _sfh.dropna(subset=["_rel"]).groupby("horse_lc")["_rel"]
            _tendency = _grp.mean().to_dict()
            _tend_n = _grp.count().to_dict()

            def _band_of(rel):
                if rel <= 0.20:
                    return "Leader"
                if rel <= 0.45:
                    return "On-pace"
                if rel <= 0.70:
                    return "Midfield"
                return "Back"

            for _, _rr in runners_df.iterrows():
                _hlc = str(_rr.get("horse", "")).strip().lower()
                _rid = str(_rr.get("run_id", ""))
                _tend = _tendency.get(_hlc)
                if _tend is None:
                    continue
                _fsz = _rr.get("field_size")
                _nudge = _se_mod.barrier_nudge(
                    _rr.get("barrier"),
                    int(_fsz) if pd.notna(_fsz) else None)
                _rel_est = min(1.0, max(0.0, _tend + _nudge))
                _settle_band_lookup[_rid] = _band_of(_rel_est)
    except Exception as _e:
        print(f"  Settling-band lookup skipped: {_e}")
        _settle_band_lookup = {}

    _step("Building per-race runner payload...")
    races_data = []
    for race_id, rdf in runners_df.groupby("race_id"):
        rdf = rdf.copy().reset_index(drop=True)
        if len(rdf) == 0:
            continue
        first = rdf.iloc[0]

        # Per-race cumulative score: predictive composite for quaddie/exotic use
        # Cumulative score removed (Stage 2) - WPR projection ranks runners.
        # Empty dict kept so the HTML payload code degrades gracefully until
        # the dashboard rework (Stage 4) removes the score UI.
        cum_lookup = {}

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
                "trr":  sf(row.get("toprate_rating")),
                "trp":  sf(row.get("toprate_price")),
                "spd":  sf(row.get("speed_rating")),
                # All four sectional speed scores (the user wants Mid+Late+Total visible)
                "es":   sf(row.get("early_speed_score")),
                "ms":   sf(row.get("mid_speed_score")),
                "ls":   sf(row.get("late_speed_score")),
                "ts":   sf(row.get("total_speed_score")),
                "wtr":  sf(row.get("weight_trend")),
                # Distance performance: starts/wins/places at this distance ±10%
                "ds":   si(row.get("starts_at_dist")),
                "dw":   si(row.get("wins_at_dist")),
                "dp":   si(row.get("places_at_dist")),
                "wd":   sf(row.get("wpr_dist")),
                # Going performance breakdown - dict by category
                "gb":   gb_parsed,
                # Form string: last 4 finishes (e.g. "3-1-7-2")
                "fm":   str(row.get("form_string")) if row.get("form_string") and str(row.get("form_string")) != "nan" else None,
                # Finish margin in lengths - distinct from "fm" above which
                # is the form string. Keyed mgnL to avoid that collision.
                "mgnL": sf(row.get("margin_finish")),
                "asp":  sf(row.get("avg_settled_pos")),
                "wpr1": sf(row.get("wpr_last1")),
                "wpra": sf(row.get("wpr_avg_last3")),
                "wprt": sf(row.get("wpr_trend")),
                "wprp": sf(row.get("wpr_peak_rank_1yr")),
                "w":    sf(row.get("wpr_nett")),
                "wt":   sf(row.get("weight_carried")),
                # Strike rates (already in CSV)
                "jw":   sf(row.get("jockey_win_pct_90d")),
                "tw":   sf(row.get("trainer_win_pct_365d")),
                # TopRate's own jockey/trainer ratings (separate from strike rates)
                "jrt":  sf(row.get("jockey_rating")),
                "trt":  sf(row.get("trainer_rating")),
                "fx":   sf(row.get("fixed_win_price")),
                # Silks image URL (full https URL ending in _front.png).
                # Dashboard renders an <img> on Race + Summary cards.
                "sk":   str(row.get("silk_url")) if row.get("silk_url") and str(row.get("silk_url")) != "nan" else None,
                "sp":   sf(row.get("starting_price_sp")),
                "top":  sf(row.get("price_top")),
                "f":    si(row.get("finish_position")),
                "won":  si(row.get("won")),
                "fs":   len(rdf),
                # Cumulative score + rank within race (predictive composite for exotics)
                "cs":   _cs.get("score"),
                "crk":  _cs.get("rank"),
                # Confidence: 1 = signals tightly clustered (unanimous), 0 = wide spread (split)
                # None for races with only 1 signal populated (can't measure agreement)
                "csc":  _cs.get("conf"),
                # Per-signal percentile breakdown (for the detail panel) -
                # dict of signal_name -> percentile in [0,1]
                "csg":  _cs.get("sigs") or {},
                # ── Punting Form ratings (None if PF didn't rate this runner) ─
                # AI signals
                "pfaiR":   sf(row.get("pf_ai_rank")),
                "pfaiPrc": sf(row.get("pf_ai_price")),
                "pfaiSc":  sf(row.get("pf_ai_score")),
                # Class signals
                "wcR":     sf(row.get("pf_class_rank")),
                "tacwcR":  sf(row.get("pf_tac_class_rank")),
                # Time / sectional ranks
                "tR":      sf(row.get("pf_time_rank")),
                "etR":     sf(row.get("pf_early_time_rank")),
                "l600R":   sf(row.get("pf_last600_rank")),
                "l400R":   sf(row.get("pf_last400_rank")),
                "l200R":   sf(row.get("pf_last200_rank")),
                # Pace / class change
                "rs":      str(row.get("pf_run_style")) if row.get("pf_run_style") else None,
                "clsChg":  sf(row.get("pf_class_change")),
                # ── WPR projection (Step 2c) ─────────────────────────────────
                # wpj* keys deliberately distinct from existing "wprp"
                # (wpr_peak_rank_1yr) and "w"/"wpra" to avoid collisions.
                # None on fallback runners (under 3 prior runs).
                "wpjp":  sf(row.get("wprp_proj")),    # projected run-day WPR
                "wpjc":  si(row.get("wprp_conf")),    # confidence 0-100
                "wpjpr": sf(row.get("wprp_price")),   # fair-value WPR price
                "wpjr":  si(row.get("wprp_rank")),    # WPR rank within race
                "wpjpk": sf(row.get("wprp_peak")),    # career peak WPR
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
                "wpja":  sf(row.get("wpr_actual")),
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
                # career-peak run when it falls OUTSIDE the last 6 runs.
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
            "distance":  int(first.get("distance") or 0),
            "going":     str(first.get("going", "")) if first.get("going") and str(first.get("going")) != "nan" else "",
            "track_grading": str(first.get("track_grading", "")) if first.get("track_grading") else "",
            "rail":      str(first.get("rail_position", "")) if first.get("rail_position") and str(first.get("rail_position")) != "nan" else "",
            "prize":     int(first.get("prize_money") or 0),
            "start_time": str(first.get("start_time", "")) if first.get("start_time") else "",
            "rse":       sf(first.get("race_shape_early")) if callable(sf) else None,
            "rsm":       sf(first.get("race_shape_mid")) if callable(sf) else None,
            "rsl":       sf(first.get("race_shape_late")) if callable(sf) else None,
            "hfs":       int(bool(first.get("has_first_starter"))),  # has first starter
            # PF coverage at race level: 1 if all runners in this race have
            # PF AI rank populated (meeting was rated by PF), 0 otherwise.
            # When 0, the new model rule produces no picks for this race.
            "pfRel":     int(bool(rdf.get("pf_ai_rank") is not None
                                   and rdf["pf_ai_rank"].notna().all())) if "pf_ai_rank" in rdf.columns else 0,
            "fs":        len(rdf),
            "done":      int((rdf["resulted"] == 1).all() if rdf["resulted"].notna().any() else 0),
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
                # PF data carried through to picks for the Today tab and history
                "pf_ai_rank":      r.get("pf_ai_rank"),
                "pf_ai_price":     r.get("pf_ai_price"),
                "pf_class_rank":   r.get("pf_class_rank"),
                "pf_last600_rank": r.get("pf_last600_rank"),
                "pf_last400_rank": r.get("pf_last400_rank"),
                "pf_last200_rank": r.get("pf_last200_rank"),
                "pf_run_style":    r.get("pf_run_style"),
                "pf_class_change": r.get("pf_class_change"),
            })

    # ── Model meta removed (WPR-only refactor) ───────────────────────────────
    # MODEL_DEFS and the Edge/Volume model rule were removed. model_meta is
    # now empty and primary_key a placeholder; the HTML still accepts these
    # args and degrades gracefully (no picks). The dashboard rework (Stage 4)
    # removes the picks UI entirely.
    primary_key = "edge"
    model_meta = {}

    # ── Build price history map: run_id -> {o, oat, r, rat} ──────────────────
    price_hist_map = {}
    if PRICE_HISTORY_CSV.exists():
        try:
            ph = pd.read_csv(PRICE_HISTORY_CSV, dtype={"run_id": str, "race_id": str})
            ph = ph[ph["fixed_win_price"].notna() & (ph["fixed_win_price"] > 0)].copy()
            ph["snapshot_time"] = pd.to_datetime(ph["snapshot_time"], errors="coerce", utc=True)
            ph = ph.dropna(subset=["snapshot_time"])
            ph["local_date"] = ph["snapshot_time"].dt.tz_convert("Australia/Melbourne").dt.strftime("%Y-%m-%d")
            today_ph = ph[ph["local_date"] == today_str]
            for run_id, grp in today_ph.groupby("run_id"):
                grp = grp.sort_values("snapshot_time")
                first_p = grp.iloc[0]
                last_p  = grp.iloc[-1]
                price_hist_map[run_id] = {
                    "o":   float(first_p["fixed_win_price"]),
                    "oat": first_p["snapshot_time"].isoformat(),
                    "r":   float(last_p["fixed_win_price"]),
                    "rat": last_p["snapshot_time"].isoformat(),
                    "n":   int(len(grp)),
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
    html, data_json = render_html(
        races=races_data,
        model_picks_by_race=model_picks_by_race,
        model_meta=model_meta,
        price_hist=price_hist_map,
        run_date=run_date,
        run_iso=now_iso,
        model_pick_rows=model_pick_rows or [],
        primary_model_key=primary_key,
    )
    OUTPUT_HTML.write_text(html, encoding="utf-8")
    # Data payload written alongside the HTML. The page fetches this at boot
    # instead of inlining it (keeps the JS compile cost off the load path).
    OUTPUT_DATA = OUTPUT_HTML.parent / "toprate_data.json"
    OUTPUT_DATA.write_text(data_json, encoding="utf-8")
    _step("HTML + data write complete.")

    n_total   = len(races_data)
    n_done    = sum(1 for r in races_data if r["done"] == 1)
    n_pending = n_total - n_done
    n_picks   = sum(len(picks_by_model.get(primary_key, []))
                    for picks_by_model in model_picks_by_race.values())
    print(f"HTML rebuilt -> {OUTPUT_HTML}")
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

    # Files we care about
    files_to_push = []
    for f in ["toprate_live.html", "toprate_data.json", "toprate_runners.csv",
              "toprate_model_picks.csv", "toprate_price_history.csv"]:
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
    parser = argparse.ArgumentParser(description="TopRate daily runner database + live HTML")
    parser.add_argument("--no-html",    action="store_true", help="Skip HTML rebuild")
    parser.add_argument("--backfill",   type=int, default=0, help="Backfill results for last N days")
    parser.add_argument("--date",       help="Fetch races for specific date (YYYY-MM-DD)")
    parser.add_argument("--publish",    action="store_true", help="After rebuilding, push HTML to GitHub Pages")
    parser.add_argument("--rebuild-only", action="store_true",
                        help="Skip the API fetch/projection/results steps and "
                             "just rebuild the HTML from the existing CSV, then "
                             "(with --publish) push it. Fast path for HTML/CSS "
                             "template changes that need no fresh data.")
    parser.add_argument("--serve",      action="store_true", help="After rebuilding, serve HTML on local network for iPhone access")
    parser.add_argument("--serve-only", action="store_true", help="Skip fetch/rebuild, just start the server (use existing HTML)")
    parser.add_argument("--port",       type=int, default=8080, help="Port for --serve (default 8080)")
    parser.add_argument("--workers",    type=int, default=DEFAULT_FETCH_WORKERS,
                        help=f"Concurrent API fetch workers (default {DEFAULT_FETCH_WORKERS}). "
                             f"Use --workers 1 for fully sequential if the API rate-limits.")
    args = parser.parse_args()

    if args.serve_only:
        serve(args.port)
        return

    print(f"\n{'='*60}")
    print(f"TopRate Daily — {datetime.now():%Y-%m-%d %H:%M}")
    print(f"{'='*60}\n")

    runners_df = load_runners()
    n_existing = len(runners_df)
    n_races    = runners_df["race_id"].nunique() if n_existing else 0
    print(f"Runners DB: {n_existing:,} runners across {n_races:,} races ({RUNNERS_CSV})")

    # ── Fast path: rebuild HTML from the existing CSV, no API fetch ──────────
    # For HTML/CSS template changes that need no fresh data. Skips login,
    # results, today's-races fetch, form flush, projection, race-speed,
    # actuals and the price snapshot - the slow ~3-4 min of a full run - and
    # goes straight to the HTML rebuild (~3 min mostly form-history lookup)
    # plus publish. Use: python toprate_daily.py --rebuild-only --publish
    if args.rebuild_only:
        print("── Rebuild-only: skipping API fetch, rebuilding HTML from existing CSV ──")
        rebuild_html(runners_df, model_pick_rows=[])
        if args.publish:
            publish()
        print(f"\n{'='*60}")
        print("Done (rebuild-only).")
        if args.serve:
            serve(args.port)
        return

    jwt = login()
    print()

    print(f"── Step 1: Updating results ── (fetch workers: {args.workers})")
    runners_df = update_results(jwt, runners_df, fetch_workers=args.workers)
    print()

    print("── Step 2: Fetching today's races ──")
    runners_df = fetch_todays_races(jwt, runners_df, args.date,
                                    fetch_workers=args.workers)
    print()

    # Persist the raw WPR form-history captured during the scrape. Isolated
    # from the rest of the pipeline - just writes its own append-only CSV.
    print("── Step 2a: Saving WPR form history ──")
    flush_wpr_form_history()
    print()

    # ── Step 2c: WPR projection ─────────────────────────────────────────────
    # Runs after the form-history flush so wpr_form_history.csv on disk holds
    # every runner's full history. Adds the wprp_* columns (projected WPR,
    # confidence, price, rank, peak, description). Additive - never breaks the
    # pipeline; returns runners_df unchanged on any failure.
    print("── Step 2c: WPR projection ──")
    runners_df = compute_wpr_projection(runners_df, args.date)
    print()

    # Step 2d: automated race-speed (early-tempo) estimate. Adds rs_score
    # and rs_label per race. Low-confidence estimate, context only -
    # additive and fail-safe, never breaks the pipeline.
    print("── Step 2d: Race-speed estimate ──")
    runners_df = compute_race_speed(runners_df, args.date)
    print()

    # Step 2e: actual WPR for resulted runners. Joins the real run-day WPR
    # from the form history onto resulted runners so the dashboard can show
    # predicted vs actual. Fills in over ~5 days as the form history
    # settles. Additive and fail-safe.
    print("── Step 2e: Actual WPR for resulted runners ──")
    runners_df = compute_wpr_actual(runners_df)
    print()

    # Step 2f: fill comments (video + stewards) onto resulted runners from the
    # form history. Like the actual WPR, comments land over the days after a
    # race; this self-healing pass picks them up progressively, so no manual
    # backfill is needed. Additive and fail-safe.
    print("── Step 2f: Comments for resulted runners ──")
    runners_df = fill_comments_from_history(runners_df)
    print()

    save_runners(runners_df)
    print(f"Saved -> {RUNNERS_CSV} ({len(runners_df):,} runners, {runners_df['race_id'].nunique():,} races)")
    
    # Snapshot prices for drift tracking
    print("  Snapshotting prices for drift tracking…")
    snapshot_prices(runners_df)
    print()

    # ── Model picks removed (WPR-only refactor Stage A) ──
    # The Edge/Volume model rule has been removed. The dashboard now
    # presents WPR projection rankings; bet selection is manual. HTML is
    # rebuilt with no model picks.
    model_pick_rows = []

    if not args.no_html:
        print("── Step 4: Rebuilding HTML ──")
        rebuild_html(runners_df, model_pick_rows=model_pick_rows)

    if args.publish:
        publish()

    print(f"\n{'='*60}")
    print("Done.")

    if args.serve:
        serve(args.port)

if __name__ == "__main__":
    main()
