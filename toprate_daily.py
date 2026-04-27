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
import argparse
import sys
import time
import math
import json
import os
import urllib3
from datetime import datetime, timedelta, date
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

RUNNERS_CSV    = Path(__file__).parent / "toprate_runners.csv"
SELECTIONS_CSV = Path(__file__).parent / "toprate_selections.csv"
OUTPUT_HTML    = Path(__file__).parent / "toprate_live.html"

# 14 signals matching the backtest
SIGNALS_HIGHER = ["wpr_nett","wpr_last1","wpr_avg_last3","jockey_win_pct_90d",
                  "trainer_win_pct_365d","toprate_rating","speed_rating"]
SIGNALS_LOWER  = ["starting_price_sp","wpr_rank","wpr_peak_rank_1yr","wpr_consistency",
                  "toprate_price","fixed_win_price","price_top"]
ALL_SIGNALS    = SIGNALS_HIGHER + SIGNALS_LOWER

# Runner DB columns
RUNNER_COLS = [
    # Race info
    "date","venue","state","race","race_id","race_name","distance","prize_money",
    "going","track_grading","rail_position","start_time",
    "race_shape_early","race_shape_mid","race_shape_late",
    "has_first_starter",
    # Runner info
    "run_id","tab_number","barrier","horse","jockey","trainer","runs_with_wpr",
    # Signal values (raw)
    "wpr_nett","wpr_rank","wpr_last1","wpr_avg_last3","wpr_trend","wpr_consistency",
    "wpr_peak_rank_1yr","toprate_rating","toprate_price","speed_rating",
    "fixed_win_price","jockey_win_pct_90d","trainer_win_pct_365d",
    # Pre-race market (starting_price_sp and price_top filled post-race)
    "starting_price_sp","price_top",
    # Result fields
    "finish_position","won","placed","resulted",
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

def build_wpr_history_lookup(wpr_chart, race_date=None):
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
        peak1_rank  = None
        for p in runner.get("peak", []):
            d = p.get("domain", {})
            if (d.get("period") == "1 year" and d.get("jumpsOrFlats") == "flatsOnly"
                    and d.get("distances") == "all"):
                peak1_rank = p.get("peak1Rank")
                break
        lookup[rid] = {
            "wpr_last1":         wprs[0] if wprs else None,
            "wpr_avg_last3":     round(mean(wprs[:3]), 1) if wprs else None,
            "wpr_trend":         trend,
            "wpr_consistency":   consistency,
            "wpr_peak_rank_1yr": peak1_rank,
            "runs_with_wpr":     len(wprs),
        }
    return lookup

def build_stats_lookup(race_stats):
    lookup = {}
    for runner in (race_stats or []):
        rid = runner.get("runId")
        def pick(lst, region, price, days, jumps):
            for s in (lst or []):
                d = s.get("domain", {})
                if (d.get("region") == region and d.get("startingPrice") == price
                        and d.get("periodDays") == days and d.get("jumpsOrFlats") == jumps):
                    return s
            return {}
        j90  = pick(runner.get("jockeyStats",  []), "metro", "all",  90, "flatsOnly")
        t365 = pick(runner.get("trainerStats", []), "metro", "all", 365, "flatsOnly")
        lookup[rid] = {
            "jockey_win_pct_90d":   j90.get("winPercent"),
            "trainer_win_pct_365d": t365.get("winPercent"),
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


def compute_signal_rankings(rdf):
    """
    For a single race DataFrame (already reset_index'd to 0-based),
    return per-signal top-3 positional indices and the runner u-list.
    rdf must have contiguous 0-based index matching positional order.
    """
    n = len(rdf)
    run_id_to_pos = {str(rdf.loc[i, "run_id"]): i for i in range(n)}

    signal_rankings = []
    for sig in ALL_SIGNALS:
        col = "fixed_win_price" if sig == "starting_price_sp" else sig
        if col == "price_top" or col not in rdf.columns or not rdf[col].notna().any():
            signal_rankings.append([-1, -1, -1])
            continue
        valid = rdf[rdf[col].notna()]
        ascending = sig not in SIGNALS_HIGHER
        sorted_valid = valid.sort_values(col, ascending=ascending)
        top3 = sorted_valid.index.tolist()[:3]  # positional indices (0-based after reset)
        while len(top3) < 3:
            top3.append(-1)
        signal_rankings.append(top3[:3])

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
            "j": str(row.get("jockey", "")),
            "f": safe_int(row.get("finish_position")),
            "sp": safe_float(row.get("starting_price_sp")),
            "fx": safe_float(row.get("fixed_win_price")),
            "tr": safe_float(row.get("wpr_trend")),
            "w": safe_float(row.get("wpr_nett")),
            "b": safe_int(row.get("barrier")),
            "st": str(row.get("_settling", "")) if row.get("_settling") else None,
            "ps": str(row.get("_pace_scenario", "")) if row.get("_pace_scenario") else None,
        })

    return signal_rankings, u_list

# -----------------------------------------------------------------------
# LOAD / SAVE
# -----------------------------------------------------------------------
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
        return df
    return pd.DataFrame(columns=RUNNER_COLS)

def save_runners(df):
    cols = [c for c in RUNNER_COLS if c in df.columns]
    extras = [c for c in df.columns if c not in RUNNER_COLS]
    # Always save deduplicated
    df = df.drop_duplicates(subset=["run_id"], keep="last")
    df[cols + extras].to_csv(RUNNERS_CSV, index=False)

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
        # Settling position estimate
        field_size = len(rdf)
        if speed_rank_in_race is not None and field_size > 1:
            settle_pct = (speed_rank_in_race - 1) / (field_size - 1)
            settling = ("leader"     if speed_rank_in_race == 1 else
                        "on-pace"    if speed_rank_in_race <= 2 else
                        "midfield"   if settle_pct <= 0.6 else
                        "backmarker")
        else:
            settle_pct = None
            settling   = "unknown"
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

        # Inject per-runner context into rdf so compute_signal_rankings can include b/st/ps in u_list
        for i in range(field_size):
            row_i = rdf.loc[i]
            spd_i = safe(row_i.get("speed_rating"))
            if spd_i is not None and len(all_speeds) > 0:
                sr_i = int((all_speeds > spd_i).sum()) + 1
            else:
                sr_i = safe(row_i.get("speed_rank_in_race"))
            if sr_i is not None and field_size > 1:
                pct_i = (sr_i - 1) / (field_size - 1)
                st_i = ("leader"    if sr_i == 1 else
                        "on-pace"   if sr_i <= 2 else
                        "midfield"  if pct_i <= 0.6 else
                        "backmarker")
            else:
                st_i = "unknown"
            rdf.loc[i, "_settling"]      = st_i
            rdf.loc[i, "_pace_scenario"] = row_i.get("pace_scenario")

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
def update_results(jwt, runners_df):
    today = date.today()
    pending = runners_df[
        (runners_df["resulted"] != 1) &
        runners_df["race_id"].notna()
    ].copy()

    if pending.empty:
        print("No pending runners to update.")
        return runners_df

    race_ids = pending["race_id"].astype(str).unique()
    updated  = 0

    for race_id in race_ids:
        mask = runners_df["race_id"].astype(str) == str(race_id)
        sample = runners_df[mask].iloc[0]
        race_date = pd.to_datetime(sample["date"]).date() if sample.get("date") else None
        if race_date and race_date > today:
            continue

        try:
            result_raw = api_race_results(jwt, int(race_id)) or {}
            result_runners = result_raw.get("runners", []) if isinstance(result_raw, dict) else []
            if not result_runners:
                continue

            # Build lookup: run_id -> {finish, sp, price_top}
            result_map = {}
            for r in result_runners:
                rid = str(r.get("runId", ""))
                pos = r.get("positionFinish")
                sp  = r.get("priceStarting")
                pt  = r.get("priceTop")
                if rid and pos:
                    result_map[rid] = {"finish": pos, "sp": sp, "price_top": pt}

            # Update each runner in this race
            race_rows = runners_df[mask].index
            for idx in race_rows:
                rid = str(runners_df.loc[idx, "run_id"])
                if rid in result_map:
                    res = result_map[rid]
                    finish = res["finish"]
                    sp     = res["sp"]
                    runners_df.loc[idx, "finish_position"]  = finish
                    runners_df.loc[idx, "starting_price_sp"] = sp
                    runners_df.loc[idx, "price_top"]         = res.get("price_top")
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

            time.sleep(0.3)
        except Exception as e:
            print(f"  Error fetching results for race {race_id}: {e}")

    print(f"Updated {updated} runner results.")
    return runners_df

# -----------------------------------------------------------------------
# STEP 2: FETCH TODAY'S RACES (ALL RUNNERS)
# -----------------------------------------------------------------------
def fetch_todays_races(jwt, runners_df, target_date_str=None):
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

    for i, race_meta in enumerate(races_today, 1):
        rc_id = race_meta["raceId"]
        try:
            detail    = api_race_detail(jwt, rc_id) or []
            if not detail:
                continue
            cache     = api_race_cache(jwt, rc_id) or {}
            wpr_chart = api_race_wpr(jwt, rc_id) or []
            stats     = api_race_stats(jwt, rc_id) or []

            wpr_lu    = build_wpr_lookup(cache)
            wpr_hist  = build_wpr_history_lookup(wpr_chart, race_date=today_str)
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
                    "toprate_rating":     d.get("topRateRating"),
                    "toprate_price":      d.get("topRatePrice"),
                    "speed_rating":       d.get("speed"),
                    "fixed_win_price":    d.get("fixedWinPrice"),
                    "jockey_win_pct_90d": s.get("jockey_win_pct_90d"),
                    "trainer_win_pct_365d": s.get("trainer_win_pct_365d"),
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

            # Pace scenario: estimate from field speed distribution (pre-race)
            # Count runners with speed_rating well above field mean = natural pace horses
            speeds = rdf_ctx['speed_rating'].dropna()
            pace_scenario = None
            contested_pace = None
            if len(speeds) >= 4:
                mean_sp = speeds.mean()
                n_pace_horses = int((speeds > mean_sp + 5).sum())
                pace_scenario = ("slow" if n_pace_horses <= 1
                                 else "fast" if n_pace_horses >= 4
                                 else "neutral")
                # Contested if top-3 speeds within 5pts of each other
                top3 = sorted(speeds, reverse=True)[:3]
                contested_pace = (top3[0] - top3[-1]) < 5

            for i in range(len(race_runners)):
                race_runners[i]['pace_scenario']  = pace_scenario
                race_runners[i]['contested_pace'] = contested_pace

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

                # Check optimal filter (7+ signals, SP>=2, prize>=25k, trend>0, no_fs)
                is_opt = (top_votes >= 7 and sp_val and sp_val >= 2.0
                          and prize_v >= 25000
                          and trend_v is not None and not (isinstance(trend_v, float) and math.isnan(trend_v))
                          and trend_v > 0 and not has_fs)
                if is_opt:
                    n_optimal += 1

                sp_str   = f"${sp_val:.2f}" if sp_val else "N/A"
                trend_str = f"{trend_v:+.1f}" if trend_v is not None and not (isinstance(trend_v, float) and math.isnan(trend_v)) else "nan"
                flag      = "✓ OPTIMAL" if is_opt else "  saved  "
                print(f"  [{i:>2}/{len(races_today)}] {race_meta['venue']} R{race_meta['number']} "
                      f"— {flag} top: {top_row['horse']} {top_votes}/{total} "
                      f"{sp_str} trend={trend_str} prize=${prize_v:,.0f} runners={len(race_runners)}")

            new_rows.extend(race_runners)
            time.sleep(0.3)

        except Exception as e:
            print(f"  Error on {race_meta['venue']} R{race_meta['number']}: {e}")

    if new_rows:
        new_df = pd.DataFrame(new_rows)
        runners_df = pd.concat([runners_df, new_df], ignore_index=True)
        # Deduplicate: keep last occurrence per run_id (latest fetch wins)
        runners_df = runners_df.drop_duplicates(subset=["run_id"], keep="last").reset_index(drop=True)
        total_runners = len(new_rows)
        total_races   = len(set(r["race_id"] for r in new_rows))
        print(f"\nAdded {total_runners} runners from {total_races} races for {today_str}")
        print(f"  {n_optimal} races meet optimal filter (7+ signals, SP≥$2, prize≥$25k, trend>0)")

    return runners_df

# -----------------------------------------------------------------------
# STEP 3: REBUILD HTML
# -----------------------------------------------------------------------
def rebuild_html(runners_df):
    """
    Build selections summary from runners DB, then render interactive HTML.
    """
    # Compute per-race top selection with vote count
    sel_df = runners_to_selections(runners_df)

    if sel_df.empty:
        print("No selections to render.")
        return

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

    races = []
    for _, r in sel_df.sort_values(["date","race_id"], na_position="last").iterrows():
        done = int(r.get("resulted") or 0)
        sig_rankings = r.get("sig_rankings")
        if not isinstance(sig_rankings, list):
            sig_rankings = [[-1,-1,-1]] * len(ALL_SIGNALS)
        u_list = r.get("u_list")
        if not isinstance(u_list, list):
            u_list = []
        races.append({
            "d":    str(r.get("date",""))[:10],
            "v":    str(r.get("venue","")),
            "r":    si(r.get("race")),
            "p":    si(r.get("prize_money")),
            "n":    1 if r.get("has_first_starter") else 0,
            "t":    1,
            "done": done,
            "top":  int(r.get("top_idx") or 0),
            "s":    sig_rankings,
            "u":    u_list,
            "ps":   str(r.get("pace_scenario","")) if r.get("pace_scenario") else None,
            "rid":  si(r.get("race_id")),
            "tm":   str(r.get("start_time","")) if r.get("start_time") else None,
        })

    data_js  = "const RACES = " + json.dumps(races, separators=(",",":")) + ";"
    run_date = datetime.now().strftime("%d %b %Y %H:%M")
    n_total  = len(races)
    n_res    = sum(1 for r in races if r["done"] == 1)
    n_pend   = sum(1 for r in races if r["done"] == 0)

    html = f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>TopRate — Live Tracking</title>
<style>
@import url('https://fonts.googleapis.com/css2?family=Space+Mono:wght@400;700&family=Barlow+Condensed:wght@400;700;900&family=Barlow:wght@400;500;600&display=swap');
*{{box-sizing:border-box;margin:0;padding:0;}}
body{{background:#f0f2f5;color:#2c3542;font-family:Barlow,sans-serif;font-size:13px;}}
.shell{{display:grid;grid-template-columns:260px 1fr;min-height:100vh;}}
.sidebar{{background:#1a3a5c;padding:20px 16px;display:flex;flex-direction:column;position:sticky;top:0;height:100vh;overflow-y:auto;}}
.sidebar::-webkit-scrollbar{{width:3px;}}.sidebar::-webkit-scrollbar-thumb{{background:rgba(255,255,255,.2);}}
.mob-bar{{display:none;}}
@media(max-width:768px){{
  .shell{{display:block;}}
  .sidebar{{position:fixed;top:0;left:0;width:88vw;max-width:320px;height:100vh;z-index:200;transform:translateX(-105%);transition:transform .28s cubic-bezier(.4,0,.2,1);box-shadow:4px 0 24px rgba(0,0,0,.3);}}
  .sidebar.open{{transform:translateX(0);}}
  .mob-bar{{display:flex;align-items:center;justify-content:space-between;background:#1a3a5c;padding:12px 16px;position:sticky;top:0;z-index:100;box-shadow:0 2px 8px rgba(0,0,0,.15);}}
  .mob-bar-logo{{font-family:'Barlow Condensed',sans-serif;font-size:22px;font-weight:900;color:#fff;letter-spacing:-1px;}}
  .mob-bar-logo em{{color:#f97316;font-style:normal;}}
  .mob-menu-btn{{background:rgba(255,255,255,.1);border:1px solid rgba(255,255,255,.2);color:#fff;font-size:18px;cursor:pointer;padding:6px 10px;border-radius:4px;line-height:1;}}
  .mob-overlay{{display:none;position:fixed;inset:0;background:rgba(0,0,0,.55);z-index:199;backdrop-filter:blur(2px);}}
  .mob-overlay.open{{display:block;}}
  .main{{padding:10px 10px 80px;}}
  .main-tabs{{margin-bottom:10px;}}
  .main-tab{{padding:8px 14px;font-size:9px;}}
  /* KPI: 3 cols, 2 rows — no overflow */
  .kpi-strip{{grid-template-columns:repeat(3,1fr);gap:3px;margin-bottom:12px;}}
  .kpi{{padding:8px 8px;}}
  .kpi .v{{font-size:18px;}}
  .kpi .l{{font-size:7px;}}
  /* Hide desktop tables */
  .desk-only{{display:none !important;}}
  /* Mobile bet cards */
  .mob-bet-list{{display:flex;flex-direction:column;gap:8px;}}
  .mob-bet-card{{background:#fff;border:1px solid #e2e5ea;border-radius:6px;overflow:hidden;}}
  .mob-bet-card.wr{{border-left:4px solid #2e7d32;background:#f1f8f1;}}
  .mob-bet-card.pr{{border-left:4px solid #1565c0;background:#f0f4ff;}}
  .mob-bet-card.no-bet-card{{opacity:0.5;}}
  .mob-bet-hdr{{display:flex;align-items:center;justify-content:space-between;padding:7px 12px;background:#f5f6f8;border-bottom:1px solid #e2e5ea;}}
  .mob-bet-venue{{font-size:12px;font-weight:700;color:#0f1923;}}
  .mob-bet-date{{font-family:'Space Mono',monospace;font-size:9px;color:#9ca3af;}}
  .mob-bet-body{{padding:10px 12px;}}
  .mob-bet-horse{{font-size:15px;font-weight:700;color:#0f1923;margin-bottom:2px;}}
  .mob-bet-jockey{{font-size:11px;color:#6b7280;margin-bottom:8px;}}
  .mob-bet-row{{display:flex;gap:5px;flex-wrap:wrap;margin-bottom:8px;align-items:center;}}
  .mob-bet-tag{{display:inline-flex;align-items:center;padding:2px 7px;border-radius:3px;font-family:'Space Mono',monospace;font-size:10px;white-space:nowrap;}}
  .mob-bet-tag.score{{background:#fff3e0;color:#e65100;border:1px solid #ffcc80;}}
  .mob-bet-tag.sp{{background:#e8f0fb;color:#1a3a5c;border:1px solid #93b8e0;}}
  .mob-bet-tag.mkt{{background:#e8f5e9;color:#2e7d32;border:1px solid #a5d6a7;font-weight:700;}}
  .mob-bet-tag.wpr{{background:#f5f6f8;color:#374151;border:1px solid #d1d5db;}}
  .mob-bet-tag.prize{{background:#f5f6f8;color:#6b7280;border:1px solid #e2e5ea;}}
  .mob-bet-footer{{display:flex;align-items:center;gap:8px;padding:8px 12px;border-top:1px solid #f0f2f5;flex-wrap:wrap;}}
  .mob-fixed-inp{{width:70px;font-family:'Space Mono',monospace;font-size:12px;border:1px solid #f0c040;border-radius:4px;padding:4px 6px;text-align:center;background:#fffde7;color:#92400e;outline:none;}}
  .mob-fixed-inp.has-val{{background:#fff7ed;border-color:#fb923c;color:#c2410c;font-weight:700;}}
  .mob-res-inp{{width:44px;font-family:'Space Mono',monospace;font-size:12px;border:1px solid #d1d5db;border-radius:4px;padding:4px 6px;text-align:center;background:#f0fdf4;outline:none;}}
  .mob-stake-lbl{{font-family:'Space Mono',monospace;font-size:11px;color:#6b7280;margin-left:auto;}}
  /* Quaddie: single column, legs stack vertically */
  .q-legs{{display:grid !important;grid-template-columns:1fr !important;}}
  .q-leg{{border-right:none !important;border-bottom:1px solid #e2e5ea;width:100% !important;}}
  .q-meeting{{margin-bottom:16px;}}
  .q-meeting-hdr{{flex-wrap:wrap;gap:4px;}}
  .q-cost-bar{{flex-wrap:wrap;gap:8px;}}
  .q-runner-name{{font-size:13px;}}
}}
.logo{{font-family:'Barlow Condensed',sans-serif;font-size:24px;font-weight:900;letter-spacing:-1px;color:#fff;margin-bottom:2px;}}
.logo em{{color:#f97316;font-style:normal;}}
.logo-sub{{font-family:'Space Mono',monospace;font-size:9px;color:rgba(255,255,255,.4);letter-spacing:.1em;margin-bottom:20px;}}
.fsec{{margin-bottom:16px;}}
.ftitle{{font-family:'Space Mono',monospace;font-size:9px;text-transform:uppercase;letter-spacing:.14em;color:rgba(255,255,255,.4);margin-bottom:8px;padding-bottom:5px;border-bottom:1px solid rgba(255,255,255,.1);}}
.trow{{display:flex;align-items:center;justify-content:space-between;padding:5px 0;}}
.tlbl{{font-size:12px;color:rgba(255,255,255,.85);}}
.tog{{position:relative;width:34px;height:18px;cursor:pointer;flex-shrink:0;}}
.tog input{{opacity:0;width:0;height:0;}}
.tog-track{{position:absolute;inset:0;background:rgba(255,255,255,.2);border-radius:9px;transition:background .2s;}}
.tog input:checked+.tog-track{{background:#f97316;}}
.tog-thumb{{position:absolute;top:2px;left:2px;width:14px;height:14px;background:#fff;border-radius:50%;transition:transform .2s;box-shadow:0 1px 3px rgba(0,0,0,.3);}}
.tog input:checked~.tog-thumb{{transform:translateX(16px);}}
.srow{{margin-bottom:12px;}}
.shdr{{display:flex;justify-content:space-between;align-items:baseline;margin-bottom:5px;}}
.slbl{{font-size:12px;color:rgba(255,255,255,.85);}}
.sval{{font-family:'Space Mono',monospace;font-size:12px;color:#f97316;font-weight:700;}}
input[type=range]{{width:100%;height:3px;-webkit-appearance:none;appearance:none;background:rgba(255,255,255,.2);border-radius:2px;outline:none;cursor:pointer;}}
input[type=range]::-webkit-slider-thumb{{-webkit-appearance:none;width:14px;height:14px;border-radius:50%;background:#f97316;cursor:pointer;}}
input[type=range]::-moz-range-thumb{{width:14px;height:14px;border-radius:50%;background:#f97316;border:none;cursor:pointer;}}
.dow-grid{{display:grid;grid-template-columns:1fr 1fr;gap:3px;}}
.dow-cb{{display:flex;align-items:center;gap:5px;cursor:pointer;padding:3px 5px;border-radius:3px;}}
.dow-cb input{{cursor:pointer;accent-color:#f97316;width:12px;height:12px;}}
.dow-cb span{{font-size:11px;color:rgba(255,255,255,.75);}}
.qbtns{{display:flex;gap:4px;margin-bottom:8px;}}
.qbtn{{flex:1;padding:4px 0;font-family:'Space Mono',monospace;font-size:9px;text-transform:uppercase;cursor:pointer;border:1px solid rgba(255,255,255,.2);background:rgba(255,255,255,.07);color:rgba(255,255,255,.6);border-radius:2px;}}
.qbtn:hover{{background:rgba(255,255,255,.14);color:rgba(255,255,255,.9);}}
.mth-btns{{display:grid;grid-template-columns:1fr 1fr 1fr;gap:3px;margin-bottom:10px;}}
.mb{{padding:6px 4px;font-size:10px;font-family:'Space Mono',monospace;text-align:center;cursor:pointer;border:1px solid rgba(255,255,255,.15);background:rgba(255,255,255,.06);color:rgba(255,255,255,.55);border-radius:2px;line-height:1.3;}}
.mb.active{{background:#f97316;border-color:#f97316;color:#fff;font-weight:700;}}
.mb:hover:not(.active){{background:rgba(255,255,255,.12);color:rgba(255,255,255,.85);}}
.reset-btn{{width:100%;padding:9px;background:rgba(255,255,255,.08);border:1px solid rgba(255,255,255,.18);color:rgba(255,255,255,.55);font-family:'Space Mono',monospace;font-size:9px;text-transform:uppercase;letter-spacing:.1em;cursor:pointer;border-radius:2px;margin-bottom:8px;}}
.reset-btn:hover{{background:rgba(255,255,255,.16);color:#fff;}}
.run-info{{font-family:'Space Mono',monospace;font-size:9px;color:rgba(255,255,255,.3);margin-top:auto;padding-top:12px;line-height:1.6;}}
.bt-link{{display:block;padding:8px;background:rgba(255,255,255,.08);border:1px solid rgba(255,255,255,.18);color:rgba(255,255,255,.6);font-family:'Space Mono',monospace;font-size:9px;text-transform:uppercase;text-decoration:none;text-align:center;margin-top:8px;}}
.bt-link:hover{{background:rgba(255,255,255,.15);color:#fff;}}
.main{{padding:24px 24px 60px;}}
.kpi-strip{{display:grid;grid-template-columns:repeat(6,1fr);gap:2px;margin-bottom:20px;}}
.kpi{{background:#fff;border:1px solid #e2e5ea;padding:12px 14px;}}
.kpi.hl{{background:#e8f0fb;border-color:#93b8e0;}}
.kpi.neg-kpi{{background:#fff5f5;border-color:#fca5a5;}}
.kpi .v{{font-family:'Barlow Condensed',sans-serif;font-size:30px;font-weight:900;line-height:1;color:#0f1923;}}
.kpi.hl .v{{color:#1a3a5c;}}.kpi.neg-kpi .v{{color:#c62828;}}
.kpi .l{{font-family:'Space Mono',monospace;font-size:9px;color:#9ca3af;text-transform:uppercase;letter-spacing:.08em;margin-top:3px;}}
.st{{font-family:'Space Mono',monospace;font-size:10px;text-transform:uppercase;letter-spacing:.12em;color:#9ca3af;margin:16px 0 8px;display:flex;align-items:center;gap:10px;}}
.st::after{{content:'';flex:1;height:1px;background:#e2e5ea;}}
.cnt{{color:#1a3a5c;font-weight:700;margin-left:6px;}}
.card{{background:#fff;border:1px solid #e2e5ea;overflow:hidden;margin-bottom:16px;overflow-x:auto;}}
table{{width:100%;border-collapse:collapse;font-size:12px;}}
thead tr{{background:#f5f6f8;position:sticky;top:0;z-index:2;}}
thead th{{padding:7px 10px;text-align:right;font-family:'Space Mono',monospace;font-size:9px;text-transform:uppercase;letter-spacing:.08em;color:#9ca3af;font-weight:400;border-bottom:2px solid #e2e5ea;white-space:nowrap;}}
thead th:nth-child(-n+4){{text-align:left;}}
tbody tr{{border-bottom:1px solid #e2e5ea;transition:background .08s;}}
tbody tr:hover{{background:#f5f6f8;}}
tbody tr.wr{{background:#e8f5e9;}}tbody tr.wr:hover{{background:#c8e6c9;}}
tbody tr.pr{{background:#e3f2fd;}}tbody tr.pr:hover{{background:#bbdefb;}}
td{{padding:7px 10px;text-align:right;vertical-align:middle;}}
td:nth-child(-n+4){{text-align:left;}}
.mn{{font-family:'Space Mono',monospace;font-size:11px;}}
.br{{color:#0f1923;font-weight:700;}}.dm{{color:#9ca3af;}}
.pill{{display:inline-block;padding:1px 7px;font-family:'Space Mono',monospace;font-size:9px;font-weight:700;border-radius:2px;}}
.pw{{background:#e8f5e9;color:#2e7d32;border:1px solid #a5d6a7;}}
.pp{{background:#e3f2fd;color:#1565c0;border:1px solid #90caf9;}}
.pl{{background:#f5f6f8;color:#9ca3af;border:1px solid #e2e5ea;}}
.pd{{background:#fff8e1;color:#f57f17;border:1px solid #ffe082;}}
.tc{{font-family:'Space Mono',monospace;font-size:10px;padding:1px 5px;border-radius:2px;}}
.tp{{background:#e8f5e9;color:#2e7d32;}}.tn{{background:#ffebee;color:#c62828;}}.tz{{color:#9ca3af;}}
.rp{{color:#2e7d32;font-family:'Space Mono',monospace;font-size:11px;font-weight:700;}}
.rn{{color:#9ca3af;font-family:'Space Mono',monospace;font-size:11px;}}
.cp{{color:#2e7d32;font-family:'Space Mono',monospace;font-size:11px;}}
.cn{{color:#c62828;font-family:'Space Mono',monospace;font-size:11px;}}
.empty{{padding:40px;text-align:center;color:#9ca3af;font-family:'Space Mono',monospace;font-size:12px;}}
.ctx{{display:inline-block;padding:1px 6px;font-size:10px;border-radius:2px;margin-right:3px;cursor:default;}}
.ctx-good{{background:#e8f5e9;color:#2e7d32;border:1px solid #c8e6c9;}}
.ctx-warn{{background:#fff3e0;color:#e65100;border:1px solid #ffcc80;}}
.ctx-neut{{background:#f5f6f8;color:#6b7280;border:1px solid #e2e5ea;}}
.sig-grid{{display:grid;grid-template-columns:1fr 1fr;gap:3px;margin-bottom:8px;}}
.sig-cb{{display:flex;align-items:center;gap:5px;cursor:pointer;padding:3px 5px;border-radius:3px;transition:background .1s;}}
.sig-cb:hover{{background:rgba(255,255,255,.08);}}
.sig-cb input{{cursor:pointer;accent-color:#f97316;width:12px;height:12px;}}
.sig-cb span{{font-size:10px;color:rgba(255,255,255,.75);font-family:'Space Mono',monospace;}}
.sig-cb.dir-h span{{color:rgba(180,224,140,.85);}}
.sig-cb.dir-l span{{color:rgba(140,180,224,.85);}}
.sig-sel-btns{{display:flex;gap:4px;margin-bottom:8px;}}
.sig-btn{{flex:1;padding:4px 0;font-family:'Space Mono',monospace;font-size:9px;text-transform:uppercase;cursor:pointer;border:1px solid rgba(255,255,255,.2);background:rgba(255,255,255,.07);color:rgba(255,255,255,.6);border-radius:2px;}}
.sig-btn:hover{{background:rgba(255,255,255,.14);color:rgba(255,255,255,.9);}}
.fixed-inp{{width:58px;font-family:'Space Mono',monospace;font-size:11px;border:1px solid #d1d5db;border-radius:3px;padding:2px 5px;text-align:center;background:#fffbeb;color:#92400e;outline:none;}}
.fixed-inp:focus{{border-color:#f97316;background:#fff7ed;}}
.fixed-inp.has-val{{background:#fff7ed;border-color:#fb923c;color:#c2410c;font-weight:700;}}
.bet-tog{{width:32px;height:22px;border:none;border-radius:4px;font-size:11px;font-weight:700;cursor:pointer;transition:background .15s,color .15s;}}
.bet-y{{background:#16a34a;color:#fff;}}
.bet-n{{background:#e5e7eb;color:#6b7280;}}
.no-bet-row td{{opacity:0.45;}}
.date-inp{{width:100%;background:rgba(255,255,255,.08);border:1px solid rgba(255,255,255,.18);color:rgba(255,255,255,.85);font-family:'Space Mono',monospace;font-size:10px;padding:5px 7px;border-radius:2px;outline:none;cursor:pointer;}}
.date-inp:focus{{border-color:#f97316;background:rgba(255,255,255,.12);}}
.date-inp::-webkit-calendar-picker-indicator{{filter:invert(1);opacity:0.5;cursor:pointer;}}
.main-tabs{{display:flex;gap:0;margin-bottom:20px;border-bottom:2px solid #e2e5ea;}}
.main-tab{{padding:10px 20px;font-family:'Space Mono',monospace;font-size:10px;text-transform:uppercase;letter-spacing:.1em;cursor:pointer;border:none;background:none;color:#9ca3af;border-bottom:2px solid transparent;margin-bottom:-2px;transition:color .15s;}}
.main-tab.active{{color:#1a3a5c;border-bottom-color:#f97316;font-weight:700;}}
.main-tab:hover:not(.active){{color:#1a3a5c;}}
.tab-panel{{display:none;}}.tab-panel.active{{display:block;}}
.q-meeting{{background:#fff;border:1px solid #e2e5ea;margin-bottom:24px;}}
.q-meeting-hdr{{background:#1a3a5c;color:#fff;padding:10px 16px;display:flex;align-items:center;justify-content:space-between;}}
.q-meeting-name{{font-family:'Barlow Condensed',sans-serif;font-size:18px;font-weight:900;letter-spacing:-.5px;}}
.q-meeting-date{{font-family:'Space Mono',monospace;font-size:9px;color:rgba(255,255,255,.5);}}
.q-cost-bar{{background:#f0f2f5;border-bottom:1px solid #e2e5ea;padding:8px 16px;display:flex;align-items:center;gap:16px;flex-wrap:wrap;}}
.q-cost-lbl{{font-family:'Space Mono',monospace;font-size:10px;color:#6b7280;text-transform:uppercase;letter-spacing:.08em;}}
.q-cost-val{{font-family:'Barlow Condensed',sans-serif;font-size:22px;font-weight:900;color:#1a3a5c;}}
.q-cost-combos{{font-family:'Space Mono',monospace;font-size:10px;color:#9ca3af;}}
.q-stake-wrap{{margin-left:auto;display:flex;align-items:center;gap:8px;}}
.q-stake-inp{{width:64px;font-family:'Space Mono',monospace;font-size:12px;border:1px solid #d1d5db;border-radius:3px;padding:4px 6px;text-align:center;}}
.q-legs{{display:grid;grid-template-columns:repeat(4,1fr);gap:0;border-top:1px solid #e2e5ea;}}
.q-leg{{border-right:1px solid #e2e5ea;padding:0;}}
.q-leg:last-child{{border-right:none;}}
.q-leg-hdr{{background:#f5f6f8;padding:8px 12px;border-bottom:1px solid #e2e5ea;display:flex;align-items:center;justify-content:space-between;}}
.q-leg-title{{font-family:'Space Mono',monospace;font-size:9px;text-transform:uppercase;letter-spacing:.1em;color:#6b7280;}}
.q-leg-race{{font-family:'Barlow Condensed',sans-serif;font-size:16px;font-weight:900;color:#1a3a5c;}}
.q-runner{{display:flex;align-items:center;gap:0;padding:7px 10px;border-bottom:1px solid #f0f2f5;cursor:pointer;transition:background .08s;}}
.q-runner:hover{{background:#f5f6f8;}}
.q-runner.selected{{background:#fff8f0;}}
.q-runner.banker{{background:#fff3e0;}}
.q-runner input[type=checkbox]{{margin-right:8px;accent-color:#f97316;width:13px;height:13px;cursor:pointer;flex-shrink:0;}}
.q-runner-name{{font-size:12px;font-weight:600;color:#0f1923;flex:1;min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;}}
.q-runner-score{{font-family:'Space Mono',monospace;font-size:10px;color:#f97316;font-weight:700;margin-left:4px;flex-shrink:0;}}
.q-runner-sp{{font-family:'Space Mono',monospace;font-size:9px;color:#9ca3af;margin-left:4px;flex-shrink:0;}}
.q-runner-top{{margin-left:4px;flex-shrink:0;}}
.q-pill{{display:inline-block;padding:1px 5px;font-family:'Space Mono',monospace;font-size:8px;font-weight:700;border-radius:2px;}}
.q-pill-1{{background:#fff3cd;color:#856404;border:1px solid #ffc107;}}
.q-pill-2{{background:#e8f5e9;color:#2e7d32;border:1px solid #a5d6a7;}}
.q-pill-3{{background:#e3f2fd;color:#1565c0;border:1px solid #90caf9;}}
.q-sigs{{padding:8px 12px;}}
.q-sig-row{{display:flex;align-items:center;justify-content:space-between;padding:2px 0;border-bottom:1px solid #f8f9fa;}}
.q-sig-row:last-child{{border-bottom:none;}}
.q-sig-name{{font-family:'Space Mono',monospace;font-size:9px;color:#6b7280;}}
.q-sig-top3{{display:flex;gap:3px;}}
.q-sig-horse{{font-size:10px;color:#1a3a5c;max-width:90px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;}}
.q-no-meeting{{padding:40px;text-align:center;color:#9ca3af;font-family:'Space Mono',monospace;font-size:11px;}}
.q-sig-toggle{{padding:6px 12px;font-family:var(--mono,monospace);font-size:9px;color:#9ca3af;cursor:pointer;list-style:none;text-transform:uppercase;letter-spacing:.08em;}}
.q-sig-toggle::-webkit-details-marker{{display:none;}}
.q-pend-tag{{font-family:'Space Mono',monospace;font-size:8px;padding:1px 5px;border-radius:2px;background:#fff8e1;color:#f57f17;border:1px solid #ffe082;}}
</style>
</head>
<body>
<div class="mob-overlay" id="mob-overlay" onclick="closeSidebar()"></div>
<div class="mob-bar">
  <div class="mob-bar-logo">Top<em>Rate</em></div>
  <button class="mob-menu-btn" onclick="toggleSidebar()">&#9776;</button>
</div>
<div class="shell">
<div class="sidebar">
  <div class="logo">Top<em>Rate</em></div>
  <div class="logo-sub">LIVE TRACKING</div>

  <div class="fsec">
    <div class="ftitle">Race filters</div>
    <div class="trow"><span class="tlbl">TAB races only</span>
      <label class="tog"><input type="checkbox" id="f-tab" checked><div class="tog-track"></div><div class="tog-thumb"></div></label></div>
    <div class="srow" style="margin-top:6px">
      <div class="shdr"><span class="slbl">Min prize money</span><span class="sval" id="v-prize">$25k</span></div>
      <input type="range" id="f-prize" min="0" max="100000" step="5000" value="25000">
    </div>
    <div class="trow"><span class="tlbl">Exclude first starters</span>
      <label class="tog"><input type="checkbox" id="f-nofs" checked><div class="tog-track"></div><div class="tog-thumb"></div></label></div>
    <div class="trow"><span class="tlbl">Trend &gt; 0 only</span>
      <label class="tog"><input type="checkbox" id="f-trend" checked><div class="tog-track"></div><div class="tog-thumb"></div></label></div>
  </div>

  <div class="fsec">
    <div class="ftitle">Context filters</div>
    <div class="trow"><span class="tlbl">Exclude wide (barrier &gt; 8)</span>
      <label class="tog"><input type="checkbox" id="f-nowide"><div class="tog-track"></div><div class="tog-thumb"></div></label></div>
    <div class="srow" style="margin-top:6px">
      <div class="shdr"><span class="slbl">Max barrier</span><span class="sval" id="v-barrier">Any</span></div>
      <input type="range" id="f-barrier" min="1" max="16" step="1" value="16">
    </div>
    <div style="margin-top:6px"><div class="ftitle" style="margin-bottom:5px">Settling</div>
      <div class="dow-grid">
        <label class="dow-cb"><input type="checkbox" data-settle="leader" checked><span>Leader</span></label>
        <label class="dow-cb"><input type="checkbox" data-settle="on-pace" checked><span>On-pace</span></label>
        <label class="dow-cb"><input type="checkbox" data-settle="midfield" checked><span>Midfield</span></label>
        <label class="dow-cb"><input type="checkbox" data-settle="backmarker" checked><span>Backmarker</span></label>
        <label class="dow-cb"><input type="checkbox" data-settle="unknown" checked><span>Unknown</span></label>
      </div>
    </div>
    <div style="margin-top:6px"><div class="ftitle" style="margin-bottom:5px">Pace scenario</div>
      <div class="dow-grid">
        <label class="dow-cb"><input type="checkbox" data-pace="slow" checked><span>Slow</span></label>
        <label class="dow-cb"><input type="checkbox" data-pace="neutral" checked><span>Neutral</span></label>
        <label class="dow-cb"><input type="checkbox" data-pace="fast" checked><span>Fast</span></label>
        <label class="dow-cb"><input type="checkbox" data-pace="unknown" checked><span>Unknown</span></label>
      </div>
    </div>
  </div>

  <div class="fsec">
    <div class="ftitle">Price filter</div>
    <div class="srow">
      <div class="shdr"><span class="slbl">Min SP</span><span class="sval" id="v-sp">$2.50</span></div>
      <input type="range" id="f-sp" min="1" max="10" step="0.5" value="2.5">
    </div>
    <div class="srow">
      <div class="shdr"><span class="slbl">Max SP</span><span class="sval" id="v-spmax">Any</span></div>
      <input type="range" id="f-spmax" min="3" max="30" step="1" value="30">
    </div>
  </div>

  <div class="fsec">
    <div class="ftitle">Day of week</div>
    <div class="qbtns">
      <button class="qbtn" onclick="setDow('all')">All</button>
      <button class="qbtn" onclick="setDow('weekend')">Sat/Sun</button>
      <button class="qbtn" onclick="setDow('mid')">Mid</button>
    </div>
    <div class="dow-grid" id="dow-grid">
      <label class="dow-cb"><input type="checkbox" data-dow="1" checked><span>Monday</span></label>
      <label class="dow-cb"><input type="checkbox" data-dow="2" checked><span>Tuesday</span></label>
      <label class="dow-cb"><input type="checkbox" data-dow="3" checked><span>Wednesday</span></label>
      <label class="dow-cb"><input type="checkbox" data-dow="4" checked><span>Thursday</span></label>
      <label class="dow-cb"><input type="checkbox" data-dow="5" checked><span>Friday</span></label>
      <label class="dow-cb"><input type="checkbox" data-dow="6" checked><span>Saturday</span></label>
      <label class="dow-cb"><input type="checkbox" data-dow="0" checked><span>Sunday</span></label>
    </div>
  </div>

  <div class="fsec">
    <div class="ftitle">Staking method</div>
    <div class="mth-btns">
      <button class="mb active" id="s-flat" onclick="setStake('flat')">Flat<br>1u</button>
      <button class="mb" id="s-fixed" onclick="setStake('fixed')">Fixed<br>return</button>
      <button class="mb" id="s-prop" onclick="setStake('prop')">Signal<br>prop</button>
    </div>
    <div id="s-fixed-wrap" style="display:none" class="srow">
      <div class="shdr"><span class="slbl">Target return</span><span class="sval" id="v-target">4.0u</span></div>
      <input type="range" id="f-target" min="1" max="10" step="0.5" value="4">
    </div>
  </div>

  <div class="fsec">
    <div class="ftitle">Scoring method</div>
    <div class="mth-btns">
      <button class="mb active" id="m-top1" onclick="setMethod('top1')">Top 1<br>only</button>
      <button class="mb" id="m-top3c" onclick="setMethod('top3c')">Top 3<br>count</button>
      <button class="mb" id="m-top3w" onclick="setMethod('top3w')">Top 3<br>weighted</button>
    </div>
    <div class="srow">
      <div class="shdr"><span class="slbl" id="thresh-label">Min votes (of 14)</span><span class="sval" id="v-votes">7</span></div>
      <input type="range" id="f-votes" min="1" max="14" value="7">
    </div>
  </div>

  <div class="fsec">
    <div class="ftitle">Signals <span style="font-size:8px;color:rgba(255,255,255,.3);margin-left:4px;">&#8593; higher better &nbsp; &#8595; lower better</span></div>
    <div class="sig-sel-btns">
      <button class="sig-btn" onclick="selectAllSigs()">All</button>
      <button class="sig-btn" onclick="selectNoneSigs()">None</button>
      <button class="sig-btn" onclick="selectOptimalSigs()">Optimal</button>
    </div>
    <div class="sig-grid" id="sig-grid"></div>
  </div>

  <div class="fsec">
    <div class="ftitle">Date range</div>
    <div class="qbtns">
      <button class="qbtn" onclick="setDateRange('today')">Today</button>
      <button class="qbtn" onclick="setDateRange('7')">7d</button>
      <button class="qbtn" onclick="setDateRange('30')">30d</button>
      <button class="qbtn" onclick="setDateRange('all')">All</button>
    </div>
    <div class="srow" style="margin-bottom:6px">
      <div class="slbl" style="margin-bottom:4px;font-size:11px;">From</div>
      <input type="date" class="date-inp" id="f-date-from">
    </div>
    <div class="srow">
      <div class="slbl" style="margin-bottom:4px;font-size:11px;">To</div>
      <input type="date" class="date-inp" id="f-date-to">
    </div>
  </div>

  <div class="fsec">
    <div class="ftitle">View</div>
    <div class="trow"><span class="tlbl">Show pending</span>
      <label class="tog"><input type="checkbox" id="f-pend" checked><div class="tog-track"></div><div class="tog-thumb"></div></label></div>
    <div class="trow"><span class="tlbl">Resulted only</span>
      <label class="tog"><input type="checkbox" id="f-resonly"><div class="tog-track"></div><div class="tog-thumb"></div></label></div>
  </div>

  <button class="reset-btn" onclick="resetAll()">&#8635; Reset to optimal</button>
  <button class="reset-btn" style="color:rgba(100,200,100,.8);border-color:rgba(100,200,100,.3);" onclick="showSyncSetup()">&#8645; Sync setup</button>
  <button class="reset-btn" style="color:rgba(100,200,100,.8);border-color:rgba(100,200,100,.3);" id="sync-now-btn" onclick="syncNow()">&#8635; Sync now</button>
  <button class="reset-btn" style="color:#f97316;border-color:rgba(249,115,22,.4);font-weight:700;" id="run-script-btn" onclick="runScript()">&#9654; Run script</button>
  <div id="run-status" style="font-size:9px;color:rgba(255,255,255,.5);margin-top:2px;text-align:center;word-break:break-all;line-height:1.4;"></div>
  <div id="sync-status" style="font-size:9px;color:rgba(255,255,255,.5);margin-top:4px;text-align:center;word-break:break-all;line-height:1.4;"></div>
  <div class="run-info">Updated {run_date}<br>{n_total} races &middot; {n_res} resulted &middot; {n_pend} pending</div>
  <a class="bt-link" href="toprate_interactive.html">&#8592; 42-day backtest</a>
</div>
<div class="main">
  <div class="main-tabs">
    <button class="main-tab active" id="tab-bets" onclick="switchTab('bets')">Bets</button>
    <button class="main-tab" id="tab-quaddie" onclick="switchTab('quaddie')">Quaddie</button>
  </div>
  <div class="tab-panel active" id="panel-bets">
  <div class="kpi-strip">
    <div class="kpi hl"><div class="v" id="k-roi">—</div><div class="l">ROI</div></div>
    <div class="kpi"><div class="v" id="k-bets">0</div><div class="l">Bets resulted</div></div>
    <div class="kpi"><div class="v" id="k-wins">0</div><div class="l">Wins</div></div>
    <div class="kpi"><div class="v" id="k-wp">—</div><div class="l">Win rate</div></div>
    <div class="kpi"><div class="v" id="k-pp">—</div><div class="l">Place rate</div></div>
    <div class="kpi"><div class="v" id="k-profit">—</div><div class="l" id="k-profit-l">Profit</div></div>
  </div>
  <div class="st" id="pend-title" style="display:none">Pending <span class="cnt" id="pend-cnt"></span></div>
  <div class="card desk-only" id="pend-card" style="display:none">
    <table><thead><tr>
      <th>Date</th><th>Time</th><th>Venue</th><th>Horse</th><th>Jockey</th>
      <th>Sigs</th><th>SP</th><th>Mkt $</th><th>Fixed $</th><th>Prize</th><th>WPR</th><th>Trend</th><th>Context</th><th>Bet?</th><th>Stake</th><th>Result</th>
    </tr></thead><tbody id="pend-tb"></tbody></table>
  </div>
  <div class="mob-bet-list" id="pend-mob" style="display:none"></div>
  <div class="st">Resulted bets <span class="cnt" id="res-cnt"></span></div>
  <div class="card desk-only" id="res-card">
    <table><thead><tr>
      <th>Date</th><th>Time</th><th>Venue</th><th>Horse</th><th>Jockey</th>
      <th>Sigs</th><th>SP</th><th>Fixed</th><th>Prize</th><th>WPR</th><th>Trend</th>
      <th>Context</th><th>Bet?</th><th>Stake</th><th>Result</th><th>P&amp;L</th><th>Cumul</th>
    </tr></thead><tbody id="tb"></tbody></table>
    <div class="empty" id="empty">No resulted bets match current filters</div>
  </div>
  <div class="mob-bet-list" id="res-mob"></div>
  </div><!-- end panel-bets -->
  <div class="tab-panel" id="panel-quaddie">
    <div id="q-content"><div class="q-no-meeting">Loading quaddie data...</div></div>
  </div>
</div><!-- end main -->
</div><!-- end shell -->
<script>
{data_js}
const SIG_NAMES  = ["wpr_nett","wpr_last1","wpr_avg_last3","jky_win90","trn_win365","tr_rating","speed","sp","wpr_rank","peak_rank","consistency","tr_price","fixed_price","price_top"];
const SIG_DIR    = [1,1,1,1,1,1,1,0,0,0,0,0,0,0];
const SIG_LABELS = ["wpr_nett ↑","wpr_last1 ↑","wpr_avg3 ↑","jky_win90 ↑","trn_win365 ↑","tr_rating ↑","speed ↑","sp ↓","wpr_rank ↓","peak_rank ↓","consistency ↓","tr_price ↓","fixed_price ↓","price_top ↓"];
let activeSigs=new Set(SIG_NAMES);
let stakeMethod='flat';
let method='top1';

function dateToDow(d){{const p=d.split('-');return new Date(parseInt(p[0]),parseInt(p[1])-1,parseInt(p[2])).getDay();}}
function fmtTime(tm){{
  if(!tm)return'';
  try{{
    const d=new Date(tm);
    // Format in local browser time (iPhone/desktop will show correct local time)
    return d.toLocaleTimeString([],{{hour:'2-digit',minute:'2-digit',hour12:true}});
  }}catch(e){{return'';}}
}}
function getActiveDows(){{const s=new Set();document.querySelectorAll('#dow-grid input:checked').forEach(cb=>s.add(parseInt(cb.dataset.dow)));return s;}}
function setDow(mode){{document.querySelectorAll('#dow-grid input').forEach(cb=>{{const d=parseInt(cb.dataset.dow);cb.checked=mode==='all'?true:mode==='weekend'?(d===0||d===6):(d>=1&&d<=5);}});update();}}
function setStake(m){{stakeMethod=m;['s-flat','s-fixed','s-prop'].forEach(id=>document.getElementById(id).classList.remove('active'));document.getElementById('s-'+m).classList.add('active');document.getElementById('s-fixed-wrap').style.display=m==='fixed'?'':'none';update();}}
function calcStake(score,maxScore,sp){{if(stakeMethod==='flat')return 1;if(stakeMethod==='fixed'){{const tg=parseFloat(document.getElementById('f-target').value);return sp&&sp>1?Math.max(tg/(sp-1),0.1):1;}}const pct=maxScore>0?score/maxScore:0;return Math.max(0.5,pct*2);}}
function setMethod(m){{
  method=m;
  ['m-top1','m-top3c','m-top3w'].forEach(id=>document.getElementById(id).classList.remove('active'));
  document.getElementById('m-'+m).classList.add('active');
  const slider=document.getElementById('f-votes');
  const lbl=document.getElementById('thresh-label');
  if(m==='top1'){{slider.min=1;slider.max=14;lbl.textContent='Min votes (of '+activeSigs.size+')';}}
  else if(m==='top3c'){{slider.min=1;slider.max=activeSigs.size;if(parseInt(slider.value)>activeSigs.size)slider.value=activeSigs.size;lbl.textContent='Min score per horse (1pt/top-3, max '+activeSigs.size+')';}}
  else{{slider.min=1;slider.max=activeSigs.size*3;if(parseInt(slider.value)<Math.round(activeSigs.size*1.5))slider.value=Math.round(activeSigs.size*1.5);lbl.textContent='Min score per horse (3/2/1pts, max '+activeSigs.size*3+')';}}
  document.getElementById('v-votes').textContent=slider.value;
  update();
}}
function rebuildActiveSigs(){{activeSigs=new Set();document.querySelectorAll('#sig-grid input:checked').forEach(cb=>activeSigs.add(cb.dataset.sig));}}
function selectAllSigs(){{document.querySelectorAll('#sig-grid input').forEach(cb=>cb.checked=true);rebuildActiveSigs();update();}}
function selectNoneSigs(){{document.querySelectorAll('#sig-grid input').forEach(cb=>cb.checked=false);rebuildActiveSigs();update();}}
function selectOptimalSigs(){{const exclude=new Set(['sp','fixed_price','price_top']);document.querySelectorAll('#sig-grid input').forEach(cb=>{{cb.checked=!exclude.has(cb.dataset.sig);}});rebuildActiveSigs();update();}}
(function(){{
  const grid=document.getElementById('sig-grid');
  SIG_NAMES.forEach((sig,i)=>{{
    const isH=SIG_DIR[i]===1;
    const cb=document.createElement('label');
    cb.className='sig-cb '+(isH?'dir-h':'dir-l');
    cb.innerHTML='<input type="checkbox" data-sig="'+sig+'" checked><span>'+SIG_LABELS[i]+'</span>';
    cb.querySelector('input').addEventListener('change',()=>{{rebuildActiveSigs();update();}});
    grid.appendChild(cb);
  }});
}})();
function scoreRace(race){{
  const scores=new Array(race.u.length).fill(0);
  SIG_NAMES.forEach((sig,si)=>{{
    if(!activeSigs.has(sig))return;
    const [r1,r2,r3]=race.s[si];
    if(method==='top1'){{if(r1>=0)scores[r1]+=1;}}
    else if(method==='top3c'){{if(r1>=0)scores[r1]+=1;if(r2>=0)scores[r2]+=1;if(r3>=0)scores[r3]+=1;}}
    else{{if(r1>=0)scores[r1]+=3;if(r2>=0)scores[r2]+=2;if(r3>=0)scores[r3]+=1;}}
  }});
  let topIdx=-1,topScore=0;
  scores.forEach((s,i)=>{{if(s>topScore){{topScore=s;topIdx=i;}}}});
  return {{topIdx,topScore,scores}};
}}
function getF(){{return{{
  tab:document.getElementById('f-tab').checked,
  prize:parseInt(document.getElementById('f-prize').value),
  nofs:document.getElementById('f-nofs').checked,
  trend:document.getElementById('f-trend').checked,
  sp:parseFloat(document.getElementById('f-sp').value),
  spmax:parseFloat(document.getElementById('f-spmax').value),
  votes:parseFloat(document.getElementById('f-votes').value),
  pend:document.getElementById('f-pend').checked,
  resonly:document.getElementById('f-resonly').checked,
  nowide:document.getElementById('f-nowide').checked,
  barrier:parseInt(document.getElementById('f-barrier').value),
  dateFrom:document.getElementById('f-date-from').value||'',
  dateTo:document.getElementById('f-date-to').value||'',
}};}}
function setDateRange(mode){{
  const today=new Date();
  // Use local date (not UTC) — toISOString() can return yesterday in AEST
  const fmt=d=>{{
    const y=d.getFullYear();
    const m=String(d.getMonth()+1).padStart(2,'0');
    const day=String(d.getDate()).padStart(2,'0');
    return y+'-'+m+'-'+day;
  }};
  const toEl=document.getElementById('f-date-to');
  const fromEl=document.getElementById('f-date-from');
  toEl.value=fmt(today);
  if(mode==='today'){{fromEl.value=fmt(today);}}
  else if(mode==='7'){{const d=new Date(today);d.setDate(d.getDate()-6);fromEl.value=fmt(d);}}
  else if(mode==='30'){{const d=new Date(today);d.setDate(d.getDate()-29);fromEl.value=fmt(d);}}
  else{{fromEl.value='';toEl.value='';}}
  update();
}}function getActiveSettle(){{const s=new Set();document.querySelectorAll('[data-settle]:checked').forEach(cb=>s.add(cb.dataset.settle));return s;}}
function getActivePace(){{const s=new Set();document.querySelectorAll('[data-pace]:checked').forEach(cb=>s.add(cb.dataset.pace));return s;}}
function fmtPrize(p){{return p?'$'+(p/1000).toFixed(0)+'k':'—';}}
function ctxHtml(runner,race){{
  const st=runner.st||'unknown';
  const ps=race.ps||runner.ps||'unknown';
  const bar=runner.b;
  const stCls=st==='leader'?'ctx-good':st==='on-pace'?'ctx-good':st==='midfield'?'ctx-neut':'ctx-warn';
  const psCls=ps==='slow'?'ctx-good':ps==='neutral'?'ctx-neut':ps==='fast'?'ctx-warn':'ctx-neut';
  let h='<span class="ctx '+stCls+'">'+st+'</span><span class="ctx '+psCls+'">'+ps+'</span>';
  if(bar)h+='<span class="ctx ctx-neut">b'+bar+'</span>';
  return h;
}}
function trendHtml(t){{if(t===null||t===undefined)return'<span class="tc tz">—</span>';return t>0?'<span class="tc tp">+'+t.toFixed(1)+'</span>':'<span class="tc tn">'+t.toFixed(1)+'</span>';}}
function buildBets(f){{
  const activeDows=getActiveDows();
  const activeSettle=getActiveSettle();
  const activePace=getActivePace();
  const maxScore=method==='top1'?activeSigs.size:method==='top3c'?activeSigs.size:activeSigs.size*3;
  const resulted=[],pending=[];
  RACES.forEach(race=>{{
    if(f.tab&&!race.t)return;
    if(f.prize>0&&race.p<f.prize)return;
    if(f.nofs&&race.n)return;
    if(f.dateFrom&&race.d<f.dateFrom)return;
    if(f.dateTo&&race.d>f.dateTo)return;
    if(activeDows.size<7){{const dow=dateToDow(race.d);if(!activeDows.has(dow))return;}}
    const {{topIdx,topScore,scores}}=scoreRace(race);
    if(topIdx<0||topScore<f.votes)return;
    // In top1 mode: emit only the race leader (original behaviour).
    // In top3c/top3w modes: emit every runner whose individual score meets the threshold.
    const candidateIdxs=method==='top1'
      ?[topIdx]
      :scores.map((s,i)=>s>=f.votes?i:-1).filter(i=>i>=0);
    candidateIdxs.forEach(idx=>{{
      const runner=race.u[idx];
      if(!runner)return;
      const sp=runner.sp;
      if(race.done===0){{if(sp!==null&&sp!==undefined&&(sp<f.sp||sp>f.spmax))return;}}
      else{{if(!sp||sp<f.sp||sp>f.spmax)return;}}
      if(f.trend&&(runner.tr===null||runner.tr===undefined||runner.tr<=0))return;
      if(f.nowide&&runner.b&&runner.b>8)return;
      if(f.barrier<16&&runner.b&&runner.b>f.barrier)return;
      const st=runner.st||'unknown';
      const ps=race.ps||runner.ps||'unknown';
      if(activeSettle.size<5&&!activeSettle.has(st))return;
      if(activePace.size<4&&!activePace.has(ps))return;
      const runnerScore=scores[idx];
      const stake=calcStake(runnerScore,maxScore,sp);
      const scoreDisp=method==='top1'?runnerScore+'/'+activeSigs.size:method==='top3c'?runnerScore+'/'+activeSigs.size:runnerScore+'/'+(activeSigs.size*3);
      // For pending races, check if user has manually entered a result or toggled bet off
      const _betKey='bet|'+race.d+'|'+race.v+'|'+race.r+'|'+runner.h;
      const _resKey='res|'+race.d+'|'+race.v+'|'+race.r+'|'+runner.h;
      const _betStored=syncGet(_betKey);
      const isBet=_betStored===null?true:_betStored==='1';
      const _manualResStored=syncGet(_resKey);
      const manualFinish=_manualResStored?parseInt(_manualResStored):null;
      // Use manual finish if available (pending race only), otherwise use API finish
      const effectiveFinish=race.done===0&&manualFinish!==null?manualFinish:runner.f;
      const effectiveDone=race.done===1||(race.done===0&&manualFinish!==null)?1:0;
      const bet={{date:race.d,venue:race.v,race:race.r,horse:runner.h,jockey:runner.j,score:runnerScore,scoreDisp,sp,mktPrice:runner.fx||null,wpr:runner.w,trend:runner.tr,prize:race.p,finish:effectiveFinish,won:effectiveFinish===1,placed:effectiveFinish!==null&&effectiveFinish<=3,stake,done:effectiveDone,settling:st,pace:ps,barrier:runner.b,isBet,manualFinish,raceObj:race,runnerObj:runner}};
      if(effectiveDone===1)resulted.push(bet);
      else pending.push(bet);
    }});
  }});
  return {{resulted,pending}};
}}
// ── Gist-synced storage ───────────────────────────────────────────────────
// Stores fixed odds, bet Y/N, and manual results in a GitHub Gist so they
// sync across devices. Falls back to localStorage if no token is set.
let _syncData = {{}};  // in-memory cache
let _gistId = localStorage.getItem('tr_gist_id') || '';
let _ghToken = localStorage.getItem('tr_gh_token') || '';
let _syncTimer = null;
let _pollTimer = null;
let _lastSyncedAt = 0;  // timestamp of last successful Gist load

async function syncLoad() {{
  if(!_gistId||!_ghToken){{
    for(let i=0;i<localStorage.length;i++){{
      const k=localStorage.key(i);
      if(k&&(k.startsWith('fx|')||k.startsWith('bet|')||k.startsWith('res|')))
        _syncData[k]=localStorage.getItem(k);
    }}
    _setSyncStatus('No token set','#f97316');
    return;
  }}
  _setSyncStatus('Loading...','#9ca3af');
  try{{
    const r=await fetch('https://api.github.com/gists/'+_gistId,{{
      headers:{{
        'Authorization':'Bearer '+_ghToken,
        'Accept':'application/vnd.github+json',
        'X-GitHub-Api-Version':'2022-11-28'
      }}
    }});
    if(r.ok){{
      const g=await r.json();
      const content=g.files&&g.files['toprate_bets.json']&&g.files['toprate_bets.json'].content;
      if(content){{
        _syncData=JSON.parse(content);
        _lastSyncedAt=Date.now();
        _setSyncStatus('Loaded '+Object.keys(_syncData).length+' keys '+_timeStr(),'#4ade80');
      }} else {{
        _setSyncStatus('Gist has no toprate_bets.json file','#f97316');
      }}
    }} else {{
      const err=await r.json().catch(()=>({{message:r.status}}));
      _setSyncStatus('Load error '+r.status+': '+(err.message||''),'#f87171');
    }}
  }}catch(e){{
    _setSyncStatus('Load failed: '+e.message,'#f87171');
  }}
}}

function _timeStr(){{return new Date().toLocaleTimeString([],{{hour:'2-digit',minute:'2-digit'}});}}
function _setSyncStatus(msg,color){{
  const el=document.getElementById('sync-status');
  if(el){{el.textContent=msg;el.style.color=color||'rgba(255,255,255,.4)';}}
  console.log('[Sync]',msg);
}}

// Poll every 30s to pick up changes made on other devices
function startSyncPoll(){{
  if(!_gistId||!_ghToken)return;
  clearInterval(_pollTimer);
  _pollTimer=setInterval(async()=>{{
    // Don't poll if we saved recently (avoid reading our own write)
    if(Date.now()-_lastSyncedAt<5000)return;
    const prevKeys=JSON.stringify(_syncData);
    await syncLoad();
    if(JSON.stringify(_syncData)!==prevKeys){{
      // Data changed on another device — re-render
      update();
      const status=document.getElementById('sync-status');
      const t=new Date().toLocaleTimeString([],{{hour:'2-digit',minute:'2-digit'}});
      if(status)status.textContent='Synced: '+t;
    }}
  }},30000);
}}

function syncSave(){{
  clearTimeout(_syncTimer);
  _setSyncStatus('Saving...','#9ca3af');
  _syncTimer=setTimeout(async ()=>{{
    if(!_gistId||!_ghToken){{_setSyncStatus('No token — save skipped','#f97316');return;}}
    try{{
      const body=JSON.stringify({{files:{{'toprate_bets.json':{{'content':JSON.stringify(_syncData)}}}}}});
      const r=await fetch('https://api.github.com/gists/'+_gistId,{{
        method:'PATCH',
        headers:{{
          'Authorization':'Bearer '+_ghToken,
          'Accept':'application/vnd.github+json',
          'X-GitHub-Api-Version':'2022-11-28',
          'Content-Type':'application/json'
        }},
        body
      }});
      if(r.ok){{
        _lastSyncedAt=Date.now();
        _setSyncStatus('Saved '+Object.keys(_syncData).length+' keys '+_timeStr(),'#4ade80');
      }} else {{
        const err=await r.json().catch(()=>({{message:r.status}}));
        _setSyncStatus('Save error '+r.status+': '+(err.message||''),'#f87171');
      }}
    }}catch(e){{
      _setSyncStatus('Save failed: '+e.message,'#f87171');
    }}
  }},1500);
}}

function syncGet(key){{return _syncData[key]||localStorage.getItem(key)||null;}}
function syncSet(key,val){{
  _syncData[key]=val;
  localStorage.setItem(key,val);
  syncSave();
}}
function syncRemove(key){{
  delete _syncData[key];
  localStorage.removeItem(key);
  syncSave();
}}

async function runScript(){{
  if(!_ghToken){{
    _setRunStatus('No token — set up sync first','#f87171');
    return;
  }}
  const btn=document.getElementById('run-script-btn');
  if(btn){{btn.textContent='Running...';btn.disabled=true;}}
  _setRunStatus('Triggering script...','#9ca3af');
  try{{
    // First check what workflows exist
    const listR=await fetch('https://api.github.com/repos/mattdwyer01/TopRate/actions/workflows',{{
      headers:{{
        'Authorization':'Bearer '+_ghToken,
        'Accept':'application/vnd.github+json',
        'X-GitHub-Api-Version':'2022-11-28'
      }}
    }});
    if(!listR.ok){{
      _setRunStatus('Repo error '+listR.status+' — check token has workflow scope','#f87171');
      if(btn){{btn.textContent='▶ Run script';btn.disabled=false;}}
      return;
    }}
    const listData=await listR.json();
    const workflows=listData.workflows||[];
    if(workflows.length===0){{
      _setRunStatus('No workflows found — push .github/workflows/toprate_daily.yml to GitHub first','#f87171');
      if(btn){{btn.textContent='▶ Run script';btn.disabled=false;}}
      return;
    }}
    // Use first workflow found, or find by name
    const wf=workflows.find(w=>w.name==='TopRate Daily'||w.path.includes('toprate_daily'))||workflows[0];
    console.log('Using workflow:',wf.name,'id:',wf.id,'path:',wf.path);
    _setRunStatus('Found: '+wf.name+' — dispatching...','#9ca3af');
    const r=await fetch('https://api.github.com/repos/mattdwyer01/TopRate/actions/workflows/'+wf.id+'/dispatches',{{
      method:'POST',
      headers:{{
        'Authorization':'Bearer '+_ghToken,
        'Accept':'application/vnd.github+json',
        'X-GitHub-Api-Version':'2022-11-28',
        'Content-Type':'application/json'
      }},
      body:JSON.stringify({{ref:'main'}})
    }});
    if(r.status===204){{
      _setRunStatus('✓ Script triggered! Refresh in ~2 min.','#4ade80');
    }} else {{
      let msg='';
      try{{msg=(await r.json()).message||'';}}catch(e){{}}
      _setRunStatus('Dispatch error '+r.status+': '+msg.slice(0,80),'#f87171');
    }}
  }}catch(e){{
    _setRunStatus('Failed: '+e.message,'#f87171');
  }}
  if(btn){{btn.textContent='▶ Run script';btn.disabled=false;}}
}}
function _setRunStatus(msg,color){{
  const el=document.getElementById('run-status');
  if(el){{el.textContent=msg;el.style.color=color||'rgba(255,255,255,.5)';}}
  console.log('[Run]',msg);
}}
async function syncNow(){{
  const btn=document.getElementById('sync-now-btn');
  if(btn)btn.textContent='Syncing...';
  await syncLoad();
  update();
  if(btn)btn.textContent='↻ Sync now';
}}
function showSyncSetup(){{
  const cur_id=localStorage.getItem('tr_gist_id')||'';
  const msg='To sync fixed odds and bets across devices:\\n\\n'+
    '1. Go to gist.github.com\\n'+
    '2. Create a new secret Gist named toprate_bets.json with content: {{}}\\n'+
    '3. Copy the Gist ID from the URL (the long string at the end)\\n'+
    '4. Enter it below\\n\\n'+
    'Gist ID (current: '+(cur_id||'none')+'):';
  const id=prompt(msg);
  if(id&&id.trim()){{
    localStorage.setItem('tr_gist_id',id.trim());
    _gistId=id.trim();
    const tok=prompt('GitHub Personal Access Token\\nNeeds scopes: gist + workflow\\n(stored locally on this device only)');
    if(tok&&tok.trim()){{
      localStorage.setItem('tr_gh_token',tok.trim());
      _ghToken=tok.trim();
      syncLoad().then(()=>{{update();startSyncPoll();alert('Sync connected! Data loaded from Gist.');}});
    }}
  }}
}}

// ── Key functions (now use syncGet/Set/Remove) ────────────────────────────
function fixedKey(b){{return'fx|'+b.date+'|'+b.venue+'|'+b.race+'|'+b.horse;}}
function getFixed(b){{const v=syncGet(fixedKey(b));return v?parseFloat(v):null;}}
function setFixed(b,val){{if(val===null||val===''||isNaN(val)){{syncRemove(fixedKey(b));}}else{{syncSet(fixedKey(b),String(val));}}}}
function betKey(b){{return'bet|'+b.date+'|'+b.venue+'|'+b.race+'|'+b.horse;}}
function getBet(b){{const v=syncGet(betKey(b));return v===null?true:v==='1';}}
function setBet(b,val){{syncSet(betKey(b),val?'1':'0');}}
function resultKey(b){{return'res|'+b.date+'|'+b.venue+'|'+b.race+'|'+b.horse;}}
function getResult(b){{const v=syncGet(resultKey(b));return v?parseInt(v):null;}}
function setResult(b,val){{if(val===null||isNaN(val)){{syncRemove(resultKey(b));}}else{{syncSet(resultKey(b),String(val));}}}}
// ─────────────────────────────────────────────────────────────────────────
function update(){{
  const f=getF();
  const {{resulted,pending}}=buildBets(f);
  // Sort: most recent date first, then by start time (if available) else race_id
  const sortBets=arr=>arr.slice().sort((a,b)=>{{
    if(b.date!==a.date)return b.date>a.date?1:-1;
    const at=a.raceObj.tm?new Date(a.raceObj.tm).getTime():null;
    const bt=b.raceObj.tm?new Date(b.raceObj.tm).getTime():null;
    if(at&&bt)return at-bt;
    return(a.raceObj.rid||0)-(b.raceObj.rid||0);
  }});
  const sortedResulted=sortBets(resulted);
  const sortedPending=sortBets(pending);
  const n=resulted.filter(b=>b.isBet!==false).length;
  let staked=0,profit=0,wins=0,places=0;
  resulted.forEach(b=>{{
    const isBet=b.isBet!==false;
    if(!isBet)return;
    const fx=getFixed(b);
    const priceForStake=fx&&fx>1?fx:b.sp;
    const effStake=calcStake(b.score,method==='top1'?activeSigs.size:activeSigs.size*3,priceForStake);
    staked+=effStake;
    if(b.won){{profit+=effStake*(priceForStake-1);wins++;}}else{{profit-=effStake;}}
    if(b.placed)places++;
  }});
  const roi=staked>0?profit/staked*100:null;
  const roiStr=roi!==null?(roi>=0?'+':'')+roi.toFixed(1)+'%':'—';
  document.getElementById('k-roi').textContent=roiStr;
  document.getElementById('k-roi').parentElement.className='kpi'+(roi===null?' hl':roi>=0?' hl':' neg-kpi');
  document.getElementById('k-bets').textContent=n;
  document.getElementById('k-wins').textContent=wins;
  document.getElementById('k-wp').textContent=n?(wins/n*100).toFixed(1)+'%':'—';
  document.getElementById('k-pp').textContent=n?(places/n*100).toFixed(1)+'%':'—';
  document.getElementById('k-profit').textContent=n?(profit>=0?'+':'')+profit.toFixed(1)+'u':'—';
  document.getElementById('k-profit-l').textContent=stakeMethod!=='flat'&&n?'Profit ('+staked.toFixed(1)+'u staked)':'Profit';
  document.getElementById('res-cnt').textContent=n?'('+n+')':'';
  const lbl=document.getElementById('thresh-label');
  if(method==='top1')lbl.textContent='Min votes (of '+activeSigs.size+')';
  else if(method==='top3c')lbl.textContent='Min score per horse (1pt/top-3, max '+activeSigs.size+')';
  else lbl.textContent='Min score per horse (3/2/1pts, max '+activeSigs.size*3+')';
  const tb=document.getElementById('tb');
  const empty=document.getElementById('empty');
  if(!n){{tb.innerHTML='';empty.style.display='';}}
  else{{
    empty.style.display='none';let cum=0;
    tb.innerHTML=sortedResulted.map(b=>{{
      const fx=getFixed(b);
      const priceForStake=fx&&fx>1?fx:b.sp;
      const isBet=b.isBet!==false;
      const effStake=isBet?calcStake(b.score,method==='top1'?activeSigs.size:activeSigs.size*3,priceForStake):0;
      const pl=isBet?(b.won?effStake*(priceForStake-1):-effStake):0;cum+=pl;
      const res=b.won?'<span class="pill pw">WIN</span>':b.placed?'<span class="pill pp">PLACE</span>':'<span class="pill pl">'+(b.finish||'?')+'th</span>';
      const manualTag=b.manualFinish!==null&&b.manualFinish!==undefined?'<span style="font-size:9px;color:#f97316;margin-left:2px" title="Manual result — will update when script runs">✎</span>':'';
      const plH=isBet?(pl>=0?'<span class="rp">+'+pl.toFixed(2)+'</span>':'<span class="rn">'+pl.toFixed(2)+'</span>'):'<span style="color:#9ca3af">0u</span>';
      const cumH=cum>=0?'<span class="cp">+'+cum.toFixed(1)+'</span>':'<span class="cn">'+cum.toFixed(1)+'</span>';
      const fxVal=fx?fx.toFixed(2):'';
      const fxCls='fixed-inp'+(fx?' has-val':'');
      const fxId='fx-'+b.date+'-'+b.venue+'-'+b.race+'-'+b.horse.replace(/[^a-zA-Z0-9]/g,'_');
      const betId='rbet-'+b.date+'-'+b.venue+'-'+b.race+'-'+b.horse.replace(/[^a-zA-Z0-9]/g,'_');
      const betBtn='<button class="bet-tog '+(isBet?'bet-y':'bet-n')+'" id="'+betId+'">'+(isBet?'Y':'N')+'</button>';
      const timeStrR=fmtTime(b.raceObj.tm);
      return'<tr class="'+(b.won&&isBet?'wr':b.placed&&isBet?'pr':'')+(!isBet?' no-bet-row':'')+'"><td class="mn dm">'+b.date+'</td><td class="mn" style="white-space:nowrap;color:#6b7280;">'+timeStrR+'</td><td class="br">'+b.venue+' R'+b.race+'</td><td class="br">'+b.horse+'</td><td class="dm">'+b.jockey+'</td><td class="mn">'+b.scoreDisp+'</td><td class="mn br">'+(b.sp?'$'+b.sp.toFixed(2):'?')+'</td><td class="mn"><input class="'+fxCls+'" id="'+fxId+'" type="text" inputmode="decimal" placeholder="$" value="'+fxVal+'"></td><td class="mn dm">'+fmtPrize(b.prize)+'</td><td class="mn">'+(b.wpr!=null?b.wpr.toFixed(1):'—')+'</td><td>'+trendHtml(b.trend)+'</td><td>'+ctxHtml(b.runnerObj,b.raceObj)+'</td><td class="mn">'+betBtn+'</td><td class="mn">'+(isBet?effStake.toFixed(2)+'u':'<span style="color:#9ca3af">0u</span>')+'</td><td>'+res+manualTag+'</td><td>'+plH+'</td><td>'+cumH+'</td></tr>';
    }}).join('');
    // Re-attach listeners after innerHTML rebuild
    sortedResulted.forEach(b=>{{
      const fxId='fx-'+b.date+'-'+b.venue+'-'+b.race+'-'+b.horse.replace(/[^a-zA-Z0-9]/g,'_');
      const betId='rbet-'+b.date+'-'+b.venue+'-'+b.race+'-'+b.horse.replace(/[^a-zA-Z0-9]/g,'_');
      const inp=document.getElementById(fxId);
      if(inp){{
        inp.addEventListener('change',e=>{{
          const v=parseFloat(e.target.value);
          if(!isNaN(v)&&v>1){{setFixed(b,v);inp.classList.add('has-val');}}
          else{{setFixed(b,null);inp.value='';inp.classList.remove('has-val');}}
          update();
        }});
        inp.addEventListener('click',e=>e.stopPropagation());
      }}
      const bb=document.getElementById(betId);
      if(bb){{
        bb.addEventListener('click',e=>{{
          e.stopPropagation();
          setBet(b,!getBet(b));
          update();
        }});
      }}
    }});
  }}
  // ── Mobile resulted cards ──────────────────────────────────────────────────
  const isMob=window.innerWidth<=768;
  document.getElementById('res-mob').style.display=isMob&&n?'':'none';
  if(isMob&&n){{
    let cumMob=0;
    document.getElementById('res-mob').innerHTML=sortedResulted.map(b=>{{
      const fx=getFixed(b);
      const price=fx&&fx>1?fx:b.sp;
      const isBet=b.isBet!==false;
      const effStake=isBet?calcStake(b.score,method==='top1'?activeSigs.size:activeSigs.size*3,price):0;
      const pl=isBet?(b.won?effStake*(price-1):-effStake):0;
      cumMob+=pl;
      const res=b.won?'<span class="pill pw">WIN</span>':b.placed?'<span class="pill pp">PLACE</span>':'<span class="pill pl">'+(b.finish||'?')+'th</span>';
      const plStr=isBet?(pl>=0?'<span class="rp">+'+pl.toFixed(2)+'u</span>':'<span class="rn">'+pl.toFixed(2)+'u</span>'):'<span style="color:#9ca3af">0u</span>';
      const fxVal=fx?fx.toFixed(2):'';
      const fxCls='mob-fixed-inp'+(fx?' has-val':'');
      const fxId='mfx-'+b.date+'-'+b.venue+'-'+b.race+'-'+b.horse.replace(/[^a-zA-Z0-9]/g,'_');
      const betId='mrbet-'+b.date+'-'+b.venue+'-'+b.race+'-'+b.horse.replace(/[^a-zA-Z0-9]/g,'_');
      const mobTimeR=fmtTime(b.raceObj.tm);
      return'<div class="mob-bet-card'+(b.won&&isBet?' wr':b.placed&&isBet?' pr':'')+(!isBet?' no-bet-card':'')+'">'
        +'<div class="mob-bet-hdr"><div><span class="mob-bet-venue">'+b.venue+' R'+b.race+(mobTimeR?' &nbsp;<span style="color:#6b7280;font-size:10px;">'+mobTimeR+'</span>':'')+'</span></div>'
        +'<div style="display:flex;align-items:center;gap:6px;">'+res+'<span class="mob-bet-date">'+b.date+'</span></div></div>'
        +'<div class="mob-bet-body">'
        +'<div class="mob-bet-horse">'+b.horse+'</div>'
        +'<div class="mob-bet-jockey">'+b.jockey+'</div>'
        +'<div class="mob-bet-row">'
        +'<span class="mob-bet-tag score">'+b.scoreDisp+'</span>'
        +(b.sp?'<span class="mob-bet-tag sp">SP $'+b.sp.toFixed(2)+'</span>':'')
        +(b.wpr!=null?'<span class="mob-bet-tag wpr">WPR '+b.wpr.toFixed(1)+'</span>':'')
        +'<span class="mob-bet-tag prize">'+fmtPrize(b.prize)+'</span>'
        +'</div>'
        +'<div class="mob-bet-footer">'
        +'<button class="bet-tog '+(isBet?'bet-y':'bet-n')+'" id="'+betId+'">'+(isBet?'Y':'N')+'</button>'
        +'<span style="font-size:10px;color:#6b7280;">Fixed:</span>'
        +'<input class="'+fxCls+'" id="'+fxId+'" type="text" inputmode="decimal" placeholder="$" value="'+fxVal+'">'
        +'<span class="mob-stake-lbl">'+(isBet?effStake.toFixed(2)+'u':'0u')+' &nbsp; '+plStr+'</span>'
        +'</div>'
        +'</div></div>';
    }}).join('');
    sortedResulted.forEach(b=>{{
      const fxId='mfx-'+b.date+'-'+b.venue+'-'+b.race+'-'+b.horse.replace(/[^a-zA-Z0-9]/g,'_');
      const betId='mrbet-'+b.date+'-'+b.venue+'-'+b.race+'-'+b.horse.replace(/[^a-zA-Z0-9]/g,'_');
      const inp=document.getElementById(fxId);
      if(inp){{
        inp.addEventListener('change',e=>{{
          const v=parseFloat(e.target.value);
          if(!isNaN(v)&&v>1){{setFixed(b,v);inp.classList.add('has-val');}}
          else{{setFixed(b,null);inp.value='';inp.classList.remove('has-val');}}
          update();
        }});
      }}
      const bb=document.getElementById(betId);
      if(bb){{bb.addEventListener('click',e=>{{e.stopPropagation();setBet(b,!getBet(b));update();}});}}
    }});
  }}

  const showPend=f.pend&&!f.resonly;
  document.getElementById('pend-title').style.display=showPend&&sortedPending.length?'':'none';
  document.getElementById('pend-card').style.display=showPend&&sortedPending.length&&!isMob?'':'none';
  document.getElementById('pend-mob').style.display=showPend&&sortedPending.length&&isMob?'':'none';
  document.getElementById('pend-cnt').textContent=sortedPending.length?'('+sortedPending.length+')':'';
  if(showPend&&sortedPending.length){{
    document.getElementById('pend-tb').innerHTML=sortedPending.map(b=>{{
      const fx=getFixed(b);
      const isBet=getBet(b);
      const manualResult=getResult(b);
      const priceForStake=fx&&fx>1?fx:b.sp;
      const effStake=isBet?calcStake(b.score,method==='top1'?activeSigs.size:activeSigs.size*3,priceForStake):0;
      const fxVal=fx?fx.toFixed(2):'';
      const fxCls='fixed-inp'+(fx?' has-val':'');
      const fxId='pfx-'+b.date+'-'+b.venue+'-'+b.race+'-'+b.horse.replace(/[^a-zA-Z0-9]/g,'_');
      const betId='pbet-'+b.date+'-'+b.venue+'-'+b.race+'-'+b.horse.replace(/[^a-zA-Z0-9]/g,'_');
      const resId='pres-'+b.date+'-'+b.venue+'-'+b.race+'-'+b.horse.replace(/[^a-zA-Z0-9]/g,'_');
      const betBtn='<button class="bet-tog '+(isBet?'bet-y':'bet-n')+'" id="'+betId+'">'+(isBet?'Y':'N')+'</button>';
      const resVal=manualResult!==null?manualResult:'';
      const resInp='<input class="res-inp" id="'+resId+'" type="text" inputmode="numeric" placeholder="—" value="'+resVal+'" style="width:36px;font-size:11px;text-align:center;border:1px solid #d1d5db;border-radius:3px;padding:2px 4px;background:#f0fdf4;">';
      const mktPriceHtml=b.mktPrice?'<span class="mn" style="color:#1a3a5c;font-weight:700;">$'+b.mktPrice.toFixed(2)+'</span>':'<span style="color:#9ca3af">—</span>';
      const timeStr=fmtTime(b.raceObj.tm);
      return'<tr class="'+(isBet?'':'no-bet-row')+'"><td class="mn dm">'+b.date+'</td><td class="mn" style="white-space:nowrap;color:#f97316;font-weight:700;">'+timeStr+'</td><td class="br">'+b.venue+' R'+b.race+'</td><td class="br">'+b.horse+'</td><td class="dm">'+b.jockey+'</td><td class="mn">'+b.scoreDisp+'</td><td class="mn br">'+(b.sp?'$'+b.sp.toFixed(2):'TBD')+'</td><td class="mn">'+mktPriceHtml+'</td><td class="mn"><input class="'+fxCls+'" id="'+fxId+'" type="text" inputmode="decimal" placeholder="$" value="'+fxVal+'"></td><td class="mn dm">'+fmtPrize(b.prize)+'</td><td class="mn">'+(b.wpr!=null?b.wpr.toFixed(1):'—')+'</td><td>'+trendHtml(b.trend)+'</td><td>'+ctxHtml(b.runnerObj,b.raceObj)+'</td><td class="mn">'+betBtn+'</td><td class="mn">'+(isBet?effStake.toFixed(2)+'u':'<span style="color:#9ca3af">0u</span>')+'</td><td class="mn">'+resInp+'</td></tr>';
    }}).join('');
    sortedPending.forEach(b=>{{
      const fxId='pfx-'+b.date+'-'+b.venue+'-'+b.race+'-'+b.horse.replace(/[^a-zA-Z0-9]/g,'_');
      const betId='pbet-'+b.date+'-'+b.venue+'-'+b.race+'-'+b.horse.replace(/[^a-zA-Z0-9]/g,'_');
      const resId='pres-'+b.date+'-'+b.venue+'-'+b.race+'-'+b.horse.replace(/[^a-zA-Z0-9]/g,'_');
      const fxInp=document.getElementById(fxId);
      if(fxInp){{
        fxInp.addEventListener('change',e=>{{
          const v=parseFloat(e.target.value);
          if(!isNaN(v)&&v>1){{setFixed(b,v);fxInp.classList.add('has-val');}}
          else{{setFixed(b,null);fxInp.value='';fxInp.classList.remove('has-val');}}
          update();
        }});
        fxInp.addEventListener('click',e=>e.stopPropagation());
      }}
      const betBtn=document.getElementById(betId);
      if(betBtn){{
        betBtn.addEventListener('click',e=>{{
          e.stopPropagation();
          const cur=getBet(b);
          setBet(b,!cur);
          update();
        }});
      }}
      const resInp=document.getElementById(resId);
      if(resInp){{
        resInp.addEventListener('change',e=>{{
          const v=parseInt(e.target.value);
          setResult(b,isNaN(v)||v<1?null:v);
          update();
        }});
        resInp.addEventListener('click',e=>e.stopPropagation());
      }}
    }});
    // ── Mobile pending cards ─────────────────────────────────────────────────
    if(isMob){{
      document.getElementById('pend-mob').innerHTML=sortedPending.map(b=>{{
        const fx=getFixed(b);
        const isBet=getBet(b);
        const manualResult=getResult(b);
        const price=fx&&fx>1?fx:b.sp;
        const effStake=isBet?calcStake(b.score,method==='top1'?activeSigs.size:activeSigs.size*3,price):0;
        const fxVal=fx?fx.toFixed(2):'';
        const fxCls='mob-fixed-inp'+(fx?' has-val':'');
        const fxId='mpfx-'+b.date+'-'+b.venue+'-'+b.race+'-'+b.horse.replace(/[^a-zA-Z0-9]/g,'_');
        const betId='mpbet-'+b.date+'-'+b.venue+'-'+b.race+'-'+b.horse.replace(/[^a-zA-Z0-9]/g,'_');
        const resId='mpres-'+b.date+'-'+b.venue+'-'+b.race+'-'+b.horse.replace(/[^a-zA-Z0-9]/g,'_');
        const mobTimeP=fmtTime(b.raceObj.tm);
        return'<div class="mob-bet-card'+(!isBet?' no-bet-card':'')+'">'
          +'<div class="mob-bet-hdr"><span class="mob-bet-venue">'+b.venue+' R'+b.race+(mobTimeP?' &nbsp;<span style="color:#f97316;font-size:10px;font-weight:700;">'+mobTimeP+'</span>':'')+'</span>'
          +'<span class="mob-bet-date">'+b.date+'</span></div>'
          +'<div class="mob-bet-body">'
          +'<div class="mob-bet-horse">'+b.horse+'</div>'
          +'<div class="mob-bet-jockey">'+b.jockey+'</div>'
          +'<div class="mob-bet-row">'
          +'<span class="mob-bet-tag score">'+b.scoreDisp+'</span>'
          +(b.sp?'<span class="mob-bet-tag sp">SP $'+b.sp.toFixed(2)+'</span>':'<span class="mob-bet-tag sp">SP TBD</span>')
          +(b.mktPrice?'<span class="mob-bet-tag mkt">Mkt $'+b.mktPrice.toFixed(2)+'</span>':'')
          +(b.wpr!=null?'<span class="mob-bet-tag wpr">WPR '+b.wpr.toFixed(1)+'</span>':'')
          +'<span class="mob-bet-tag prize">'+fmtPrize(b.prize)+'</span>'
          +'</div>'
          +'<div class="mob-bet-footer">'
          +'<button class="bet-tog '+(isBet?'bet-y':'bet-n')+'" id="'+betId+'">'+(isBet?'Y':'N')+'</button>'
          +'<span style="font-size:10px;color:#6b7280;">Fixed:</span>'
          +'<input class="'+fxCls+'" id="'+fxId+'" type="text" inputmode="decimal" placeholder="$" value="'+fxVal+'">'
          +'<span style="font-size:10px;color:#6b7280;">Pos:</span>'
          +'<input class="mob-res-inp" id="'+resId+'" type="text" inputmode="numeric" placeholder="—" value="'+(manualResult!==null?manualResult:'')+'">'
          +'<span class="mob-stake-lbl">'+(isBet?effStake.toFixed(2)+'u':'0u')+'</span>'
          +'</div>'
          +'</div></div>';
      }}).join('');
      sortedPending.forEach(b=>{{
        const fxId='mpfx-'+b.date+'-'+b.venue+'-'+b.race+'-'+b.horse.replace(/[^a-zA-Z0-9]/g,'_');
        const betId='mpbet-'+b.date+'-'+b.venue+'-'+b.race+'-'+b.horse.replace(/[^a-zA-Z0-9]/g,'_');
        const resId='mpres-'+b.date+'-'+b.venue+'-'+b.race+'-'+b.horse.replace(/[^a-zA-Z0-9]/g,'_');
        const fxInp=document.getElementById(fxId);
        if(fxInp){{fxInp.addEventListener('change',e=>{{const v=parseFloat(e.target.value);if(!isNaN(v)&&v>1){{setFixed(b,v);fxInp.classList.add('has-val');}}else{{setFixed(b,null);fxInp.value='';fxInp.classList.remove('has-val');}}update();}});}}
        const bb=document.getElementById(betId);
        if(bb){{bb.addEventListener('click',e=>{{e.stopPropagation();setBet(b,!getBet(b));update();}});}}
        const ri=document.getElementById(resId);
        if(ri){{ri.addEventListener('change',e=>{{const v=parseInt(e.target.value);setResult(b,isNaN(v)||v<1?null:v);update();}});}}
      }});
    }}
  }}
}}
// re-render mobile cards on resize
window.addEventListener('resize',update);
document.getElementById('f-votes').addEventListener('input',e=>{{document.getElementById('v-votes').textContent=e.target.value;update();}});
document.getElementById('f-sp').addEventListener('input',e=>{{document.getElementById('v-sp').textContent='$'+parseFloat(e.target.value).toFixed(2);update();}});
document.getElementById('f-spmax').addEventListener('input',e=>{{const v=parseFloat(e.target.value);document.getElementById('v-spmax').textContent=v>=30?'Any':'$'+v.toFixed(0);update();}});
document.getElementById('f-prize').addEventListener('input',e=>{{const v=parseInt(e.target.value);document.getElementById('v-prize').textContent=v===0?'Any':'$'+(v/1000).toFixed(0)+'k';update();}});
document.getElementById('f-target').addEventListener('input',e=>{{document.getElementById('v-target').textContent=parseFloat(e.target.value).toFixed(1)+'u';update();}});
document.getElementById('f-barrier').addEventListener('input',e=>{{const v=parseInt(e.target.value);document.getElementById('v-barrier').textContent=v>=16?'Any':'<='+v;update();}});
['f-tab','f-trend','f-nofs','f-pend','f-resonly','f-nowide'].forEach(id=>document.getElementById(id).addEventListener('change',update));
document.querySelectorAll('#dow-grid input').forEach(cb=>cb.addEventListener('change',update));
document.querySelectorAll('[data-settle],[data-pace]').forEach(cb=>cb.addEventListener('change',update));
document.getElementById('f-date-from').addEventListener('change',update);
document.getElementById('f-date-to').addEventListener('change',update);
function resetAll(){{
  document.getElementById('f-tab').checked=true;
  document.getElementById('f-prize').value=25000;document.getElementById('v-prize').textContent='$25k';
  document.getElementById('f-nofs').checked=true;document.getElementById('f-trend').checked=true;
  document.getElementById('f-nowide').checked=false;
  document.getElementById('f-barrier').value=16;document.getElementById('v-barrier').textContent='Any';
  document.getElementById('f-sp').value=1;document.getElementById('v-sp').textContent='$1.00';
  document.getElementById('f-spmax').value=30;document.getElementById('v-spmax').textContent='Any';
  document.getElementById('f-target').value=4;document.getElementById('v-target').textContent='4.0u';
  document.getElementById('f-pend').checked=true;document.getElementById('f-resonly').checked=false;
  document.querySelectorAll('[data-settle],[data-pace]').forEach(cb=>cb.checked=true);
  setDow('all');setStake('fixed');selectOptimalSigs();setMethod('top3c');
  document.getElementById('f-votes').value=8;document.getElementById('v-votes').textContent='8';
  document.getElementById('f-date-from').value='';document.getElementById('f-date-to').value='';
  setDateRange('today');
  update();
}}
selectOptimalSigs();
setStake('fixed');
setMethod('top3c');
document.getElementById('f-sp').value=1;
document.getElementById('v-sp').textContent='$1.00';
document.getElementById('f-spmax').value=30;
document.getElementById('v-spmax').textContent='Any';
document.getElementById('f-votes').value=8;
document.getElementById('v-votes').textContent='8';
document.getElementById('f-target').value=4;
document.getElementById('v-target').textContent='4.0u';
setDateRange('today');
syncLoad().then(()=>{{update();startSyncPoll();}});

// ── Tab switching ────────────────────────────────────────────────────────────
function switchTab(tab){{
  ['bets','quaddie'].forEach(t=>{{
    document.getElementById('tab-'+t).classList.toggle('active',t===tab);
    document.getElementById('panel-'+t).classList.toggle('active',t===tab);
  }});
  if(tab==='quaddie')buildQuaddie();
}}

// ── Quaddie ──────────────────────────────────────────────────────────────────
// Per-meeting state: which runners are selected in each leg
const qSelections={{}};  // key: date|venue|legIdx|runnerIdx -> bool
const qStakes={{}};       // key: date|venue -> stake amount

function qKey(date,venue,legIdx,runIdx){{return date+'|'+venue+'|'+legIdx+'|'+runIdx;}}
function qMeetingKey(date,venue){{return date+'|'+venue;}}

function buildQuaddie(){{
  const f=getF();
  // Group RACES by date+venue, sort races within each meeting by race number
  const meetings={{}};
  RACES.forEach(race=>{{
    // Apply date filter same as bets tab
    if(f.dateFrom&&race.d<f.dateFrom)return;
    if(f.dateTo&&race.d>f.dateTo)return;
    const mk=race.d+'~~~'+race.v;
    if(!meetings[mk])meetings[mk]={{date:race.d,venue:race.v,races:[]}};
    meetings[mk].races.push(race);
  }});

  // Sort races within each meeting by race number, take last 4
  const meetingList=Object.values(meetings).sort((a,b)=>b.date.localeCompare(a.date)||a.venue.localeCompare(b.venue));

  const container=document.getElementById('q-content');
  if(!meetingList.length){{container.innerHTML='<div class="q-no-meeting">No meetings match current date filter. Use the Date Range filter on the left to select a date.</div>';return;}}

  // Active signal indices for signal breakdown
  const activeSigIdxs=SIG_NAMES.map((s,i)=>activeSigs.has(s)?i:-1).filter(i=>i>=0);
  const activeSigLabels=activeSigIdxs.map(i=>SIG_LABELS[i]);

  container.innerHTML=meetingList.map(meeting=>{{
    const sortedRaces=meeting.races.slice().sort((a,b)=>(a.r||0)-(b.r||0));
    const legs=sortedRaces.slice(-4);  // last 4 races
    if(legs.length<1)return'';
    const mk=qMeetingKey(meeting.date,meeting.venue);
    const stake=qStakes[mk]||1;

    // Build combination count from current selections
    const comboCounts=legs.map((leg,li)=>{{
      const checked=leg.u.filter((_,ri)=>{{
        const k=qKey(meeting.date,meeting.venue,li,ri);
        return qSelections[k]!==false;  // default = top runner selected
      }});
      // Default: top-scored runner selected
      const scores=leg.u.map((_,ri)=>{{
        let sc=0;
        activeSigIdxs.forEach(si=>{{
          const [r1,r2,r3]=leg.s[si];
          if(method==='top1'){{if(r1===ri)sc+=1;}}
          else if(method==='top3c'){{if(r1===ri||r2===ri||r3===ri)sc+=1;}}
          else{{if(r1===ri)sc+=3;else if(r2===ri)sc+=2;else if(r3===ri)sc+=1;}}
        }});
        return sc;
      }});
      const maxSc=Math.max(...scores,0);
      const topIdx=scores.indexOf(maxSc);
      // Count selected: if no explicit selection set, default to top runner
      let n=0;
      leg.u.forEach((_,ri)=>{{
        const k=qKey(meeting.date,meeting.venue,li,ri);
        const explicit=qSelections[k];
        const byDefault=explicit===undefined&&ri===topIdx;
        if(explicit===true||byDefault)n++;
      }});
      return Math.max(n,1);
    }});
    const totalCombos=comboCounts.reduce((a,b)=>a*b,1);
    const totalCost=(totalCombos*stake).toFixed(2);

    const legsHtml=legs.map((leg,li)=>{{
      // Compute scores for all runners in this leg
      const scores=leg.u.map((_,ri)=>{{
        let sc=0;
        activeSigIdxs.forEach(si=>{{
          const [r1,r2,r3]=leg.s[si];
          if(method==='top1'){{if(r1===ri)sc+=1;}}
          else if(method==='top3c'){{if(r1===ri||r2===ri||r3===ri)sc+=1;}}
          else{{if(r1===ri)sc+=3;else if(r2===ri)sc+=2;else if(r3===ri)sc+=1;}}
        }});
        return sc;
      }});
      const maxSc=Math.max(...scores,0);
      const topIdx=scores.indexOf(maxSc);

      // Per-signal top3 for this leg — count how many signals each runner appears in top3
      const sigTop3Counts=leg.u.map((_,ri)=>{{
        let cnt=0;
        activeSigIdxs.forEach(si=>{{
          const [r1,r2,r3]=leg.s[si];
          if(r1===ri||r2===ri||r3===ri)cnt++;
        }});
        return cnt;
      }});

      // Sort runners by composite score desc then sigTop3Counts desc
      const order=leg.u.map((_,i)=>i).sort((a,b)=>scores[b]-scores[a]||sigTop3Counts[b]-sigTop3Counts[a]);

      const statusTag=leg.done?'<span class="q-done-tag">RES</span>':'<span class="q-pend-tag">PEND</span>';

      const runnersHtml=order.map(ri=>{{
        const runner=leg.u[ri];
        const sc=scores[ri];
        const top3cnt=sigTop3Counts[ri];
        const k=qKey(meeting.date,meeting.venue,li,ri);
        const explicit=qSelections[k];
        const isDefault=explicit===undefined&&ri===topIdx;
        const isSelected=explicit===true||isDefault;
        const isBanker=ri===topIdx&&sc===maxSc;

        // Which signals put this runner in top 3? build pill list
        const sigPositions=activeSigIdxs.map((si,_)=>{{
          const [r1,r2,r3]=leg.s[si];
          if(r1===ri)return 1;
          if(r2===ri)return 2;
          if(r3===ri)return 3;
          return 0;
        }}).filter(p=>p>0);

        // Finish indicator if resulted
        let finishTag='';
        if(leg.done&&runner.f!==null&&runner.f!==undefined){{
          finishTag=runner.f===1?'<span class="q-pill q-pill-1">WIN</span>':runner.f<=3?'<span class="q-pill q-pill-2">PLC</span>':'<span style="font-size:9px;color:#9ca3af;margin-left:3px">'+runner.f+'th</span>';
        }}

        return'<div class="q-runner'+(isSelected?' selected':'')+(isBanker&&isSelected?' banker':'')+'" data-mk="'+mk+'" data-li="'+li+'" data-ri="'+ri+'">'
          +'<input type="checkbox" '+(isSelected?'checked':'')+'>'
          +'<span class="q-runner-name" title="'+runner.h+'">'+runner.h+'</span>'
          +(sc>0?'<span class="q-runner-score">'+sc+'</span>':'')
          +'<span class="q-runner-sp">'+(runner.sp?'$'+runner.sp.toFixed(2):'')+'</span>'
          +(top3cnt>0?'<span class="q-runner-top"><span style="font-size:9px;color:#6b7280;margin-left:2px">top3×'+top3cnt+'</span></span>':'')
          +finishTag
          +'</div>';
      }}).join('');

      // Signal breakdown table for this leg
      const sigBreakdownHtml='<div class="q-sigs">'
        +activeSigIdxs.map((si,_)=>{{
          const lbl=SIG_LABELS[si];
          const [r1,r2,r3]=leg.s[si];
          const n1=r1>=0&&leg.u[r1]?leg.u[r1].h:'—';
          const n2=r2>=0&&leg.u[r2]?leg.u[r2].h:'—';
          const n3=r3>=0&&leg.u[r3]?leg.u[r3].h:'—';
          return'<div class="q-sig-row">'
            +'<span class="q-sig-name">'+lbl+'</span>'
            +'<div class="q-sig-top3">'
            +'<span class="q-sig-horse" title="'+n1+'"><span class="q-pill q-pill-1">1</span> '+n1+'</span>'
            +'<span class="q-sig-horse" title="'+n2+'" style="color:#6b7280"> '+n2+'</span>'
            +'<span class="q-sig-horse" title="'+n3+'" style="color:#9ca3af"> '+n3+'</span>'
            +'</div></div>';
        }}).join('')
        +'</div>';

      return'<div class="q-leg">'
        +'<div class="q-leg-hdr"><div><div class="q-leg-title">Leg '+(li+1)+'</div><div class="q-leg-race">R'+leg.r+'</div></div>'+statusTag+'</div>'
        +runnersHtml
        +'<details style="border-top:1px solid #e2e5ea;">'
        +'<summary class="q-sig-toggle">Signal breakdown</summary>'
        +sigBreakdownHtml
        +'</details>'
        +'</div>';
    }}).join('');

    return'<div class="q-meeting">'
      +'<div class="q-meeting-hdr">'
      +'<div class="q-meeting-name">'+meeting.venue+'</div>'
      +'<div class="q-meeting-date">'+meeting.date+' &nbsp;·&nbsp; Quaddie (last '+legs.length+' races)</div>'
      +'</div>'
      +'<div class="q-cost-bar">'
      +'<div><div class="q-cost-lbl">Combinations</div><div class="q-cost-val" id="combos-'+mk.replace(/[^a-z0-9]/gi,'_')+'">'+totalCombos+'</div></div>'
      +'<div><div class="q-cost-lbl">Total cost</div><div class="q-cost-val" id="cost-'+mk.replace(/[^a-z0-9]/gi,'_')+'">$'+totalCost+'</div></div>'
      +'<div class="q-stake-wrap"><span class="q-cost-lbl">$ / combo</span>'
      +'<input class="q-stake-inp" type="text" inputmode="decimal" value="'+stake+'" data-mk="'+mk+'" oninput="updateStake(this)">'
      +'</div>'
      +'</div>'
      +'<div class="q-legs">'+legsHtml+'</div>'
      +'</div>';
  }}).join('');

  // Attach checkbox listeners
  container.querySelectorAll('.q-runner').forEach(el=>{{
    el.addEventListener('click',e=>{{
      if(e.target.tagName==='INPUT')return;  // handled separately
      const cb=el.querySelector('input[type=checkbox]');
      if(cb)cb.click();
    }});
    const cb=el.querySelector('input[type=checkbox]');
    if(cb)cb.addEventListener('change',e=>{{
      const{{mk,li,ri}}=el.dataset;
      qSelections[qKey(mk.split('~~~')[0],mk.split('~~~')[1],parseInt(li),parseInt(ri))]=e.target.checked;
      buildQuaddie();
    }});
  }});
}}

function toggleSidebar(){{
  document.querySelector('.sidebar').classList.toggle('open');
  document.getElementById('mob-overlay').classList.toggle('open');
}}
function closeSidebar(){{
  document.querySelector('.sidebar').classList.remove('open');
  document.getElementById('mob-overlay').classList.remove('open');
}}
// Close sidebar when any interactive element inside it is tapped on mobile
document.querySelector('.sidebar').addEventListener('click',e=>{{
  if(window.innerWidth>768)return;
  if(e.target.type==='range')return;  // sliders need drag — don't close
  setTimeout(closeSidebar,200);
}});
</script>
</body>
</html>"""

    OUTPUT_HTML.write_text(html, encoding="utf-8")
    # Also save selections CSV for reference
    if not sel_df.empty:
        sel_df.to_csv(SELECTIONS_CSV, index=False)
    print(f"HTML rebuilt -> {OUTPUT_HTML}")
    print(f"  {n_total} races · {n_res} resulted · {n_pend} pending")

# -----------------------------------------------------------------------
# MAIN
# -----------------------------------------------------------------------
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
    """Push updated toprate_live.html to GitHub Pages."""
    import subprocess as sp
    print("\n── Publishing to GitHub ──")
    script_dir = Path(__file__).parent
    def git(cmd, check=True):
        result = sp.run(["git"] + cmd, cwd=script_dir, capture_output=True, text=True)
        if result.stdout.strip(): print(f"  {result.stdout.strip()}")
        if result.stderr.strip(): print(f"  {result.stderr.strip()}")
        if check and result.returncode != 0:
            print(f"  git {' '.join(cmd)} failed (exit {result.returncode})")
        return result.returncode == 0
    # Fetch remote and reset only toprate_live.html to avoid conflicts
    # (don't reset --hard which would overwrite toprate_daily.py)
    sp.run(["git", "fetch", "origin"], cwd=script_dir, capture_output=True, text=True)
    sp.run(["git", "checkout", "origin/main", "--", "toprate_live.html"],
           cwd=script_dir, capture_output=True, text=True)
    git(["add", "toprate_live.html"])
    status = sp.run(["git", "diff", "--staged", "--quiet"], cwd=script_dir)
    if status.returncode == 0:
        print("  No changes to publish — HTML unchanged.")
        return
    from datetime import datetime as _dt
    msg = f"TopRate update {_dt.now():%Y-%m-%d %H:%M}"
    git(["commit", "-m", msg])
    if git(["push"], check=False):
        print(f"  Published: {msg}")
    else:
        print("  Push failed — check git remote and credentials.")


def main():
    parser = argparse.ArgumentParser(description="TopRate daily runner database + live HTML")
    parser.add_argument("--no-html",    action="store_true", help="Skip HTML rebuild")
    parser.add_argument("--backfill",   type=int, default=0, help="Backfill results for last N days")
    parser.add_argument("--date",       help="Fetch races for specific date (YYYY-MM-DD)")
    parser.add_argument("--publish",    action="store_true", help="After rebuilding, push HTML to GitHub Pages")
    parser.add_argument("--serve",      action="store_true", help="After rebuilding, serve HTML on local network for iPhone access")
    parser.add_argument("--serve-only", action="store_true", help="Skip fetch/rebuild, just start the server (use existing HTML)")
    parser.add_argument("--port",       type=int, default=8080, help="Port for --serve (default 8080)")
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

    jwt = login()
    print()

    print("── Step 1: Updating results ──")
    runners_df = update_results(jwt, runners_df)
    print()

    print("── Step 2: Fetching today's races ──")
    runners_df = fetch_todays_races(jwt, runners_df, args.date)
    print()

    save_runners(runners_df)
    print(f"Saved -> {RUNNERS_CSV} ({len(runners_df):,} runners, {runners_df['race_id'].nunique():,} races)")
    print()

    if not args.no_html:
        print("── Step 3: Rebuilding HTML ──")
        rebuild_html(runners_df)

    if args.publish:
        publish()

    print(f"\n{'='*60}")
    print("Done.")

    if args.serve:
        serve(args.port)

if __name__ == "__main__":
    main()
