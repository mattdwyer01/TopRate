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

RUNNERS_CSV    = Path(__file__).parent / "toprate_runners.csv"
SELECTIONS_CSV = Path(__file__).parent / "toprate_selections.csv"
PRICE_HISTORY_CSV = Path(__file__).parent / "toprate_price_history.csv"
OUTPUT_HTML    = Path(__file__).parent / "toprate_live.html"
BT_RUNNERS_CSV = Path(__file__).parent / "toprate_runners_backtest.csv"

# Punting Form ratings - ingested separately by puntingform_ingest.py.
# Joined into runners_df during the daily run by merge_pf_ratings(). When
# the file doesn't exist or fails to load, all PF columns are None and the
# new model rule produces zero picks (since it requires PF data).
PF_RATINGS_CSV = Path(__file__).parent / "puntingform_data" / "pf_ratings.csv"

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
    "going","track_grading","rail_position","start_time",
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
    "finish_position","won","placed","resulted",
    # ── Punting Form ratings ──────────────────────────────────────────────
    # Merged in by merge_pf_ratings() each daily run. Frozen at PF's
    # ratingsUpdated time per meeting so safe to backtest. None when PF
    # didn't rate the meeting (model rule excludes those races).
    "pf_ai_rank","pf_ai_price","pf_ai_score",
    "pf_class_rank","pf_tac_class_rank",
    "pf_time_rank","pf_early_time_rank",
    "pf_last600_rank","pf_last400_rank","pf_last200_rank",
    "pf_run_style","pf_class_change","pf_reliable",
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

        # ONE-TIME DIAGNOSTIC: log all top-level keys of the runner object so we
        # can identify where jt_combo_win_pct lives. The backtest has fields like
        # jt_combo_rides, jt_combo_win_pct, jt_combo_place_pct, jt_combo_pot.
        # If we find them in the live API response we can wire them up.
        if "_jt_combo_diag_done" not in _logged_filters:
            _logged_filters.add("_jt_combo_diag_done")
            top_keys = sorted(runner.keys())
            print(f"  DIAG: get_race_stats runner top-level keys: {top_keys}")
            # If there are any combo/jockey/trainer-related arrays we don't know about, log their domains
            for k in top_keys:
                v = runner.get(k)
                if isinstance(v, list) and v and isinstance(v[0], dict):
                    sample_keys = sorted(v[0].keys())
                    print(f"  DIAG: '{k}' is a list of {len(v)} items; first item keys: {sample_keys}")
                    if "domain" in v[0]:
                        domains = [item.get("domain") for item in v[:3]]
                        print(f"  DIAG: '{k}' first 3 domains: {domains}")
                # Also log scalar fields that might be the combo numbers directly
                elif isinstance(v, (int, float)) and "combo" in k.lower():
                    print(f"  DIAG: scalar combo field found: {k} = {v}")

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
                if jt_combo_win_pct is not None and "jt_combo_found" not in _logged_filters:
                    _logged_filters.add("jt_combo_found")
                    print(f"  DIAG: found jt_combo data in '{arr_key}'. Sample: {jt_match}")
                break

        # Path B: scalar fields on the runner object directly
        if jt_combo_win_pct is None:
            for k in ("jtComboWinPct", "jt_combo_win_pct", "comboWinPct",
                      "jockeyTrainerWinPct"):
                if runner.get(k) is not None:
                    jt_combo_win_pct = runner.get(k)
                    if "jt_combo_scalar_found" not in _logged_filters:
                        _logged_filters.add("jt_combo_scalar_found")
                        print(f"  DIAG: found jt_combo scalar at '{k}' = {jt_combo_win_pct}")
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


def merge_pf_ratings(runners_df):
    """
    Merge Punting Form ratings into runners_df.

    PF ratings are stored in puntingform_data/pf_ratings.csv (one row per
    runner per meeting). The merge key is (date, venue_lower, race_no, horse_lower).

    PF data is point-in-time clean (frozen at PF's ratingsUpdated time per
    meeting). Used by the new unified model rule which requires PF signals.

    When PF data isn't available (file missing, meeting not rated, runner
    not matched), the PF columns are filled with None. Downstream the model
    rule excludes any runner without all required PF signals.
    """
    if not PF_RATINGS_CSV.exists():
        print(f"  Warning: {PF_RATINGS_CSV} not found - skipping PF merge")
        for col in ("pf_ai_rank", "pf_ai_price", "pf_ai_score",
                    "pf_class_rank", "pf_tac_class_rank",
                    "pf_time_rank", "pf_early_time_rank",
                    "pf_last600_rank", "pf_last400_rank", "pf_last200_rank",
                    "pf_run_style", "pf_class_change", "pf_reliable"):
            if col not in runners_df.columns:
                runners_df[col] = None
        return runners_df

    try:
        pf = pd.read_csv(PF_RATINGS_CSV)
    except Exception as e:
        print(f"  Warning: failed to load {PF_RATINGS_CSV} ({e})")
        return runners_df

    # Strip right-padded run style values ("bm        " -> "bm")
    if "runStyle" in pf.columns:
        pf["runStyle"] = pf["runStyle"].astype(str).str.strip()

    # Build join key on PF side
    pf["_pf_horse_lc"] = pf["runnerName"].astype(str).str.lower().str.strip()
    pf["_pf_venue_lc"] = pf["track"].astype(str).str.lower().str.strip()
    pf["_join_key"] = (pf["_pf_date"].astype(str) + "|" +
                       pf["_pf_venue_lc"] + "|" +
                       pf["raceNo"].astype(str) + "|" +
                       pf["_pf_horse_lc"])

    # Build join key on runners_df side
    runners_df = runners_df.copy()
    runners_df["_tr_horse_lc"] = runners_df["horse"].astype(str).str.lower().str.strip()
    runners_df["_tr_venue_lc"] = runners_df["venue"].astype(str).str.lower().str.strip()
    runners_df["_join_key"] = (runners_df["date"].astype(str) + "|" +
                               runners_df["_tr_venue_lc"] + "|" +
                               runners_df["race"].astype(str) + "|" +
                               runners_df["_tr_horse_lc"])

    # Select PF columns we need and rename to our naming convention
    pf_cols = {
        "_join_key": "_join_key",
        "pfaiRank": "pf_ai_rank",
        "pfaiPrice": "pf_ai_price",
        "pfaiScore": "pf_ai_score",
        "weightClassRank": "pf_class_rank",
        "timeAdjustedWeightClassRank": "pf_tac_class_rank",
        "timeRank": "pf_time_rank",
        "earlyTimeRank": "pf_early_time_rank",
        "last600TimeRank": "pf_last600_rank",
        "last400TimeRank": "pf_last400_rank",
        "last200TimeRank": "pf_last200_rank",
        "runStyle": "pf_run_style",
        "classChange": "pf_class_change",
        "isReliable": "pf_reliable",
    }
    have_cols = [c for c in pf_cols if c in pf.columns]
    pf_subset = pf[have_cols].rename(columns={k: v for k, v in pf_cols.items() if k in have_cols})
    pf_subset = pf_subset.drop_duplicates(subset=["_join_key"], keep="last")

    # Drop existing PF columns to avoid duplicate suffixing on re-merge
    for col in pf_subset.columns:
        if col != "_join_key" and col in runners_df.columns:
            runners_df = runners_df.drop(columns=[col])

    merged = runners_df.merge(pf_subset, on="_join_key", how="left")

    # Cleanup join scratch columns
    merged = merged.drop(columns=["_join_key", "_tr_horse_lc", "_tr_venue_lc"])

    n_total = len(merged)
    n_matched = merged["pf_ai_rank"].notna().sum()
    print(f"  PF ratings merged: {n_matched:,}/{n_total:,} runners have PF data ({n_matched/n_total*100:.1f}%)")
    return merged


# -----------------------------------------------------------------------
# UNIFIED MODEL RULE - validated against 28-day backtest (Apr 9 - May 7)
# -----------------------------------------------------------------------
# Single rule combining TopRate signals (wpr_rank, late_rank) with
# Punting Form signals (weightClassRank, last600TimeRank). Validated
# against full 28-day window with these results:
#   N=120, WR=26.7%, AvgSP=$6.13, ROI=+62.1%, profit factor 1.85
# Saturday performance: 8.8 picks/Saturday, +30.3% ROI
#
# Rule: wpr_rank<=3 AND late_rank<=3 AND pf_class_rank<=1
#       AND pf_last600_rank<=3 AND fixed_win_price >= 3
#
# When PF data is missing for a meeting (PF didn't rate it), no picks
# are generated for that meeting. When TR data is missing for a runner
# (e.g. first starter with no WPR history), that runner doesn't qualify.

MODEL_DEFS = {
    "main": {
        "label":       "Main",
        "desc":        "Main: WPR≤3 + Late≤3 + ClassRank=1 + Last600≤3 + SP≥$3  OR  Sat class-up: classChange≥5 + WPR≤3 + Late≤3 + SP≥$3 (skip first-starter races)",
        # Combined backtest (28 days, Apr 9 - May 7):
        # Main rule alone: 120 picks, 26.7% WR, +62.1% ROI, 8.8/Sat
        # Sat class-up incremental: 65 picks, 15.4% WR, +27.7% ROI, 16.2/Sat
        # Combined: ~185 picks, ~22% WR weighted, ~+45% ROI weighted
        # Saturday combined: ~25/Saturday at ~+28% Saturday ROI
        # Overlap between rules is 1/66 (0.5%) - genuinely additive picks.
        "expected_wr": 0.215, "expected_roi_sp": 0.450, "expected_roi_top": 0.450,
        "bets_per_day": 6.6, "min_top_odds": 3.0,
        "is_primary":  True,
        "applies": lambda race_df, run_id, ctx:
            # Both branches require: NOT a first-starter race
            not ctx.get("has_first_starter", False)
            and (
                # RULE A: Original main rule
                # WPR top-3 + Late top-3 + Class=#1 + L600 top-3
                (
                    (ctx["wpr_rank"].get(run_id) or 99) <= 3
                    and (ctx["late_rank"].get(run_id) or 99) <= 3
                    and (ctx.get("pf_class_rank", {}).get(run_id) or 99) <= 1
                    and (ctx.get("pf_last600_rank", {}).get(run_id) or 99) <= 3
                )
                or
                # RULE B: Saturday class-up tier (NEW, ships May 2026)
                # Big class jump (>=5) + WPR top-3 + Late top-3, Saturday only.
                # Volume booster: ~16 incremental picks/Saturday at +27.7% ROI.
                # Why Saturday only: midweek class-up was H2 -4% on backtest;
                # restricting to Saturday gave +18% H1 / +18% H2 stability.
                # classChange comes from PF as numeric, NaN/None if missing.
                # The chained "or 0" handles None; pd.notna check handles NaN.
                (
                    ctx.get("dow") == "Saturday"
                    and pd.notna(ctx.get("pf_class_change", {}).get(run_id))
                    and (ctx.get("pf_class_change", {}).get(run_id) or 0) >= 5
                    and (ctx["wpr_rank"].get(run_id) or 99) <= 3
                    and (ctx["late_rank"].get(run_id) or 99) <= 3
                )
            )
            # Note: SP gate ($3) applied at display time, not at pick computation.
            # Empirically equivalent to fixed_win_price >= $3 at bet time.
    },
}


def _rank_lookup(rdf, col, ascending=False):
    """Return {run_id: rank} computed within the given race DataFrame.
    NaN values get rank None (not included in ranking)."""
    out = {}
    valid = rdf[rdf[col].notna()] if col in rdf.columns else rdf.iloc[0:0]
    if len(valid) == 0:
        return out
    sorted_df = valid.sort_values(col, ascending=ascending)
    for rank, (_, row) in enumerate(sorted_df.iterrows(), start=1):
        out[row["run_id"]] = rank
    return out


def compute_model_picks(runners_df):
    """
    Apply v3 core models to today's runners and return per-race model picks.
    Returns a list of dicts with one row per (race, model, qualifying horse).

    The output can be saved to toprate_model_picks.csv for tracking and is
    also injected into the HTML via inject_model_picks_into_selections.
    """
    rows = []
    if runners_df is None or len(runners_df) == 0:
        return rows

    for race_id, rdf in runners_df.groupby("race_id"):
        rdf = rdf.copy().reset_index(drop=True)
        n = len(rdf)
        if n == 0:
            continue

        # Pre-compute per-race rank lookups for all anchor signals
        ctx = {
            "tr_rank":      _rank_lookup(rdf, "toprate_rating",    ascending=False),
            "mid_rank":     _rank_lookup(rdf, "mid_speed_score",   ascending=False),
            "late_rank":    _rank_lookup(rdf, "late_speed_score",  ascending=False),
            "total_rank":   _rank_lookup(rdf, "total_speed_score", ascending=False),
            "early_rank":   _rank_lookup(rdf, "early_speed_score", ascending=False),
            "wpr_rank":     _rank_lookup(rdf, "wpr_nett",          ascending=False),
            "weight_trend": dict(zip(rdf["run_id"], rdf.get("weight_trend",
                                                            pd.Series([None]*n)))),
            "fix_price":    dict(zip(rdf["run_id"], rdf.get("fixed_win_price",
                                                            pd.Series([None]*n)))),
            # PF ratings - already ranked by PF (lower = better). We pass them
            # through as run_id -> rank lookups so the lambda can read them
            # alongside the TR ranks. None if PF didn't rate the runner.
            "pf_class_rank":   dict(zip(rdf["run_id"], rdf.get("pf_class_rank",
                                                                pd.Series([None]*n)))),
            "pf_last600_rank": dict(zip(rdf["run_id"], rdf.get("pf_last600_rank",
                                                                pd.Series([None]*n)))),
            "pf_ai_rank":      dict(zip(rdf["run_id"], rdf.get("pf_ai_rank",
                                                                pd.Series([None]*n)))),
            # PF classChange (numeric difference in weight class vs last start).
            # Used by the Saturday class-up tier to find horses moving up in class.
            "pf_class_change": dict(zip(rdf["run_id"], rdf.get("pf_class_change",
                                                                pd.Series([None]*n)))),
            # Day of week the race is on - needed for Saturday-only rules.
            # All runners in a race share the same date so we just need it once.
            "dow": (pd.to_datetime(rdf.iloc[0].get("date")).day_name()
                    if rdf.iloc[0].get("date") else ""),
            # True if any runner in this race has no past WPR data (first/unraced).
            # Backtest shows model picks in such races give nearly zero ROI uplift,
            # so primary model skips them. Reference models can still apply.
            "has_first_starter": bool(
                rdf["runs_with_wpr"].notna().any() and (rdf["runs_with_wpr"] == 0).any()
            ),
        }

        race_meta = rdf.iloc[0]

        for model_key, model in MODEL_DEFS.items():
            qualifying = []
            for _, row in rdf.iterrows():
                run_id = row["run_id"]
                try:
                    if model["applies"](rdf, run_id, ctx):
                        qualifying.append(row)
                except Exception:
                    pass
            for qrow in qualifying:
                rows.append({
                    "date":          race_meta.get("date"),
                    "venue":         race_meta.get("venue"),
                    "race":          race_meta.get("race"),
                    "race_id":       race_id,
                    "start_time":    race_meta.get("start_time"),
                    "model":         model_key,
                    "model_label":   model["label"],
                    "model_desc":    model["desc"],
                    "run_id":        qrow.get("run_id"),
                    "horse":         qrow.get("horse"),
                    "jockey":        qrow.get("jockey"),
                    "trainer":       qrow.get("trainer"),
                    "tab_number":    qrow.get("tab_number"),
                    "barrier":       qrow.get("barrier"),
                    "tr_rank":       ctx["tr_rank"].get(qrow["run_id"]),
                    "early_rank":    ctx["early_rank"].get(qrow["run_id"]),
                    "mid_rank":      ctx["mid_rank"].get(qrow["run_id"]),
                    "late_rank":     ctx["late_rank"].get(qrow["run_id"]),
                    "total_rank":    ctx["total_rank"].get(qrow["run_id"]),
                    "wpr_rank":      ctx["wpr_rank"].get(qrow["run_id"]),
                    # PF data for the picked runner (None if PF didn't rate)
                    "pf_ai_rank":      qrow.get("pf_ai_rank"),
                    "pf_ai_price":     qrow.get("pf_ai_price"),
                    "pf_ai_score":     qrow.get("pf_ai_score"),
                    "pf_class_rank":   qrow.get("pf_class_rank"),
                    "pf_last600_rank": qrow.get("pf_last600_rank"),
                    "pf_last400_rank": qrow.get("pf_last400_rank"),
                    "pf_last200_rank": qrow.get("pf_last200_rank"),
                    "pf_run_style":    qrow.get("pf_run_style"),
                    "pf_class_change": qrow.get("pf_class_change"),
                    "weight_trend":  qrow.get("weight_trend"),
                    "wins_at_dist":  qrow.get("wins_at_dist"),
                    "fixed_win_price": qrow.get("fixed_win_price"),
                    "starting_price_sp": qrow.get("starting_price_sp"),
                    "price_top":     qrow.get("price_top"),
                    "finish_position": qrow.get("finish_position"),
                    "won":           qrow.get("won"),
                    "placed":        qrow.get("placed"),
                    "resulted":      qrow.get("resulted"),
                })
    return rows


def save_model_picks(rows, path=None):
    """
    Save model picks to CSV.

    NOTE: stale picks for re-evaluated races are cleared FIRST by
    remove_excluded_picks_for_evaluated_races() in main(). So this function
    just appends the fresh picks. There can still be duplicate (race_id,
    run_id, model) rows if the cleanup wasn't called - dedup keeps last.
    """
    if not rows:
        return None
    if path is None:
        path = Path(__file__).parent / "toprate_model_picks.csv"
    new_df = pd.DataFrame(rows)
    new_df["race_id"] = new_df["race_id"].astype(str)
    new_df["run_id"]  = new_df["run_id"].astype(str)
    if path.exists():
        existing = pd.read_csv(path, dtype={"race_id": str, "run_id": str})
        combined = pd.concat([existing, new_df], ignore_index=True)
        combined = combined.drop_duplicates(subset=["race_id", "run_id", "model"], keep="last")
    else:
        combined = new_df
    combined.to_csv(path, index=False)
    return path


def remove_excluded_picks_for_evaluated_races(runners_df, path=None):
    """
    Drop picks from CSV for races that were evaluated this run but produced
    no qualifying horses. Without this, a race that USED to have a pick
    keeps that pick forever even after the rule excludes it.

    Called by main() right before save_model_picks. Operates on the set
    of race_ids in runners_df (i.e. races that were evaluated this run).
    """
    if path is None:
        path = Path(__file__).parent / "toprate_model_picks.csv"
    if not path.exists():
        return
    existing = pd.read_csv(path, dtype={"race_id": str, "run_id": str})
    evaluated_race_ids = set(runners_df["race_id"].astype(str).unique())
    # Keep picks NOT in the evaluated set (preserves history for older races
    # that aren't being re-evaluated this run).
    kept = existing[~existing["race_id"].isin(evaluated_race_ids)]
    if len(kept) < len(existing):
        kept.to_csv(path, index=False)
        print(f"  Cleared {len(existing) - len(kept)} stale picks from races re-evaluated this run.")


def model_picks_summary(rows, today_only=True):
    """Summarise model picks for printing at end of daily run."""
    if not rows:
        return "No model picks."
    df = pd.DataFrame(rows)
    if today_only:
        today_str = date.today().isoformat()
        df = df[df["date"] == today_str]
        if len(df) == 0:
            return f"\nNo model picks for today ({today_str}). Picks for other dates were saved to toprate_model_picks.csv."
    out = ["", "=" * 70, f"V3 MODEL PICKS - today's qualifying runners ({date.today().isoformat()})", "=" * 70]
    for model_key in MODEL_DEFS:
        sub = df[df["model"] == model_key]
        if len(sub) == 0:
            continue
        m = MODEL_DEFS[model_key]
        out.append(f"\n[{m['label']}] {m['desc']}")
        out.append(f"  Expected: {m['expected_wr']*100:.1f}% strike rate, "
                   f"ROI@SP {m['expected_roi_sp']*100:+.1f}%, "
                   f"ROI@Top {m['expected_roi_top']*100:+.1f}%")
        out.append(f"  Today: {len(sub)} qualifying runners")
        for _, r in sub.head(15).iterrows():
            time_str = ""
            if r.get("start_time"):
                try:
                    time_str = pd.to_datetime(r["start_time"]).strftime("%H:%M")
                except Exception:
                    pass
            price_str = ""
            if pd.notna(r.get("fixed_win_price")):
                price_str = f" @${r['fixed_win_price']:.1f}"
            out.append(f"    {time_str:<6} {r.get('venue', '?'):<14} "
                       f"R{r.get('race', '?')}: {r.get('horse', '?')}{price_str}")
        if len(sub) > 15:
            out.append(f"    ... and {len(sub)-15} more")
    return "\n".join(out)


# -----------------------------------------------------------------------
# CUMULATIVE PREDICTIVE SCORE
# -----------------------------------------------------------------------
# Designed for use as a tipping aid for quaddies / exotics rather than for
# straight win-betting (the v3 primary model `main` already handles win
# betting filtering). Validated against the Apr 9 - May 7 backtest data.
#
# Formula (Path B proxy, version 1):
#     score = 2.0 * tr_pct + 0.5 * wpr_avg_last3_pct + 0.3 * late_speed_pct
# where each *_pct is the within-race percentile rank (1.0 = best in field,
# 0.0 = worst). Missing values get 0 (effectively pushed to the bottom).
#
# Validation (full 1608-race backtest, 14,924 runners):
#     rk1 horse: 33.6% WR, 67.4% PR, 76% top-4 rate
#     rk2 horse: 19.9% WR, 55.2% PR
#     rk3 horse: 14.6% WR, 47.2% PR
#     Coverage: top-2 picks contain winner 54%, top-3 contain winner 69%
#     Place coverage: top-3 picks contain at least 1 of top-3 finishers 95%
#
# Future upgrade path (Path A): replace this with
#     score = 1.0 * jt_combo_pct + 1.2 * tr_pct
# once jockey/trainer combo win % is fetched from the API. That formula
# improves rk1 WR to 44%, top-3 winner-coverage to 80%.
#
# This module supports BOTH formulas. compute_cumulative_score auto-detects
# whether jt_combo_win_pct is populated for the race (>= 50% of runners with
# data) and switches to the Path A formula automatically. If not, the proxy
# formula is used. This means the upgrade ships transparently as soon as the
# API integration starts returning the field.
# Future upgrade path (Path A): replace this with
#     score = 1.0 * jt_combo_pct + 1.2 * tr_pct
# once jockey/trainer combo win % is fetched from the API.
#
# DATA INTEGRITY WARNING (2026-05-08):
# The backtest xlsx export's jt_combo fields appear to contain lookahead leakage.
# Re-running the threshold P&L analysis showed Path B (no jt_combo) gives -15%
# ROI flat-betting at SP (realistic - bookmaker over-round) but Path A gives +20%
# ROI which is implausibly profitable. The 30-point swing comes from jt_combo
# values that were calculated AFTER the period and applied retroactively.
#
# Until we have a confirmed "as at race date" jt_combo source from the live API
# (see DIAG: logging in build_stats_lookup), JT_COMBO_TRUST is False so all
# races use Path B regardless of jt_combo presence in the CSV. Once the live
# API integration is verified clean, flip this flag.
JT_COMBO_TRUST = False

SCORE_WEIGHTS_PROXY = {
    # Path B (current default): TR-dominant proxy. 33% rk1 WR, -15% ROI@SP flat.
    "toprate_rating":   2.0,
    "wpr_avg_last3":    0.5,
    "late_speed_score": 0.3,
}
SCORE_WEIGHTS_FULL = {
    # Path A (disabled until clean data): jt_combo + TR.
    "jt_combo_win_pct": 1.0,
    "toprate_rating":   1.2,
}
# Min coverage of jt_combo_win_pct in a race (as a fraction of runners) before
# the Path A formula is used. Below this we fall back to Path B for that race.
SCORE_PATH_A_MIN_COVERAGE = 0.5

# Backwards-compat alias (other callers may reference this directly)
SCORE_WEIGHTS = SCORE_WEIGHTS_PROXY
SCORE_DIRECTION = "higher"


# Constants for jockey/trainer combo Bayesian shrinkage. Used IF Path A is ever
# enabled and we have clean (non-leaky) data. Without shrinkage, small-sample
# pairs (e.g. 3 wins from 5 rides = 60%) would dominate the score even when
# their high win rate is just statistical noise.
JT_COMBO_PRIOR_WR = 9.0       # population avg jockey strike rate
JT_COMBO_PRIOR_STRENGTH = 30  # equivalent "rides of average evidence" for the prior


def _shrink_jt_combo(rdf):
    """
    Apply Bayesian shrinkage to jt_combo_win_pct in-place on a copy of the dataframe.
    Returns a NEW dataframe with the column adjusted. Pairs with few rides get
    pulled toward the population mean; pairs with many rides barely change.
    """
    if "jt_combo_win_pct" not in rdf.columns or "jt_combo_rides" not in rdf.columns:
        return rdf

    df = rdf.copy()
    rides = pd.to_numeric(df["jt_combo_rides"], errors="coerce")
    wpct  = pd.to_numeric(df["jt_combo_win_pct"], errors="coerce")
    # Shrink: posterior = (rides * raw_wr + strength * prior) / (rides + strength)
    shrunk = (
        (rides * wpct + JT_COMBO_PRIOR_STRENGTH * JT_COMBO_PRIOR_WR)
        / (rides + JT_COMBO_PRIOR_STRENGTH)
    )
    # Where data is missing, leave as NaN
    shrunk = shrunk.where(rides.notna() & wpct.notna(), other=None)
    df["jt_combo_win_pct"] = shrunk
    return df


def _resolve_score_weights(rdf):
    """Decide which formula to use for this race based on jt_combo_win_pct coverage."""
    # Path A is only used if the global trust flag is on AND coverage is sufficient.
    # See JT_COMBO_TRUST docstring above for why this defaults to False.
    if not JT_COMBO_TRUST:
        return SCORE_WEIGHTS_PROXY, "B"
    if "jt_combo_win_pct" in rdf.columns:
        non_null = pd.to_numeric(rdf["jt_combo_win_pct"], errors="coerce").notna().sum()
        if non_null >= len(rdf) * SCORE_PATH_A_MIN_COVERAGE:
            return SCORE_WEIGHTS_FULL, "A"
    return SCORE_WEIGHTS_PROXY, "B"


def compute_cumulative_score(rdf):
    """
    For a single race DataFrame, compute a per-runner cumulative score, rank,
    and confidence metric.

    Returns: dict(run_id -> {
        score: float in [0,1] - weighted percentile-rank composite
        rank: int 1..N - rank within race by score
        path: 'A'|'B' - which formula was used
        conf: float in [0,1] - signal agreement (1 = unanimous, 0 = split)
        sigs: dict(sig_name -> percentile) - per-signal percentile breakdown
    })

    Confidence is computed as 1 - (sd / max_sd) where sd is the standard
    deviation of the horse's percentile ranks across signals, and max_sd is
    the theoretical max (~0.5 for percentiles in [0,1] split bimodally).
    A horse with all signals percentile-ranked in tight cluster gets high
    conf. A horse where signals disagree wildly gets low conf.

    The 'sigs' breakdown lets the detail panel show signal-by-signal so the
    user can see exactly which signals agreed and which disagreed.
    """
    n = len(rdf)
    if n == 0:
        return {}
    # Apply Bayesian shrinkage to jt_combo so small-sample pairs don't dominate
    rdf = _shrink_jt_combo(rdf)

    if n == 1:
        rid = str(rdf.iloc[0].get("run_id", ""))
        weights, path = _resolve_score_weights(rdf)
        return {rid: {"score": 1.0, "rank": 1, "path": path, "conf": 1.0, "sigs": {}}}

    weights, path = _resolve_score_weights(rdf)
    total_w = sum(weights.values())
    runner_scores = [0.0] * n  # positional
    # Track per-signal percentile per runner (for confidence calc + detail panel)
    runner_sigs = [dict() for _ in range(n)]

    for sig, w in weights.items():
        if sig not in rdf.columns:
            continue
        col = pd.to_numeric(rdf[sig], errors="coerce")
        # Rank descending (higher = rank 1 = best). NaNs to bottom.
        rk = col.rank(method="min", ascending=False, na_option="bottom")
        for i in range(n):
            r = rk.iloc[i]
            if pd.isna(r):
                continue
            # Convert rank to percentile in [0, 1]: rank 1 -> 1.0, rank N -> 0.0
            pct = (n - r) / (n - 1)
            runner_scores[i] += w * pct
            runner_sigs[i][sig] = round(pct, 3)

    # Normalise to [0, 1]
    runner_scores = [s / total_w for s in runner_scores]

    # Compute ranks (1 = highest score)
    indexed = sorted(enumerate(runner_scores), key=lambda x: -x[1])
    ranks = [0] * n
    for rank_pos, (idx, _) in enumerate(indexed, start=1):
        ranks[idx] = rank_pos

    # Confidence: low standard deviation across signals = high agreement.
    # Max possible SD for 2+ values in [0,1] is 0.5 (perfectly bimodal).
    # We invert so 1 = tight cluster (high confidence), 0 = wide spread.
    # Horses with only 1 signal populated get conf = None (can't measure agreement).
    MAX_SD = 0.5

    out = {}
    for i in range(n):
        rid = str(rdf.iloc[i].get("run_id", ""))
        sigs = runner_sigs[i]
        if len(sigs) < 2:
            conf = None
        else:
            vals = list(sigs.values())
            mean_v = sum(vals) / len(vals)
            var = sum((v - mean_v) ** 2 for v in vals) / len(vals)
            sd = var ** 0.5
            conf = max(0.0, min(1.0, 1.0 - (sd / MAX_SD)))
            conf = round(conf, 3)
        out[rid] = {
            "score": round(runner_scores[i], 4),
            "rank":  ranks[i],
            "path":  path,
            "conf":  conf,
            "sigs":  sigs,
        }
    return out


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
        # Filter out non-TAB meetings by prize money. We keep these in the CSV
        # (saved by daily ingestion) but exclude from all downstream processing.
        # User can't bet on bush meetings at TAB, so they shouldn't clutter the UI.
        if "prize_money" in df.columns:
            before_tab = len(df)
            df = df[df["prize_money"].fillna(0) >= TAB_PRIZE_MIN].reset_index(drop=True)
            removed = before_tab - len(df)
            if removed > 0:
                print(f"  Filtered out {removed} non-TAB runners (prize_money < ${TAB_PRIZE_MIN:,})")
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
    skipped_future = 0
    skipped_old = 0
    api_calls = 0

    # ── Build start-time lookup so we can skip races that haven't started ──
    # We compute "now" with a 5-minute buffer (results aren't immediate)
    now = datetime.now()
    five_min_ago = now - timedelta(minutes=5)
    cutoff_old = today - timedelta(days=14)  # don't keep retrying ancient races

    for race_id in race_ids:
        mask = runners_df["race_id"].astype(str) == str(race_id)
        sample = runners_df[mask].iloc[0]
        race_date = pd.to_datetime(sample["date"]).date() if sample.get("date") else None

        # Skip races scheduled for future dates
        if race_date and race_date > today:
            skipped_future += 1
            continue

        # Skip races more than 14 days old that still aren't resulted - the API
        # almost certainly won't give them now and we burn API calls every run.
        if race_date and race_date < cutoff_old:
            skipped_old += 1
            continue

        # For races on TODAY, check if they've actually started yet.
        # If start_time is in the future (with 5-minute buffer), skip.
        if race_date == today:
            start_time_str = sample.get("start_time")
            if start_time_str:
                try:
                    # start_time is HH:MM, combine with today's date
                    hh, mm = str(start_time_str).split(":")[:2]
                    race_start = datetime.combine(today, datetime.min.time()).replace(
                        hour=int(hh), minute=int(mm))
                    if race_start > five_min_ago:
                        skipped_future += 1
                        continue
                except Exception:
                    pass  # if we can't parse, fall through and call API

        try:
            api_calls += 1
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

            time.sleep(0.1)  # reduced from 0.3 - API hasn't been rate-limiting us
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
            time.sleep(0.1)  # reduced from 0.3 - API hasn't been rate-limiting

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

    races_data = []
    for race_id, rdf in runners_df.groupby("race_id"):
        rdf = rdf.copy().reset_index(drop=True)
        if len(rdf) == 0:
            continue
        first = rdf.iloc[0]

        # Per-race cumulative score: predictive composite for quaddie/exotic use
        # Returns dict run_id -> {score: 0..1, rank: 1..N}. See compute_cumulative_score.
        cum_lookup = compute_cumulative_score(rdf)

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

    # ── Build model meta from MODEL_DEFS ─────────────────────────────────────
    primary_key = next((k for k, v in MODEL_DEFS.items() if v.get("is_primary")),
                       "main")
    model_meta = {
        k: {
            "label":   v["label"],
            "desc":    v["desc"],
            "wr":      v["expected_wr"],
            "roi_sp":  v["expected_roi_sp"],
            "roi_top": v["expected_roi_top"],
            "per_day": v["bets_per_day"],
            "min_odds": v.get("min_top_odds", 0),  # threshold applied at bet placement
        } for k, v in MODEL_DEFS.items()
    }

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
    now_iso  = datetime.now().isoformat()
    run_date = datetime.now().strftime("%d %b %Y %H:%M")
    html = render_html(
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
    for f in ["toprate_live.html", "toprate_runners.csv",
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

    # ── Step 2b: Merge in Punting Form ratings ──────────────────────────────
    # PF data is the foundation of the new unified model rule. It's pulled
    # by puntingform_ingest.py (separate cron) into puntingform_data/pf_ratings.csv.
    # The merge is keyed on (date, venue, race_no, horse_name lower-cased).
    print("── Step 2b: Merging Punting Form ratings ──")
    runners_df = merge_pf_ratings(runners_df)
    print()

    save_runners(runners_df)
    print(f"Saved -> {RUNNERS_CSV} ({len(runners_df):,} runners, {runners_df['race_id'].nunique():,} races)")
    
    # Snapshot prices for drift tracking
    print("  Snapshotting prices for drift tracking…")
    snapshot_prices(runners_df)
    print()

    # ── V3 Core Model picks (walk-forward verified filters) ──
    print("── Step 3: Computing v3 model picks ──")
    # First clear stale picks for races we're about to re-evaluate. Without
    # this, a race that USED to qualify a horse keeps that pick forever even
    # if the rule has changed (e.g. first-starter exclusion now removes it).
    remove_excluded_picks_for_evaluated_races(runners_df)
    # Compute picks for EVERY race in the dataframe, not just today's. This way
    # historical data already in toprate_runners.csv (e.g. yesterday's races
    # whose results came in overnight) get picks computed and saved too.
    # The picks CSV dedupes on (run_id, model) so re-runs are safe.
    model_pick_rows = compute_model_picks(runners_df)
    saved_path = save_model_picks(model_pick_rows)
    if saved_path:
        n_picks = len(model_pick_rows)
        n_horses = len({r["run_id"] for r in model_pick_rows})
        print(f"  {n_picks} model-pick rows ({n_horses} unique horses) saved -> {saved_path.name}")
    print(model_picks_summary(model_pick_rows))
    print()

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
