"""
toprate_html_v3.py
==================
Clean dashboard rebuild for the v3 primary model:
  TR<=3 + Mid+Late+Total top 2 + min Top $3

Architecture:
  - render_html(races, model_picks, model_meta, price_hist, run_date, stats)
    returns a complete HTML document string ready to write to disk
  - All data flows in via JSON-serialisable dicts/lists
  - Single primary model 'main' is the only one displayed for betting
  - Reference models 'top_form' and 'tr1_min4' are tracked but not displayed

Tabs:
  TODAY   - chronological list of today's primary model picks
  RACE    - meeting/race navigator with full field grid
  PNL     - settled bet history + cumulative units chart
  INSIGHTS - rolling model performance metrics + reference comparison
  SETTINGS - unit size, display preferences

Stake rule: stake = round(4 / price, 2), min 0.25u, max 4u, "bet to return 4u" (gross)
Stake price source: fixed_win_price (current bookie price), or oddsTaken if entered.
"""

import json
import gzip
import csv
from pathlib import Path
from datetime import datetime


# ── Venue bias lookup ──────────────────────────────────────────────────
# Loaded from /home/claude/toprate_venue_history.json.gz which is populated
# by backfill_venue_history.py. The file is a list of race-level records
# each with {venue, date, going, rail, distance, winnerZone, ...}.
# We turn that into two lookups for the bias commentary:
#   1. By (venue, going_cat, rail) - the most-specific filter
#   2. By venue alone - the venue's all-conditions baseline
# Each lookup gives {leaders, onpace, midfield, back} winner-zone counts
# plus total race count.
VENUE_HISTORY_FILE = Path(__file__).parent / "toprate_venue_history.json.gz"

# PF barrier x runstyle A2E bias data. Written by puntingform_ingest.py
# (the speedmaps endpoint). Each meeting yields 4 rows: barrier bands
# 1-3, 4-7, 8+ and a Totals row, with A2E figures for Forward / Midfield /
# Back run styles. We surface this on the race detail panel as a 4x3
# grid alongside the existing winner-zone bias chart.
PF_BARRIER_BIAS_FILE = (
    Path(__file__).parent / "puntingform_data" / "pf_barrier_bias.csv"
)


def _going_category(going):
    """Bucket a going string into Firm/Good/Soft/Heavy/Synthetic."""
    if not going:
        return ""
    g = str(going).lower()
    if g.startswith("firm"):  return "Firm"
    if g.startswith("good"):  return "Good"
    if g.startswith("soft"):  return "Soft"
    if g.startswith("heavy"): return "Heavy"
    if g.startswith("synth"): return "Synthetic"
    return going


def _normalize_rail(rail):
    """
    Normalize rail-position strings so 'Out 8m' and 'Out 8m Entire Circuit'
    bucket together. We strip 'Entire Circuit' / leading/trailing whitespace.
    """
    if not rail:
        return ""
    r = str(rail).replace("Entire Circuit", "").strip()
    return r or "Unknown"


def load_venue_bias_lookup():
    """
    Load venue history file and compute the two lookups.

    Returns:
        {
          'byVenueGoingRail': {
              'Caulfield|Good|True': {'l':12, 'o':18, 'm':9, 'b':3, 'n':42},
              ...
          },
          'byVenue': {
              'Caulfield': {'l':45, 'o':102, 'm':87, 'b':22, 'n':256},
              ...
          },
          'totalRaces': 4521
        }

    Returns empty structure if file doesn't exist (graceful fallback so
    bias commentary just shows 'insufficient sample' until backfill runs).
    """
    if not VENUE_HISTORY_FILE.exists():
        return {"byVenueGoingRail": {}, "byVenue": {}, "totalRaces": 0}

    try:
        with gzip.open(VENUE_HISTORY_FILE, "rt", encoding="utf-8") as f:
            races = json.load(f)
    except Exception as e:
        print(f"  ! venue history load failed ({e})")
        return {"byVenueGoingRail": {}, "byVenue": {}, "totalRaces": 0}

    by_specific = {}
    by_venue = {}

    for race in races:
        venue = race.get("venue") or ""
        going = _going_category(race.get("going") or "")
        rail = _normalize_rail(race.get("rail") or "")
        wzone = race.get("winnerZone")
        if not venue or not wzone:
            continue
        zone_letter = {
            "leaders":  "l",
            "onpace":   "o",
            "midfield": "m",
            "back":     "b",
        }.get(wzone)
        if not zone_letter:
            continue

        # Specific bucket
        spec_key = f"{venue}|{going}|{rail}"
        if spec_key not in by_specific:
            by_specific[spec_key] = {"l": 0, "o": 0, "m": 0, "b": 0, "n": 0}
        by_specific[spec_key][zone_letter] += 1
        by_specific[spec_key]["n"] += 1

        # Venue-wide bucket
        if venue not in by_venue:
            by_venue[venue] = {"l": 0, "o": 0, "m": 0, "b": 0, "n": 0}
        by_venue[venue][zone_letter] += 1
        by_venue[venue]["n"] += 1

    return {
        "byVenueGoingRail": by_specific,
        "byVenue":          by_venue,
        "totalRaces":       len(races),
    }


def load_pf_barrier_bias():
    """
    Load PF barrier x runstyle bias from pf_barrier_bias.csv (written by
    puntingform_ingest.py via the User/Speedmaps endpoint).

    PF re-derives these lifetime A2E figures nightly. Each meeting we've
    ingested has 4 rows (1-3, 4-7, 8+, Totals). When the same venue appears
    on multiple dates we keep the MOST RECENT row per band so the lookup
    reflects PF's current view, not stale snapshots.

    Returns:
        {
          'byVenue': {
            'Moe': {
              'railPosition': '3-7',
              'antiClockwise': True,
              'asOf': '2026-05-12',
              'bands': [
                {'band':'1-3',    'forward':0.80, 'midfield':0.98, 'back':0.66},
                {'band':'4-7',    'forward':0.91, 'midfield':1.14, 'back':1.02},
                {'band':'8+',     'forward':0.86, 'midfield':1.10, 'back':1.19},
                {'band':'Totals', 'forward':0.86, 'midfield':1.08, 'back':0.97},
              ],
            },
            ...
          }
        }

    Returns empty {byVenue: {}} if file doesn't exist (graceful fallback so
    the panel just shows "no PF data yet" until ingest runs).
    """
    if not PF_BARRIER_BIAS_FILE.exists():
        return {"byVenue": {}}

    # Most-recent date per (venue, band) wins. We sort by date asc and
    # overwrite as we go - last write is freshest.
    by_venue = {}
    try:
        with PF_BARRIER_BIAS_FILE.open("r", newline="", encoding="utf-8") as f:
            rows = list(csv.DictReader(f))
    except (OSError, csv.Error) as e:
        print(f"  ! pf_barrier_bias load failed ({e})")
        return {"byVenue": {}}

    # Sort by date ascending so later rows clobber earlier ones below
    rows.sort(key=lambda r: r.get("_pf_date") or "")

    # Float coercion - some empty A2E cells exist for low-sample bands
    def _f(v):
        if v is None or v == "":
            return None
        try:
            return float(v)
        except (TypeError, ValueError):
            return None

    def _b(v):
        # CSV stores booleans as "True"/"False" strings
        if isinstance(v, bool):
            return v
        if isinstance(v, str):
            return v.strip().lower() == "true"
        return None

    for row in rows:
        venue = (row.get("_pf_venue") or "").strip()
        band = (row.get("barrier_band") or "").strip()
        if not venue or not band:
            continue
        v_entry = by_venue.setdefault(venue, {
            "railPosition":  None,
            "antiClockwise": None,
            "asOf":          None,
            "bands":         {},
        })
        # Meeting-level metadata - update with latest seen (sort guarantees freshness)
        v_entry["railPosition"]  = row.get("rail_position") or v_entry["railPosition"]
        v_entry["antiClockwise"] = _b(row.get("anti_clockwise"))
        v_entry["asOf"]          = row.get("_pf_date") or v_entry["asOf"]
        v_entry["bands"][band] = {
            "band":     band,
            "forward":  _f(row.get("a2e_forward")),
            "midfield": _f(row.get("a2e_midfield")),
            "back":     _f(row.get("a2e_back")),
        }

    # Flatten bands dict to ordered list (1-3, 4-7, 8+, Totals)
    band_order = ["1-3", "4-7", "8+", "Totals"]
    for venue, entry in by_venue.items():
        ordered = []
        bands_dict = entry["bands"]
        for b in band_order:
            if b in bands_dict:
                ordered.append(bands_dict[b])
        # Any unrecognised bands appended after, sorted
        extras = sorted(k for k in bands_dict if k not in band_order)
        for b in extras:
            ordered.append(bands_dict[b])
        entry["bands"] = ordered

    return {"byVenue": by_venue}


# ── Aesthetic tokens ────────────────────────────────────────────────────────
# Dominant: cool stone neutrals + emerald accent for primary model picks
# Status: red for losses, emerald for wins, amber for warnings, slate for neutral
CSS_TOKENS = """
:root {
  --bg: #f4f6f9;
  --panel: #ffffff;
  --panel-elev: #ffffff;
  --line: #e8eaf0;
  --line-soft: #f1f3f8;
  --ink: #0f1729;
  --ink-soft: #374151;
  --ink-mute: #6b7280;
  --ink-faint: #9ca3af;

  --emerald: #059669;
  --emerald-bg: #ecfdf5;
  --emerald-line: #a7f3d0;
  --emerald-deep: #047857;

  --rose: #dc2626;
  --rose-bg: #fef2f2;
  --rose-line: #fecaca;

  --amber: #d97706;
  --amber-bg: #fffbeb;
  --amber-line: #fde68a;

  --slate: #475569;
  --slate-bg: #f1f5f9;

  --indigo: #4338ca;
  --indigo-bg: #eef2ff;

  --shadow-1: 0 1px 2px rgba(28,25,23,.04);
  --shadow-2: 0 4px 12px rgba(28,25,23,.06);
  --radius-sm: 6px;
  --radius-md: 10px;
  --radius-lg: 14px;

  --font-mono: 'IBM Plex Mono', ui-monospace, 'SF Mono', Menlo, monospace;
  --font-display: 'Outfit', sans-serif;
  --font-body: 'Outfit', sans-serif;
}
"""


def _safe(v, default=None):
    if v is None:
        return default
    try:
        if isinstance(v, float) and v != v:  # NaN
            return default
    except Exception:
        pass
    return v


def render_html(*, races, model_picks_by_race, model_meta, price_hist,
                run_date, run_iso, model_pick_rows, primary_model_key='main',
                github_repo='mattdwyer01/TopRate'):
    """
    Render the full v3 HTML dashboard.

    Parameters
    ----------
    races : list of dict
        One per race. Must include race_id, date, venue, race, distance,
        going, prize, start_time, runners, and per-runner fields.
    model_picks_by_race : dict
        race_id -> {model_key: [{run_id, horse, ...}, ...]}
    model_meta : dict
        model_key -> {label, desc, wr, roi_sp, roi_top, per_day, min_odds}
    price_hist : dict
        run_id -> [(timestamp, price), ...]
    run_date : str
        Display string for the run timestamp ('07 May 2026 13:35')
    run_iso : str
        ISO timestamp for relative-time computation in JS
    model_pick_rows : list of dict
        Flat picks list (used for PNL tab settled bet history)
    primary_model_key : str
        Which model_meta key is the betting model (default 'main')
    github_repo : str
        GitHub repo path 'owner/name' for Actions trigger button
    """
    primary = model_meta.get(primary_model_key, {})

    # Sanitise model_pick_rows for JSON (numpy/pandas types -> native Python)
    def _to_json_safe(v):
        if v is None:
            return None
        # Handle pandas/numpy types
        try:
            import math as _m
            if hasattr(v, 'item'):  # numpy scalars
                v = v.item()
            if isinstance(v, float) and _m.isnan(v):
                return None
        except Exception:
            pass
        return v

    safe_pick_rows = []
    for r in (model_pick_rows or []):
        safe_pick_rows.append({k: _to_json_safe(v) for k, v in r.items()})
    model_pick_rows = safe_pick_rows


    # Build picks list (all dates - JS filters to today's local date)
    # All models included; each pick tagged with 'model' so JS sub-tabs can
    # filter by active model on Today/P&L. Previously only primary_model_key
    # picks were emitted - changed when the "loose" experimental model was
    # added so users can flip between them in the dashboard.
    all_picks_list = []
    for race_id, models in model_picks_by_race.items():
        for model_key, picks in models.items():
            for pick in picks:
                # Find the parent race row for context
                race = next((r for r in races if str(r.get('race_id')) == str(race_id)), None)
                if not race:
                    continue
                all_picks_list.append({
                    'race_id': race_id,
                    'model': model_key,
                    'date': race.get('date'),
                    'venue': race.get('venue'),
                    'race': race.get('race'),
                    'race_name': race.get('race_name'),
                    'start_time': race.get('start_time'),
                    'distance': race.get('distance'),
                    'going': race.get('going'),
                    'track_grading': race.get('track_grading'),
                    'prize': race.get('prize'),
                    'pace_score': race.get('pace_score'),
                    'field_size': race.get('fs'),
                    'rse': race.get('rse'),
                    'rsm': race.get('rsm'),
                    'rsl': race.get('rsl'),
                    'run_id': pick.get('run_id'),
                    'horse': pick.get('horse'),
                    'tab': pick.get('tab'),
                    'fxprice': pick.get('fxprice'),
                    'sp':      pick.get('starting_price_sp'),
                    'top':     pick.get('price_top'),
                    'tr_rank': pick.get('tr_rank'),
                    'early_rank': pick.get('early_rank'),
                    'mid_rank': pick.get('mid_rank'),
                    'late_rank': pick.get('late_rank'),
                    'total_rank': pick.get('total_rank'),
                    'wpr_rank': pick.get('wpr_rank'),
                    'pfaiR':   pick.get('pf_ai_rank'),
                    'pfaiPrc': pick.get('pf_ai_price'),
                    'wcR':     pick.get('pf_class_rank'),
                    'l600R':   pick.get('pf_last600_rank'),
                    'l400R':   pick.get('pf_last400_rank'),
                    'l200R':   pick.get('pf_last200_rank'),
                    'rs':      pick.get('pf_run_style'),
                    'clsChg':  pick.get('pf_class_change'),
                })
    # Enrich with finish data and full per-runner context from races
    # Also compute Early and Total ranks per race (these may be missing from old picks CSVs)
    for tp in all_picks_list:
        race = next((r for r in races if str(r.get('race_id')) == str(tp['race_id'])), None)
        if race:
            runners_in_race = race.get('runners', [])
            runner = next((u for u in runners_in_race
                           if str(u.get('rid')) == str(tp['run_id'])), None)
            if runner:
                tp['runner_full'] = runner
                # Surface cumulative score directly on the pick for easy JS access
                tp['cs']  = runner.get('cs')
                tp['crk'] = runner.get('crk')
                # Confidence: signal-agreement metric (1 = unanimous, 0 = split)
                tp['csc'] = runner.get('csc')

            # Backfill wpr_rank for picks whose CSV row was written before the
            # column existed. Recompute from the race's runner list using the
            # same convention as the daily script (highest wpr_nett = rank 1).
            if tp.get('wpr_rank') is None and runners_in_race:
                wpr_pairs = [(str(u.get('rid')), u.get('w'))
                             for u in runners_in_race if u.get('w') is not None]
                wpr_pairs.sort(key=lambda x: x[1], reverse=True)
                for idx, (rid, _) in enumerate(wpr_pairs):
                    if rid == str(tp['run_id']):
                        tp['wpr_rank'] = idx + 1
                        break
            tp['done'] = race.get('done')
            # Surface first-starter flag at race level so detail panels can warn
            tp['hfs'] = bool(race.get('hfs'))

            # Compute ranks if missing from pick payload
            def _rank_in_race(field, my_rid):
                # higher value = better rank (rank 1 = highest)
                vals = [(u.get('rid'), u.get(field)) for u in runners_in_race
                        if u.get(field) is not None]
                if not vals:
                    return None
                # Sort descending by value, find my position
                vals.sort(key=lambda x: -x[1])
                for i, (rid, _) in enumerate(vals):
                    if str(rid) == str(my_rid):
                        return i + 1
                return None
            if 'early_rank' not in tp or tp.get('early_rank') is None:
                tp['early_rank'] = _rank_in_race('es', tp['run_id'])
            if 'total_rank' not in tp or tp.get('total_rank') is None:
                tp['total_rank'] = _rank_in_race('ts', tp['run_id'])
    # Sort chronologically by date+start_time so JS can filter and the order is correct
    all_picks_list.sort(key=lambda t: (t.get('date') or '', t.get('start_time') or '', t.get('race') or 0))
    today_picks = all_picks_list  # keep variable name for JSON injection

    # Build settled bet history for ALL models. Each entry tagged with 'model'
    # so JS can filter by active model on the P&L sub-tab. Previously only the
    # primary model's settled rows were emitted - changed when "loose"
    # experimental model was added.
    settled_history = []
    for r in (model_pick_rows or []):
        if not r.get('resulted'):
            continue
        race_id = r.get('race_id')
        run_id = r.get('run_id')
        race = next((rc for rc in races if str(rc.get('race_id')) == str(race_id)), None)
        runner_full = None
        if race:
            runner_full = next((u for u in race.get('runners', []) if str(u.get('rid')) == str(run_id)), None)
        settled_history.append({
            'model': r.get('model'),
            'date': r.get('date'),
            'venue': r.get('venue'),
            'race': r.get('race'),
            'race_id': race_id,
            'horse': r.get('horse'),
            'tab': r.get('tab_number'),
            'jockey': r.get('jockey'),
            'trainer': r.get('trainer'),
            'run_id': run_id,
            'start_time': r.get('start_time'),
            'distance': race.get('distance') if race else None,
            'going': race.get('going') if race else None,
            'field_size': race.get('fs') if race else None,
            'hfs': bool(race.get('hfs')) if race else False,
            'fxprice': r.get('fixed_win_price'),
            'sp': r.get('starting_price_sp'),
            'top': r.get('price_top'),
            'finish': r.get('finish_position'),
            'won': bool(r.get('won')),
            'placed': bool(r.get('placed')),
            'tr_rank': r.get('tr_rank'),
            'mid_rank': r.get('mid_rank'),
            'late_rank': r.get('late_rank'),
            'early_rank': r.get('early_rank'),
            'total_rank': r.get('total_rank'),
            'wpr_rank': r.get('wpr_rank'),
            'pfaiR':   r.get('pf_ai_rank'),
            'pfaiPrc': r.get('pf_ai_price'),
            'wcR':     r.get('pf_class_rank'),
            'l600R':   r.get('pf_last600_rank'),
            'l400R':   r.get('pf_last400_rank'),
            'l200R':   r.get('pf_last200_rank'),
            'rs':      r.get('pf_run_style'),
            'clsChg':  r.get('pf_class_change'),
            'cs':  runner_full.get('cs')  if runner_full else None,
            'crk': runner_full.get('crk') if runner_full else None,
            'csc': runner_full.get('csc') if runner_full else None,
            'runner_full': runner_full,
        })
    settled_history.sort(key=lambda r: (r.get('date') or ''))

    # Load precomputed venue bias lookup. This is built incrementally by
    # backfill_venue_history.py and read here at HTML build time. If the
    # file isn't there yet (first time running before backfill), the
    # lookup is empty and the JS commentary falls back to "insufficient
    # sample" gracefully.
    venue_bias = load_venue_bias_lookup()
    # PF barrier x runstyle A2E bias - meeting-level data from the PF
    # speedmaps endpoint. Renders as a 4x3 grid next to the existing
    # winner-zone bias chart on the race detail panel.
    pf_barrier_bias = load_pf_barrier_bias()

    # JSON payloads injected into the page
    js_data = (
        "const RACES = "        + json.dumps(races,                separators=(',', ':')) + ";\n"
        "const PICKS_TODAY = "  + json.dumps(today_picks,          separators=(',', ':')) + ";\n"
        "const SETTLED = "      + json.dumps(settled_history,      separators=(',', ':')) + ";\n"
        "const PRICE_HIST = "   + json.dumps(price_hist or {},     separators=(',', ':')) + ";\n"
        "const MODEL_META = "   + json.dumps(model_meta,           separators=(',', ':')) + ";\n"
        "const MODEL_PICKS = "  + json.dumps(model_picks_by_race,  separators=(',', ':')) + ";\n"
        "const ALL_PICKS_FLAT = " + json.dumps(model_pick_rows or [], separators=(',', ':')) + ";\n"
        "const PRIMARY_KEY = "  + json.dumps(primary_model_key)        + ";\n"
        "const RUN_DATE = "     + json.dumps(run_date)                 + ";\n"
        "const RUN_ISO = "      + json.dumps(run_iso)                  + ";\n"
        "const GITHUB_REPO = "  + json.dumps(github_repo)              + ";\n"
        "const VENUE_BIAS = "   + json.dumps(venue_bias, separators=(',', ':')) + ";\n"
        "const PF_BARRIER_BIAS = " + json.dumps(pf_barrier_bias, separators=(',', ':')) + ";\n"
    )

    return _HTML_TEMPLATE.format(
        css_tokens=CSS_TOKENS,
        css=_CSS,
        js_data=js_data,
        js_app=_JS_APP,
        primary_label=primary.get('label', 'Main'),
        primary_desc=primary.get('desc', ''),
        primary_wr=f"{primary.get('wr', 0)*100:.1f}",
        primary_roi_sp=f"{primary.get('roi_sp', 0)*100:+.1f}",
        primary_roi_top=f"{primary.get('roi_top', 0)*100:+.1f}",
        primary_per_day=f"{primary.get('per_day', 0):.1f}",
        run_date=run_date,
        n_today=len(today_picks),
        n_settled=len(settled_history),
    )


# ── CSS ─────────────────────────────────────────────────────────────────────
_CSS = """
* { box-sizing: border-box; margin: 0; padding: 0; }
html { scroll-behavior: smooth; }
@keyframes highlight {
  0%   { background: var(--emerald-bg); }
  100% { background: transparent; }
}
body {
  background: var(--bg);
  color: var(--ink-soft);
  font-family: var(--font-body);
  font-size: 13px;
  line-height: 1.45;
  -webkit-font-smoothing: antialiased;
  text-rendering: optimizeLegibility;
}

/* Layout shell */
.shell { max-width: 1440px; margin: 0 auto; padding: 0 20px; }
@media (max-width: 720px) { .shell { padding: 0 12px; } }

/* Top bar - compact, just a thin status strip */
.topbar {
  display: flex; align-items: center; justify-content: space-between;
  padding: 16px 0 14px; border-bottom: 1px solid var(--line);
  margin-bottom: 18px;
}
.topbar-compact {
  padding: 10px 0 8px; border-bottom: none; margin-bottom: 8px;
  justify-content: flex-end;
}
.topbar-left { display: flex; align-items: baseline; gap: 14px; }
.topbar-right { display: flex; align-items: center; gap: 10px; }
.run-stamp {
  font-family: var(--font-body); font-size: 11px; color: var(--ink-mute);
  font-weight: 500;
}
.brand-mark {
  display: inline-block; width: 6px; height: 6px; background: var(--emerald);
  border-radius: 50%; margin-right: 8px; vertical-align: middle;
}
.unit-control {
  font-family: var(--font-body); font-size: 11px; color: var(--ink-soft);
  background: var(--panel); border: 1px solid var(--line); padding: 4px 8px;
  border-radius: var(--radius-sm); cursor: pointer; font-weight: 500;
  font-variant-numeric: tabular-nums;
}

/* Sync indicator pill - shows in header so user can see when last pulled.
   Tap it to force a manual pull. */
.sync-pill {
  font-family: var(--font-body); font-size: 11px;
  padding: 4px 8px; border-radius: var(--radius-sm); cursor: pointer;
  font-weight: 600; letter-spacing: 0.02em; user-select: none;
  border: 1px solid transparent;
  transition: background 0.15s;
}
.sync-pill.off {
  color: var(--ink-faint); background: transparent;
  border-color: var(--line); cursor: default;
}
.sync-pill.pending {
  color: #92400e; background: #fef3c7; border-color: #fde68a;
}
.sync-pill.ok {
  color: var(--emerald-deep); background: var(--emerald-bg);
  border-color: var(--emerald-bg);
}
.sync-pill.ok::before {
  content: '●'; margin-right: 4px; color: var(--emerald);
  font-size: 9px; vertical-align: middle;
}
.sync-pill.stale {
  color: #92400e; background: #fef3c7; border-color: #fde68a;
}
.sync-pill.ok:hover, .sync-pill.stale:hover, .sync-pill.pending:hover {
  filter: brightness(0.96);
}

/* Tabs */
.tabs {
  display: flex; gap: 2px; margin-bottom: 18px;
  border-bottom: 1px solid var(--line);
}
.tab {
  font-family: var(--font-body); font-weight: 500; font-size: 12px;
  letter-spacing: 0.04em; text-transform: uppercase;
  padding: 10px 18px; cursor: pointer; color: var(--ink-mute);
  border-bottom: 2px solid transparent; margin-bottom: -1px;
  transition: color 0.15s, border-color 0.15s;
}
.tab:hover { color: var(--ink-soft); }
.tab.active { color: var(--ink); border-bottom-color: var(--emerald); font-weight: 600; }
@media (max-width: 720px) {
  /* Allow tabs to scroll horizontally on phones - 6 tabs at 18px padding overflow
     small viewports */
  .tabs {
    overflow-x: auto;
    -webkit-overflow-scrolling: touch;
    scrollbar-width: none;
    margin-bottom: 12px;
    /* Keep nav visible when scrolling. Without this, users scroll 5 picks
       deep on Today and lose access to switch tabs without scrolling back up.
       Background must be solid so picks don't bleed through.
       Stacks BELOW the sticky NTJ ticker (top: 46px ~= ticker height) so
       both ticker and tabs stay visible together. */
    position: sticky;
    top: 46px;
    background: var(--bg);
    z-index: 50;
    /* Add bottom padding so the underline border doesn't touch picks below */
    padding-bottom: 1px;
  }
  .tabs::-webkit-scrollbar { display: none; }
  .tab {
    padding: 10px 12px; font-size: 11px; flex-shrink: 0;
  }
}

/* Sub-tabs - per-section model selector. Shows "Main | Loose" pill row
   directly under the hero on Today and P&L tabs. Visually distinct from
   the main tabs (smaller, pill-styled with rounded background highlight)
   so users see the hierarchy: which tab they're on, then which model
   within that tab. */
.subtabs-row {
  display: flex; gap: 4px; margin: 0 0 14px 0;
  background: var(--line-soft);
  border-radius: var(--radius-md);
  padding: 3px;
  width: fit-content;
}
.subtab {
  font-family: var(--font-body); font-weight: 600; font-size: 11px;
  letter-spacing: 0.04em; text-transform: uppercase;
  padding: 6px 14px; cursor: pointer; color: var(--ink-mute);
  border-radius: calc(var(--radius-md) - 3px);
  transition: background 0.15s, color 0.15s;
  border: 0; background: transparent;
}
.subtab:hover { color: var(--ink-soft); }
.subtab.active {
  color: var(--ink);
  background: var(--panel);
  box-shadow: 0 1px 2px rgba(15, 23, 42, 0.06);
}
.subtab .subtab-badge {
  display: inline-block; margin-left: 5px;
  font-size: 9px; font-weight: 700;
  padding: 1px 5px; border-radius: 8px;
  background: var(--ink-faint); color: white;
  vertical-align: 1px;
}
.subtab.active .subtab-badge { background: var(--emerald); }
@media (max-width: 720px) {
  .subtabs-row { margin-bottom: 10px; }
  .subtab { padding: 5px 11px; font-size: 10px; }
}

/* Sections */
.section { display: none; padding-bottom: 60px; }
.section.active { display: block; }

/* Hero strip - model header */
.hero {
  background: var(--panel);
  border: 1px solid var(--line);
  border-radius: var(--radius-lg);
  padding: 18px 22px;
  margin-bottom: 18px;
  box-shadow: var(--shadow-1);
}
.hero-head {
  display: flex; align-items: baseline; justify-content: space-between;
  margin-bottom: 14px; flex-wrap: wrap; gap: 10px;
}
.hero-title {
  font-family: var(--font-body); font-weight: 600; font-size: 16px;
  letter-spacing: -0.005em;
}
.hero-title .label { color: var(--emerald); font-weight: 700; }
.hero-desc {
  font-family: var(--font-mono); font-size: 11px; color: var(--ink-mute);
}
.hero-stats {
  display: grid; grid-template-columns: repeat(auto-fit, minmax(140px, 1fr));
  gap: 18px;
}
@media (max-width: 720px) {
  .hero { padding: 12px 14px; margin-bottom: 10px; }
  .hero-stats {
    /* 4-column on phones for at-a-glance scanning. The 2x2 grid was
       too tall - eats prime screen real estate before users see picks.
       4 narrow cells keep all key metrics in one horizontal strip. */
    grid-template-columns: repeat(4, 1fr);
    gap: 4px;
  }
  .hero-stat { padding: 0; }
  .hero-stat .lbl { font-size: 8px; margin-bottom: 2px; letter-spacing: 0.04em; }
  .hero-stat .val { font-size: 15px; line-height: 1; }
  .hero-stat .sub { font-size: 9px; margin-top: 2px; }
}
.hero-stat { padding: 4px 0; }
.hero-stat .lbl {
  font-family: var(--font-body); font-size: 10px; font-weight: 600;
  text-transform: uppercase; letter-spacing: 0.06em; color: var(--ink-mute);
  margin-bottom: 4px;
}
.hero-stat .val {
  font-family: var(--font-body); font-weight: 900; font-size: 24px;
  letter-spacing: -0.02em; color: var(--ink); line-height: 1.1;
}
.hero-stat .sub {
  font-family: var(--font-body); font-size: 11px; font-weight: 500;
  color: var(--ink-mute); margin-top: 4px;
}
.val.pos { color: var(--emerald); }
.val.neg { color: var(--rose); }

/* ── Today tab: compact pick rows ──────────────────────────────────────── */
/* Shared horizontal-scroll container so picks-header and picks-list scroll
   together when the row exceeds viewport width. The inner header + list have
   matching min-width so they align column-for-column even while scrolled. */
.picks-scroll {
  overflow-x: auto;
  overflow-y: hidden;
  border-radius: var(--radius-md);
}

.picks-list {
  display: flex; flex-direction: column;
  background: var(--panel);
  border: 1px solid var(--line);
  border-top: none;
  border-radius: 0 0 var(--radius-md) var(--radius-md);
}
.pick-row {
  display: grid;
  grid-template-columns:
    52px              /* time */
    100px             /* venue + race # */
    minmax(180px, 1fr)  /* horse + meta */
    330px             /* signals strip - 3-col voting chips + Score/Votes stack */
    72px              /* odds (Fxd) */
    72px              /* stake */
    72px              /* return */
    96px              /* result */
    110px             /* bet toggle + odds-taken */
    24px;             /* expand chevron */
  gap: 8px;
  padding: 10px 14px;
  align-items: center;
  border-bottom: 1px solid var(--line-soft);
  cursor: pointer;
  transition: background 0.12s;
  position: relative;
  min-height: 48px;
  /* Min width ensures all columns fit; horizontal scroll on .picks-scroll
     kicks in below this on narrow viewports */
  min-width: 1188px;
}
.pick-row.bet-placed {
  box-shadow: inset 4px 0 0 var(--emerald);
}
.pick-row:last-child { border-bottom: none; }
.pick-row:hover { background: #fafbfc; }
.pick-row.below-threshold { opacity: 0.55; }
.pick-row.below-threshold:hover { opacity: 0.85; }
.pick-row.qualifies { border-left: 3px solid var(--emerald); padding-left: 11px; }
.pick-row.settled-win {
  border-left: 3px solid var(--emerald); padding-left: 11px;
  background: linear-gradient(to right, rgba(16,185,129,0.04), transparent 40%);
}
.pick-row.settled-loss {
  border-left: 3px solid var(--rose); padding-left: 11px;
  opacity: 0.75;
}
.pick-row.expanded {
  background: #fafbfc;
}

.pr-time {
  font-family: var(--font-body); font-weight: 700; font-size: 14px;
  color: var(--ink); white-space: nowrap;
}
.pr-time .ds-main {
  font-weight: 700; font-size: 13px; color: var(--ink);
  letter-spacing: -0.01em;
}
.pr-time .ttj {
  display: block; font-size: 9px; font-weight: 500;
  color: var(--ink-mute); letter-spacing: 0.04em;
  text-transform: uppercase; margin-top: 1px;
}
.pr-time .ttj.imm { color: var(--rose); font-weight: 700; }
.pr-time .ttj.soon { color: var(--amber); font-weight: 600; }

.pr-venue {
  display: flex; flex-direction: column; line-height: 1.25;
  white-space: nowrap; overflow: hidden;
}
.pr-venue .v-name {
  font-family: var(--font-body); font-weight: 700; font-size: 13px;
  color: var(--ink); letter-spacing: -0.005em;
  text-overflow: ellipsis; overflow: hidden;
}
.pr-venue .v-race {
  font-family: var(--font-body); font-weight: 600; font-size: 11px;
  color: var(--ink-mute); margin-top: 1px;
  letter-spacing: 0.04em;
}
/* Clickable venue block - jumps to race detail on click. Subtle hover hint
   so user knows it's interactive without screaming "I'M A LINK". */
.pr-venue.clickable {
  cursor: pointer; padding: 4px 6px; margin: -4px -6px;
  border-radius: 4px; transition: background 0.12s;
}
.pr-venue.clickable:hover {
  background: var(--emerald-bg);
}
.pr-venue.clickable:hover .v-name { color: var(--emerald-deep); }
.pr-venue.clickable:hover .v-race { color: var(--emerald-deep); opacity: 0.9; }

.pr-runner {
  display: flex; align-items: center; gap: 10px; min-width: 0;
}
.pr-runner .tab-bdg {
  display: inline-block; min-width: 24px; height: 24px; line-height: 24px;
  text-align: center; background: var(--ink); color: var(--panel);
  font-family: var(--font-body); font-size: 12px; font-weight: 700;
  border-radius: 4px; padding: 0 6px; flex-shrink: 0;
}
.pr-runner .rdetails {
  display: flex; flex-direction: column; line-height: 1.25; min-width: 0;
}
.pr-runner .rhorse {
  font-family: var(--font-body); font-weight: 600; font-size: 14px;
  color: var(--ink); letter-spacing: -0.005em;
  /* nowrap stays so horse names don't break mid-word; the fs-chip is
     a small inline-block that fits at the end of the line. If the
     name is so long it gets ellipsised the chip moves to the next
     line via the parent rdetails layout. */
  white-space: nowrap; overflow: visible;
}
/* Field size chip - sits inline after horse name. Neutral grey when field
   is 8+; red-bordered when 7 or fewer to flag the user's manual-skip
   strategy (small fields tend to push picks into longshot territory due
   to the SP>=3 filter excluding short favs). */
.fs-chip {
  display: inline-block; vertical-align: baseline;
  margin-left: 6px;
  font-family: var(--font-body); font-size: 10px; font-weight: 700;
  padding: 1px 6px; border-radius: 3px;
  background: var(--line-soft); color: var(--ink-mute);
  letter-spacing: 0.02em;
  cursor: help;
}
.fs-chip.warn {
  background: var(--rose-bg); color: var(--rose);
  border: 1px solid var(--rose-line);
}
/* Jockey rating chip - combined absolute + delta rule per backtest analysis.
   Four states reflect the bucket performance:
     base (no class) = neutral grey: "fine but not premium" (e.g. 80-84 rating)
     .good = emerald green: rating 85+ AND delta >= -4 (the +43.5% ROI bucket)
     .warn = amber: rating 75-79 (the underperforming bucket)
     .bad = rose red: rating < 75 OR delta < -10 (clearly weak)
   The label format is "Jky 87 -3" - absolute rating then delta from #1.
   Tooltips on hover give the full context. */
.jky-chip {
  display: inline-block; vertical-align: baseline;
  margin-left: 4px;
  font-family: var(--font-body); font-size: 10px; font-weight: 700;
  padding: 1px 6px; border-radius: 3px;
  background: var(--line-soft); color: var(--ink-mute);
  letter-spacing: 0.02em;
  cursor: help;
}
.jky-chip.good {
  background: var(--emerald-bg); color: var(--emerald-deep);
  border: 1px solid var(--emerald-line);
}
.jky-chip.warn {
  background: #fef3c7; color: #92400e;
  border: 1px solid #fde68a;
}
.jky-chip.bad {
  background: var(--rose-bg); color: var(--rose);
  border: 1px solid var(--rose-line);
}
.pr-runner .rmeta {
  font-family: var(--font-body); font-weight: 500; font-size: 11px;
  color: var(--ink-mute); margin-top: 1px;
  white-space: nowrap; overflow: hidden; text-overflow: ellipsis;
  max-width: 100%;
}

.pr-sigs {
  display: flex; flex-direction: column; align-items: flex-start; gap: 3px;
  padding-right: 12px;
}
.pr-sigs-top {
  display: flex; gap: 8px; align-items: center;
}
/* Desktop signal chip layout: 3-column grid for the 6 voting signals.
   Two compact rows (WPR/Late/Class top, L600/PFAI/TR bottom). To the
   right of this grid sits the score-votes-stack: Score chip above Votes
   badge in their own mini-column. This separates "why this was picked"
   (6 voting chips) from "how strong is the pick" (Score + Votes summary). */
.pr-sigs-top .desktop-chips {
  display: grid;
  grid-template-columns: repeat(3, minmax(0, 1fr));
  gap: 3px 5px;
  flex: 0 0 auto;
}
.pr-sigs-top .score-votes-stack {
  display: inline-flex;
  flex-direction: column;
  gap: 3px 5px;
  align-items: stretch;
  flex: 0 0 auto;
  /* Match the natural width of a voting chip in the 3-col grid above so the
     Score and Votes pills line up visually with the WPR/Late/Class/etc chips
     to their left. The widest voting chip content (e.g. "CLASS 1") renders
     at roughly this width with the standard 3px/5px padding. */
  width: 52px;
}
/* Stretch chips inside the stack so they have matching width, and centre
   their content. Padding clipped to 3px (vs the default 5px) so the
   stripped-label content fits cleanly inside the 52px stack. */
.pr-sigs-top .score-votes-stack .sig {
  justify-content: center;
  padding-left: 3px; padding-right: 3px;
  gap: 3px;
}
/* Hide both "Score" and "Votes" labels on the stacked chips - at 52px
   wide there isn't room for both label + value + suffix (confidence dot
   on Score, ★ count on Votes). The column position next to the voting
   chips already implies the meaning, and the suffixes self-label
   (• indicator for confidence, ★N for top-1 vote count). */
.pr-sigs-top .score-votes-stack .sig .lbl {
  display: none;
}
.pr-form {
  font-family: var(--font-body); font-size: 10px; color: var(--ink-mute);
  letter-spacing: 0.05em; font-weight: 600;
  font-variant-numeric: tabular-nums;
}
.pr-sigs .sig {
  display: inline-flex; align-items: baseline; gap: 2px;
  font-family: var(--font-body); font-size: 11px;
  background: var(--line-soft); border-radius: 3px;
  padding: 3px 5px; font-weight: 600; color: var(--ink-mute);
  white-space: nowrap;
}
.pr-sigs .sig.r1 { background: var(--emerald); color: #fff; }
.pr-sigs .sig.r2 { background: var(--emerald-bg); color: var(--emerald-deep); }
.pr-sigs .sig.r3 { background: #f0fdf4; color: var(--emerald-deep); }
.pr-sigs .sig .lbl {
  font-size: 9px; letter-spacing: 0.04em; text-transform: uppercase;
  font-weight: 600; opacity: 0.7;
}
.pr-sigs .sig .v {
  font-weight: 700; font-size: 12px;
}
/* Confidence dot - shows signal agreement on the Score pill.
   Filled = high agreement (signals unanimous), hollow = low (signals split). */
.pr-sigs .sig .conf-dot {
  display: inline-block; width: 6px; height: 6px; border-radius: 50%;
  margin-left: 4px; vertical-align: middle;
  border: 1px solid currentColor;
}
.pr-sigs .sig .conf-dot.high { background: currentColor; }
.pr-sigs .sig .conf-dot.mid {
  background: linear-gradient(to right, currentColor 50%, transparent 50%);
}
.pr-sigs .sig .conf-dot.low { background: transparent; opacity: 0.5; }

/* Vote count badge (V3 rule transparency).
   Shows "Votes 5/6 ★3" = 5 of 6 signals top-3, 3 of which are #1.
   Distinct from rank pills - never coloured by rank, always neutral. */
.pr-sigs .sig.vote-badge {
  background: #1f2937; color: #f9fafb;
  border: 1px solid #111827;
  padding: 2px 6px;
  display: inline-flex; align-items: center; gap: 4px;
}
.pr-sigs .sig.vote-badge .lbl {
  color: #9ca3af; font-size: 9px; letter-spacing: 0.05em;
  text-transform: uppercase;
}
.pr-sigs .sig.vote-badge .v {
  color: #f9fafb; font-weight: 700; font-variant-numeric: tabular-nums;
}
.pr-sigs .sig.vote-badge .vote-star {
  color: #fbbf24; font-size: 10px; font-weight: 700;
  margin-left: 2px;
}

.pr-odds {
  display: flex; align-items: center; gap: 4px; justify-content: flex-end;
}
/* Live fixed odds display (read-only) - no border/box, looks like static text.
   Now contains TWO lines: main Fxd price, and a small TF (Top Fluc) sub-line
   that's empty pre-race and populated when results sync. */
.pr-odds-display {
  display: inline-flex; flex-direction: column; align-items: flex-start; gap: 0;
  font-variant-numeric: tabular-nums;
  padding: 0; line-height: 1.1;
}
.pr-odds-display .pr-odds-main {
  display: inline-flex; align-items: baseline; gap: 1px;
}
.pr-odds-display .cur {
  font-family: var(--font-body); font-size: 11px; color: var(--ink-mute);
  font-weight: 500;
}
.pr-odds-display .v {
  font-family: var(--font-body); font-weight: 700; font-size: 14px;
  color: var(--ink-soft);
}
.pr-odds-display.qualifies .v { color: var(--emerald-deep); }
.pr-odds-display.below .v { color: var(--ink-soft); }
.pr-odds-display .v.empty {
  color: var(--ink-faint); font-weight: 500;
}
/* TF (Top Fluc) sub-line: shows highest bookie price during pre-race market.
   Populated post-race only; shows '—' before results sync to indicate
   "not available yet" rather than absence. Always reserves space so the
   row height doesn't jump when data arrives. */
.pr-odds-display .pr-odds-tf {
  display: inline-flex; align-items: baseline; gap: 3px;
  font-family: var(--font-body); font-size: 10px;
  margin-top: 1px; cursor: help;
}
.pr-odds-display .pr-odds-tf .tf-lbl {
  color: var(--ink-faint); font-weight: 600;
  font-size: 8px; text-transform: uppercase; letter-spacing: 0.04em;
}
.pr-odds-display .pr-odds-tf .tf-val {
  color: var(--ink-mute); font-weight: 600;
}
.pr-odds-display .pr-odds-tf .tf-val.empty {
  color: var(--ink-faint); font-weight: 500; opacity: 0.6;
}

/* Picks list column header */
.picks-header {
  display: grid;
  /* Column widths MUST match .pick-row exactly so the header labels line
     up with the data cells below them. Signals column is 330px: 3-col grid
     for the 6 voting signals (WPR/Late/Class on row 1, L600/PFAI/TR on row 2)
     plus the Score+Votes stack to the right. */
  grid-template-columns:
    52px 100px minmax(180px, 1fr) 330px 72px 72px 72px 96px 110px 24px;
  gap: 8px;
  padding: 8px 14px;
  align-items: center;
  background: var(--panel);
  border: 1px solid var(--line);
  border-bottom: none;
  border-radius: var(--radius-md) var(--radius-md) 0 0;
  /* Match picks-list min-width so columns align */
  min-width: 1188px;
}
.picks-header > div {
  font-family: var(--font-body); font-size: 10px; font-weight: 600;
  text-transform: uppercase; letter-spacing: 0.06em; color: var(--ink-mute);
}
.picks-header .th-right { text-align: right; }
.picks-list {
  border-top-left-radius: 0; border-top-right-radius: 0;
}

/* Section heads on the Today tab - "Pending" / "Resulted" separators
   between the two row groups. Each shows a count of rows in that section.
   Compact strip so it doesn't compete with the picks themselves.
   min-width matches .pick-row so the head stays aligned with the row
   columns when the user scrolls horizontally on narrow viewports. */
.picks-section-head {
  display: flex; align-items: center; gap: 8px;
  padding: 10px 14px 6px 14px;
  font-family: var(--font-body); font-size: 10px; font-weight: 700;
  letter-spacing: 0.08em; text-transform: uppercase;
  color: var(--ink-mute);
  min-width: 1188px;
  box-sizing: border-box;
}
.picks-section-head:first-child { padding-top: 4px; }
.picks-section-count {
  display: inline-block;
  font-family: var(--font-mono); font-size: 10px; font-weight: 700;
  padding: 1px 6px; border-radius: 8px;
  background: var(--line); color: var(--ink-soft);
  letter-spacing: 0;
}
/* Pending = active = highlight count slightly */
#pending-head .picks-section-count {
  background: var(--ink); color: var(--panel);
}

@media (max-width: 720px) {
  .picks-header { display: none; }
  .picks-list { border-top-left-radius: var(--radius-md); border-top-right-radius: var(--radius-md); }
  .picks-section-head { padding: 8px 12px 4px 12px; }
}

/* Inline cell labels - shown only on mobile so each value is self-explanatory.
   On desktop they're hidden because the picks-header row has the column titles. */
.cell-lbl {
  display: none;
  font-family: var(--font-body); font-size: 9px; font-weight: 600;
  text-transform: uppercase; letter-spacing: 0.06em; color: var(--ink-faint);
  margin-bottom: 2px;
}

.pr-stake, .pr-return {
  font-family: var(--font-body); text-align: right;
  font-variant-numeric: tabular-nums;
}
.pr-stake .units, .pr-return .units {
  font-weight: 700; font-size: 13px; color: var(--ink);
  display: block; line-height: 1.2;
}
.pr-stake .ret {
  font-weight: 500; font-size: 11px; color: var(--ink-mute);
  margin-top: 2px; display: block; line-height: 1.2;
}
.pr-return .ret {
  font-weight: 500; font-size: 11px; color: var(--emerald-deep);
  margin-top: 2px; display: block; line-height: 1.2;
}
.pr-stake.muted .units, .pr-return.muted .units { font-weight: 500; color: var(--ink-faint); }
.pr-stake.muted .ret, .pr-return.muted .ret { color: var(--ink-faint); }
.pr-stake .skip, .pr-return .skip {
  font-size: 11px; color: var(--ink-faint); font-weight: 500;
}

.pr-result {
  display: flex; gap: 4px; justify-content: flex-start; align-items: center;
}
.pr-result button {
  font-family: var(--font-body); font-size: 11px; font-weight: 600;
  background: var(--panel); color: var(--ink-mute);
  border: 1px solid var(--line); border-radius: 3px;
  padding: 4px 8px; cursor: pointer; transition: all 0.12s;
  min-width: 28px;
}
.pr-result button:hover {
  background: var(--emerald-bg); color: var(--emerald-deep);
  border-color: var(--emerald-line);
}
.pr-result button.lost-btn:hover {
  background: var(--rose-bg); color: var(--rose); border-color: var(--rose-line);
}
.pr-result .res-tag {
  display: inline-flex; align-items: center; gap: 6px;
  font-family: var(--font-body); font-size: 11px; font-weight: 600;
  padding: 4px 10px; border-radius: 4px;
}
.pr-result .res-tag.win { background: var(--emerald-bg); color: var(--emerald-deep); }
.pr-result .res-tag.loss { background: var(--rose-bg); color: var(--rose); }
/* Loss colour gradient by finish position. 2nd is the closest miss
   (orange, not rose) - distinguishes "narrowly lost" from "blown out".
   3rd-5th gets a softer orange-pink. 6+ stays full rose for clear losses. */
.pr-result .res-tag.loss.fin2 { background: #fff4ed; color: #b45309; }
.pr-result .res-tag.loss.fin345 { background: #fff1f2; color: #c2410c; }
.pr-result .res-tag.loss.fin6plus { background: var(--rose-bg); color: var(--rose); }
.pr-result .res-tag.manual {
  border: 1px dashed currentColor;
}
.pr-result .res-clear {
  cursor: pointer; color: var(--ink-faint); font-size: 13px;
  padding: 0 3px; line-height: 1;
}
.pr-result .res-clear:hover { color: var(--rose); }

/* Compact result dropdown for pending picks - replaces the four 1st/2nd/3rd/L
   buttons with a single ~80px-wide select. Native styling on most browsers
   shows a small caret indicator so user knows it's interactive. */
.res-select {
  font-family: var(--font-body); font-size: 11px; font-weight: 600;
  background: var(--panel); color: var(--ink-mute);
  border: 1px solid var(--line); border-radius: 3px;
  padding: 3px 4px 3px 8px; cursor: pointer; transition: all 0.12s;
  /* Keep narrow on desktop - "— set —" placeholder fits in ~78px */
  max-width: 92px;
  /* Enough touch target for mobile */
  min-height: 26px;
  /* Hide default OS chrome where possible while staying functional */
  -webkit-appearance: menulist-button; appearance: menulist-button;
}
.res-select:hover {
  background: var(--emerald-bg); color: var(--emerald-deep);
  border-color: var(--emerald-line);
}
.res-select:focus {
  outline: 2px solid var(--emerald); outline-offset: -1px;
}

/* ── Bet placed toggle + odds-taken ───────────────────────────────────── */
.pr-bet {
  display: flex; gap: 4px; align-items: center; justify-content: flex-end;
}
.bet-btn {
  font-family: var(--font-body); font-size: 13px; font-weight: 700;
  background: var(--panel); color: var(--ink-mute);
  border: 1px solid var(--line); border-radius: 4px;
  width: 28px; height: 28px; line-height: 1; cursor: pointer;
  transition: all 0.12s; flex-shrink: 0;
  display: inline-flex; align-items: center; justify-content: center;
}
.bet-btn:hover { background: var(--emerald-bg); color: var(--emerald-deep); border-color: var(--emerald-line); }
.bet-btn.placed {
  background: var(--emerald); color: #fff; border-color: var(--emerald);
}
.bet-btn.placed:hover { background: var(--emerald-deep); }
/* Odds-taken input - matches Fxd column visual format with $ prefix */
.odds-input-wrap {
  display: inline-flex; align-items: baseline; gap: 1px;
  border: 1px solid var(--line); border-radius: 4px;
  padding: 3px 8px;
  background: var(--panel);
  transition: all 0.12s;
}
.odds-input-wrap:focus-within {
  border-color: var(--emerald);
  box-shadow: 0 0 0 2px var(--emerald-bg);
}
.odds-input-wrap .cur {
  font-family: var(--font-body); font-size: 11px; color: var(--ink-mute);
  font-weight: 500;
}
.odds-input {
  font-family: var(--font-body); font-size: 14px; font-weight: 700;
  width: 44px; padding: 0;
  border: none; outline: none;
  color: var(--ink); background: transparent;
  font-variant-numeric: tabular-nums;
  text-align: right;
  -moz-appearance: textfield;
}
.odds-input::-webkit-outer-spin-button,
.odds-input::-webkit-inner-spin-button {
  -webkit-appearance: none; margin: 0;
}
.odds-input::placeholder { color: var(--ink-faint); font-weight: 400; }
.odds-warning {
  display: inline-flex; align-items: center; justify-content: center;
  width: 16px; height: 16px;
  color: #f59e0b; font-size: 13px; font-weight: 700; cursor: help;
  margin-left: 2px;
}

/* vs-SP timing edge indicator on placed bets in P&L tab. Shows how much
   better/worse your taken odds were vs SP. Tiny pill next to odds input. */
.vs-sp {
  display: inline-flex; align-items: center;
  font-family: var(--font-body); font-size: 10px; font-weight: 700;
  font-variant-numeric: tabular-nums;
  padding: 1px 4px; margin-left: 4px; border-radius: 3px;
  cursor: help;
}
.vs-sp.pos { background: var(--emerald-bg); color: var(--emerald-deep); }
.vs-sp.neg { background: var(--rose-bg); color: var(--rose); }
.vs-sp.neutral { background: var(--line-soft); color: var(--ink-mute); }

.pr-chev {
  color: var(--ink-faint); font-size: 12px; transition: transform 0.15s;
  text-align: center;
}
.pick-row.expanded .pr-chev { transform: rotate(180deg); color: var(--ink); }

/* ── Expanded detail panel ─────────────────────────────────────────────── */
.pick-detail {
  display: none; padding: 14px 18px 18px;
  background: #f8fafc; border-bottom: 1px solid var(--line-soft);
}
.pick-detail.show { display: block; }

.pd-section {
  margin-bottom: 14px;
}
.pd-section:last-child { margin-bottom: 0; }
.pd-section-title {
  font-family: var(--font-body); font-size: 10px; font-weight: 700;
  text-transform: uppercase; letter-spacing: 0.08em;
  color: var(--ink-mute); margin-bottom: 8px;
}

/* Bet adjustments toggle (e.g. dead heat) */
.pd-toggle {
  display: inline-flex; align-items: center; gap: 8px;
  cursor: pointer; user-select: none;
  padding: 6px 10px; background: var(--panel);
  border: 1px solid var(--line); border-radius: 5px;
}
.pd-toggle:hover { border-color: var(--line); background: #fafbfc; }
.pd-toggle input[type="checkbox"] {
  margin: 0; cursor: pointer; accent-color: var(--emerald);
}
.pd-toggle-lbl {
  font-family: var(--font-body); font-size: 12px; font-weight: 600;
  color: var(--ink-soft);
}
.pd-toggle-help {
  font-family: var(--font-body); font-size: 11px; font-weight: 400;
  color: var(--ink-mute);
}

/* Speed scores in expanded view - 4 compact inline cells */
.pd-speed {
  display: grid; grid-template-columns: repeat(4, 1fr); gap: 6px;
}
.pd-speed-cell {
  background: var(--panel); border: 1px solid var(--line);
  border-radius: 5px; padding: 5px 9px;
  display: flex; align-items: baseline; justify-content: space-between; gap: 6px;
}
.pd-speed-cell .sp-lbl {
  font-family: var(--font-body); font-size: 9px; font-weight: 600;
  text-transform: uppercase; letter-spacing: 0.05em; color: var(--ink-mute);
}
.pd-speed-cell .sp-val {
  font-family: var(--font-body); font-weight: 700; font-size: 13px;
  color: var(--ink); letter-spacing: -0.01em;
  font-variant-numeric: tabular-nums;
}
.pd-speed-cell .sp-rk {
  font-family: var(--font-body); font-size: 9px; font-weight: 600;
  color: var(--ink-mute);
}
.pd-speed-cell.r1 {
  background: var(--emerald-bg); border-color: var(--emerald-line);
}
.pd-speed-cell.r1 .sp-val, .pd-speed-cell.r1 .sp-rk { color: var(--emerald-deep); }
.pd-speed-cell.r2 .sp-val { color: var(--emerald-deep); }

/* Context grid in expanded view - clean rows of label/value pairs */
.pd-context {
  display: grid;
  grid-template-columns: repeat(auto-fit, minmax(140px, 1fr));
  gap: 12px 24px;
}
.pd-field {
  font-family: var(--font-body);
}
.pd-field .fl {
  display: block; font-size: 10px; font-weight: 600;
  text-transform: uppercase; letter-spacing: 0.06em;
  color: var(--ink-mute); margin-bottom: 3px;
}
.pd-field .fv {
  font-size: 13px; font-weight: 600; color: var(--ink);
  font-variant-numeric: tabular-nums;
}
/* Muted variant for values that aren't yet available (e.g. post-race
   prices before the results sync). Shown in greyed italic so user
   sees the placeholder rather than wondering if data is missing. */
.pd-field .fv.muted {
  color: var(--ink-faint); font-weight: 500; font-style: italic;
}

/* Score breakdown - per-signal percentile bars */
.pd-conf-summary {
  font-family: var(--font-body); font-size: 12px;
  color: var(--ink-mute); margin-bottom: 12px;
  padding: 6px 10px; background: var(--line-soft); border-radius: 4px;
}
.pd-conf-summary.pos { background: var(--emerald-bg); color: var(--emerald-deep); }
.pd-conf-summary.warn { background: #fef3c7; color: #92400e; }
.pd-conf-summary strong { color: inherit; }
.pd-sig-bars {
  display: flex; flex-direction: column; gap: 6px;
}
.pd-sig-row {
  display: grid; grid-template-columns: 130px 1fr 36px;
  gap: 10px; align-items: center;
  font-family: var(--font-body); font-size: 12px;
}
.pd-sig-lbl { color: var(--ink-soft); font-weight: 600; }
.pd-sig-bar {
  height: 12px; background: var(--line-soft);
  border-radius: 3px; overflow: hidden;
}
.pd-sig-fill {
  height: 100%; background: var(--ink-faint); border-radius: 3px;
  transition: width 0.3s;
}
.pd-sig-fill.r1 { background: var(--emerald); }
.pd-sig-fill.r2 { background: var(--emerald-deep); opacity: 0.65; }
.pd-sig-fill.r3 { background: var(--emerald-deep); opacity: 0.4; }
.pd-sig-pct {
  font-weight: 700; color: var(--ink); text-align: right;
  font-variant-numeric: tabular-nums; font-size: 12px;
}

.empty-state {
  background: var(--panel); border: 1px dashed var(--line);
  border-radius: var(--radius-md); padding: 50px 20px;
  text-align: center;
}
.empty-state .head {
  font-family: var(--font-body); font-weight: 700; font-size: 16px;
  color: var(--ink-soft); margin-bottom: 6px;
}
.empty-state .sub {
  font-family: var(--font-body); font-size: 12px; color: var(--ink-mute);
}

/* Mobile: streamlined card layout. Each pick is ~4 visual rows max.
   Time/venue header, horse, signal pills, then a single bottom strip with
   Fxd price, result tag, and bet toggle. Stake and Return values move into
   the expand panel since they're not needed at-a-glance scanning. */
@media (max-width: 720px) {
  .pick-row {
    grid-template-columns: auto 1fr auto;
    grid-template-areas:
      'time   venue   chev'
      'runner runner  runner'
      'sigs   sigs    sigs'
      'odds   result  bet';
    gap: 4px 8px;
    padding: 8px 12px;
    min-width: 0;
    align-items: center;
  }
  /* Disable horizontal scroll on mobile - row fits naturally */
  .picks-scroll { overflow-x: hidden; }
  .picks-list { min-width: 0; border-top: 1px solid var(--line); }
  .picks-section-head { min-width: 0; }

  /* Hide stake on mobile - it's in the expand panel for placed bets.
     Hide cell labels too since the new layout doesn't use them. */
  .pick-row .pr-stake { display: none; }
  .cell-lbl { display: none; }

  /* (Previously had an enlarged vote-badge override here when the badge
     was the sole mobile indicator. Now that all 6 voting chips render
     inline on mobile alongside the score-votes-stack chips, the badge
     uses the same compact sizing as the other chips - see the
     score-votes-stack rules further down for the unified sizing.) */

  /* On Today (pending) rows, hide return too - shown in expand panel.
     On P&L (settled) rows, show return as the most useful at-a-glance number. */
  .pick-row:not(.is-settled) .pr-return { display: none; }
  /* Settled rows reposition return into the bottom strip in place of bet column */
  .pick-row.is-settled {
    grid-template-areas:
      'time   venue   chev'
      'runner runner  runner'
      'sigs   sigs    sigs'
      'odds   result  return';
  }
  .pick-row.is-settled .pr-return {
    grid-area: return;
    text-align: right; justify-content: flex-end;
    flex-direction: column; gap: 0;
  }
  .pick-row.is-settled .pr-return .units {
    font-size: 13px; font-weight: 700;
  }
  .pick-row.is-settled .pr-return .ret {
    font-size: 10px;
  }
  /* Settled row also has a bet toggle (the + or odds input) - drop it
     into a tucked away spot since the row is already showing the result */
  .pick-row.is-settled .pr-bet { display: none; }

  .pr-time {
    grid-area: time;
    font-size: 13px; font-weight: 700;
  }
  .pr-venue {
    grid-area: venue;
    flex-direction: row; gap: 6px; align-items: baseline;
  }
  .pr-venue .v-name { font-size: 13px; font-weight: 600; }
  .pr-venue .v-race { font-size: 11px; color: var(--ink-mute); margin-top: 0; }
  .pr-runner { grid-area: runner; }
  .pr-runner .rhorse { font-size: 14px; }
  .pr-runner .rmeta { font-size: 11px; line-height: 1.35; }
  .pr-sigs { grid-area: sigs; }
  /* Mobile: show all 6 voting signal chips inline alongside the Votes badge.
     Chips wrap to a second row if needed. Form string stays in detail to
     save vertical space, but signal ranks are useful at a glance and should
     stay in the row (user feedback - they're scanning for #1 votes across
     signals to gauge pick strength visually). */
  .pr-sigs-top { flex-wrap: wrap; gap: 4px 5px; justify-content: flex-start; }
  .pr-sigs-top .desktop-chips {
    display: inline-flex; flex-wrap: wrap; gap: 4px 5px;
  }
  .pr-form.desktop-only { display: none; }
  /* Slightly compress the signal pills on mobile so all 7 fit comfortably */
  .pr-sigs-top .desktop-chips .sig {
    padding: 2px 6px; font-size: 10px;
  }
  .pr-sigs-top .desktop-chips .sig .lbl { font-size: 9px; }
  .pr-sigs-top .desktop-chips .sig .v { font-size: 11px; font-weight: 700; }
  /* On mobile, dissolve the Score/Votes stack column so Score and Votes
     join the same wrap-flow as the voting chips. display: contents makes
     the wrapper invisible to the layout - the two chips become direct
     children of pr-sigs-top and flow alongside WPR/Late/Class/etc. This
     replaces the previous vertical-column layout which visually separated
     Score and Votes from the voting chips. */
  .pr-sigs-top .score-votes-stack {
    display: contents;
  }
  /* Match the voting chips' compressed sizing so Score and Votes sit
     visually consistent in the wrapped row. */
  .pr-sigs-top .score-votes-stack .sig {
    padding: 2px 6px; font-size: 10px;
  }
  .pr-sigs-top .score-votes-stack .sig .lbl {
    display: inline; font-size: 9px;
  }
  .pr-sigs-top .score-votes-stack .sig .v {
    font-size: 11px; font-weight: 700;
  }
  /* Vote badge keeps its enlarged presence override from earlier in this
     media query (line ~1294) for the star + ratio. Tighten it to match
     the other chip sizing now that it sits inline with them. */
  .pr-sigs-top .score-votes-stack .vote-badge {
    padding: 2px 7px;
  }

  /* Bottom strip: Fxd | result | bet (or return for settled), single row */
  .pr-odds {
    grid-area: odds; justify-content: flex-start;
  }
  .pr-odds-display .v { font-size: 14px; font-weight: 700; }
  .pr-result {
    grid-area: result; justify-content: center;
    flex-wrap: wrap; gap: 4px;
  }
  /* Bigger touch targets on mobile - the unset state res-select dropdown
     was 26px tall which is below Apple HIG (44pt) and Google guidance (48dp).
     Bump to 36px for thumb-friendly tapping without dominating the row. */
  .pr-result .res-select {
    font-size: 12px; padding: 6px 6px 6px 10px;
    min-height: 36px;
  }
  /* Result tag (W·1st, L·3rd) - tappable to clear, gets bigger touch zone */
  .pr-result .res-tag {
    padding: 6px 8px; font-size: 12px;
  }
  .pr-bet {
    grid-area: bet; justify-content: flex-end;
    gap: 4px; flex-wrap: nowrap;
  }
  /* Bet button: 28px desktop -> 36px mobile for proper touch target */
  .pr-bet .bet-btn {
    width: 36px; height: 36px; font-size: 16px;
  }
  /* Odds input: a bit bigger and more padding so tapping it is easy */
  .pr-bet .odds-input-wrap { padding: 6px 8px; min-height: 36px; }
  .pr-bet .odds-input { width: 55px; font-size: 13px; }
  .pr-chev {
    grid-area: chev;
    font-size: 16px; color: var(--ink-faint);
    min-width: 28px; min-height: 28px;
    display: flex; align-items: center; justify-content: center;
  }
  /* Detail panel adjustments */
  .pd-speed { grid-template-columns: repeat(2, 1fr); }
  .pd-context {
    grid-template-columns: 1fr 1fr;
    gap: 10px 14px;
  }
  .pd-field .fl { font-size: 9px; }
  .pd-field .fv { font-size: 12px; }
}

.empty-state {
  background: var(--panel); border: 1px dashed var(--line);
  border-radius: var(--radius-md); padding: 50px 20px;
  text-align: center;
}
.empty-state .head {
  font-family: var(--font-display); font-weight: 600; font-size: 16px;
  color: var(--ink-soft); margin-bottom: 6px;
}
.empty-state .sub {
  font-family: var(--font-mono); font-size: 11px; color: var(--ink-mute);
}

/* Next-to-jump banner */
.ntj-ticker {
  background: #0f1729; color: #fff;
  display: flex; align-items: center; gap: 14px;
  padding: 8px 12px; border-radius: var(--radius-md);
  margin-bottom: 14px; overflow: hidden;
  /* Stick to top of viewport so the next-to-jump countdowns stay visible
     as the user scrolls through the day's picks. Background is solid dark
     so picks scrolling underneath don't bleed through. z-index 60 keeps
     it above the mobile-sticky .tabs (z-index 50). */
  position: sticky; top: 0; z-index: 60;
}
.ntj-ticker.collapsed { padding: 6px 12px; }
.ntj-ticker.collapsed .ntj-pills { display: none; }
.ntj-toggle {
  background: transparent; border: 1px solid rgba(255,255,255,.2);
  color: rgba(255,255,255,.7); width: 24px; height: 24px;
  border-radius: 4px; cursor: pointer; font-size: 9px;
  display: flex; align-items: center; justify-content: center;
  flex-shrink: 0;
}
.ntj-toggle:hover { background: rgba(255,255,255,.08); color: #fff; }
.ntj-label {
  font-family: var(--font-body); font-size: 10px; letter-spacing: 0.06em;
  color: rgba(255,255,255,.6); text-transform: uppercase; font-weight: 600;
  flex-shrink: 0; white-space: nowrap;
}
.ntj-pills {
  display: flex; gap: 8px; overflow-x: auto; flex: 1;
  -webkit-overflow-scrolling: touch; scrollbar-width: thin;
}
.ntj-pills::-webkit-scrollbar { height: 4px; }
.ntj-pills::-webkit-scrollbar-thumb { background: rgba(255,255,255,.15); border-radius: 2px; }
.ntj-pill {
  display: flex; align-items: center; gap: 8px;
  padding: 6px 12px; background: rgba(255,255,255,.06);
  border: 1px solid rgba(255,255,255,.1); border-radius: 6px;
  cursor: pointer; flex-shrink: 0; transition: all .12s; font-size: 12px;
}
.ntj-pill:hover { background: rgba(255,255,255,.12); border-color: rgba(255,255,255,.25); }
.ntj-pill-name {
  color: #fff; font-weight: 500; white-space: nowrap;
  font-family: var(--font-body); font-size: 12px;
}
.ntj-pill.has-pick { border-color: var(--emerald); background: rgba(16,185,129,.12); }
.ntj-pill.has-pick .ntj-pill-name::before {
  content: '●'; color: var(--emerald); margin-right: 6px;
}
/* Loose-model pick indicator on NTJ ticker pill. Amber dot mirrors the
   green dot used for Main picks. When both Main AND Loose pick the same
   race, the Main green dot wins (the has-pick rule above runs second in
   the cascade and overrides this one). */
.ntj-pill.has-loose-pick:not(.has-pick) {
  border-color: #d97706;
  background: rgba(217, 119, 6, .12);
}
.ntj-pill.has-loose-pick:not(.has-pick) .ntj-pill-name::before {
  content: '●'; color: #d97706; margin-right: 6px;
}
.ntj-pill-cd {
  font-family: var(--font-mono); font-size: 10px; font-weight: 700;
  padding: 2px 7px; border-radius: 4px; letter-spacing: .02em; white-space: nowrap;
}
.ntj-pill-cd.cd-live     { background: #fbbf24; color: #0f1729; }
.ntj-pill-cd.cd-imminent { background: var(--rose); color: #fff; }
.ntj-pill-cd.cd-soon     { background: #f59e0b; color: #fff; }
.ntj-pill-cd.cd-later    { background: rgba(255,255,255,.15); color: rgba(255,255,255,.85); }
.ntj-empty {
  font-family: var(--font-mono); color: rgba(255,255,255,.4);
  font-size: 11px; font-style: italic;
}
@media (max-width: 720px) {
  .ntj-ticker { margin-bottom: 10px; padding: 6px 10px; gap: 10px; }
  .ntj-label { display: none; }
  .ntj-pill { padding: 5px 10px; font-size: 11px; }
}

/* Race page - date bar */
.race-date-bar {
  display: flex; align-items: center; justify-content: space-between;
  background: var(--panel); border: 1px solid var(--line);
  border-radius: var(--radius-md); padding: 8px 14px;
  margin-bottom: 14px; flex-wrap: wrap; gap: 12px;
}
.race-date-controls { display: flex; align-items: center; gap: 6px; }
.race-date-quick {
  font-family: var(--font-body); font-size: 12px; font-weight: 500;
  background: transparent; color: var(--ink-mute); border: 1px solid var(--line);
  border-radius: var(--radius-sm); padding: 6px 12px; cursor: pointer;
  transition: all 0.12s;
}
.race-date-quick:hover { background: var(--line-soft); color: var(--ink); }
.race-date-quick.active { background: var(--ink); color: var(--panel); border-color: var(--ink); }
.race-date-input {
  font-family: var(--font-mono); font-size: 12px;
  background: var(--panel); border: 1px solid var(--line);
  border-radius: var(--radius-sm); padding: 6px 10px; color: var(--ink);
  margin-left: 4px;
}
.race-date-info {
  font-family: var(--font-mono); font-size: 11px; color: var(--ink-mute);
}
@media (max-width: 720px) {
  .race-date-bar {
    /* Stack vertically: Yesterday/Today/Tomorrow + date input on row 1,
       picks count on row 2. Avoids the awkward "7 picks" orphan in the layout. */
    flex-direction: column; align-items: stretch; gap: 8px; padding: 10px 12px;
  }
  .race-date-controls {
    /* Distribute the 3 quick buttons + date input across the row */
    flex-wrap: wrap; gap: 6px;
  }
  .race-date-quick { padding: 6px 10px; flex: 0 1 auto; }
  .race-date-input { flex: 1 1 130px; margin-left: 0; }
  .race-date-info { text-align: right; font-size: 11px; }
}

/* Race tab filters bar - sits below date bar, above meetings grid.
   Compact dropdowns + checkbox + reset link. Filtered-out cells dim
   to ~30% opacity but stay clickable so user can still inspect why
   they were filtered. Filters persist in localStorage. */
.race-filters-bar {
  display: flex; align-items: center; gap: 12px;
  background: var(--panel); border: 1px solid var(--line);
  border-radius: var(--radius-md); padding: 8px 14px;
  margin-bottom: 14px; flex-wrap: wrap;
  font-family: var(--font-body); font-size: 12px;
}
.race-filter-group { display: flex; align-items: center; gap: 6px; }
.race-filter-group label {
  color: var(--ink-mute); font-weight: 500;
  letter-spacing: 0.03em; text-transform: uppercase; font-size: 10px;
}
.race-filter-select {
  font-family: var(--font-body); font-size: 12px;
  background: var(--panel); color: var(--ink);
  border: 1px solid var(--line); border-radius: var(--radius-sm);
  padding: 4px 8px; cursor: pointer;
}
.race-filter-select:hover { border-color: var(--ink-faint); }
.race-filter-check {
  display: flex; align-items: center; gap: 5px; cursor: pointer;
  font-size: 11px; color: var(--ink-soft);
}
.race-filter-check input { cursor: pointer; }
.race-filter-reset {
  background: none; border: 0; color: var(--ink-mute);
  font-size: 11px; cursor: pointer;
  text-decoration: underline; padding: 2px 4px;
}
.race-filter-reset:hover { color: var(--rose); }
.race-filter-summary {
  margin-left: auto;
  font-family: var(--font-mono); font-size: 11px; color: var(--ink-mute);
}
@media (max-width: 720px) {
  .race-filters-bar { padding: 8px 10px; gap: 8px; }
  .race-filter-group label { display: none; }
  .race-filter-summary { display: none; }
}

/* Race page - meetings grid table */
.meetings-table {
  background: var(--panel); border: 1px solid var(--line);
  border-radius: var(--radius-md); overflow: hidden;
}
.mt-row {
  display: grid;
  grid-template-columns: 200px repeat(auto-fill, minmax(60px, 1fr));
  border-bottom: 1px solid var(--line-soft); align-items: stretch;
}
.mt-row:last-child { border-bottom: none; }
.mt-row.mt-head {
  background: var(--line-soft); border-bottom: 1px solid var(--line);
}
.mt-row.mt-head .mt-venue-col,
.mt-row.mt-head .mt-race-head {
  padding: 10px 12px; font-family: var(--font-mono);
  font-size: 9px; letter-spacing: 0.08em; color: var(--ink-mute);
  font-weight: 600; text-transform: uppercase;
}
.mt-row.mt-head .mt-race-head {
  text-align: center; border-left: 1px solid var(--line-soft);
}
.mt-venue-col {
  padding: 14px 16px; border-right: 1px solid var(--line-soft);
  display: flex; flex-direction: column; justify-content: center;
}
.mt-venue-name {
  font-family: var(--font-body); font-weight: 600; font-size: 14px;
  color: var(--ink); letter-spacing: -0.005em;
}
.mt-venue-state {
  font-family: var(--font-mono); font-size: 10px; color: var(--ink-mute);
  margin-top: 2px; letter-spacing: 0.04em;
}
.mt-race-cell {
  padding: 12px 6px; border-left: 1px solid var(--line-soft);
  display: flex; flex-direction: column; align-items: center; justify-content: center;
  cursor: pointer; font-size: 11px; color: var(--ink-soft); background: var(--panel);
  transition: background 0.12s, color 0.12s; position: relative; min-height: 48px;
}
.mt-race-cell:hover { background: var(--line-soft); color: var(--ink); }
.mt-race-cell .mt-time {
  font-family: var(--font-mono); font-size: 11px; font-weight: 500;
}
.mt-race-cell.mt-empty { color: var(--ink-faint); cursor: default; background: var(--bg); }
.mt-race-cell.mt-empty:hover { background: var(--bg); color: var(--ink-faint); }
.mt-race-cell.mt-resulted { color: var(--ink-mute); background: var(--bg); }

/* Abandoned styling. Whole row fades and strikes through when meeting is
   marked abandoned. Race-level abandon strikes that single cell. Hover
   still works so the user can unmark. The abandon button itself stays
   visible (no strike-through) so the unmark target is always reachable. */
.mt-row.is-abandoned .mt-venue-name,
.mt-row.is-abandoned .mt-venue-state,
.mt-row.is-abandoned .mt-race-cell {
  text-decoration: line-through;
  opacity: 0.45;
}
.mt-row.is-abandoned .mt-race-cell:hover { opacity: 0.65; }
.mt-race-cell.is-abandoned {
  text-decoration: line-through; opacity: 0.45;
}
.mt-race-cell.is-abandoned:hover { opacity: 0.65; }
.mt-abandon-btn {
  margin-top: 4px;
  font-family: var(--font-body); font-size: 9px; font-weight: 600;
  letter-spacing: 0.04em; text-transform: uppercase;
  background: transparent; color: var(--ink-mute);
  border: 1px solid var(--line); border-radius: 3px;
  padding: 2px 6px; cursor: pointer;
  align-self: flex-start;
}
.mt-abandon-btn:hover { color: var(--rose); border-color: var(--rose); }
.mt-row.is-abandoned .mt-abandon-btn {
  background: var(--rose); color: #fff; border-color: var(--rose);
  text-decoration: none; opacity: 1;
}
.mt-row.is-abandoned .mt-abandon-btn:hover { background: #b91c1c; }

/* Resulted-race outcome highlighting. mt-result-main-hit: emerald tint when
   the Main model pick won. mt-result-loose-hit: amber tint when only the
   Loose pick won (Main missed). Lets the user scan a day's card and
   immediately see model accuracy without clicking into each race. */
.mt-race-cell.mt-resulted.mt-result-main-hit {
  background: #d1fae5;
  color: var(--emerald-deep);
  font-weight: 600;
}
.mt-race-cell.mt-resulted.mt-result-main-hit:hover { background: #a7f3d0; }
.mt-race-cell.mt-resulted.mt-result-loose-hit {
  background: #fef3c7;
  color: #92400e;
  font-weight: 600;
}
.mt-race-cell.mt-resulted.mt-result-loose-hit:hover { background: #fde68a; }
.mt-race-cell.mt-imminent {
  background: var(--emerald); color: #fff; font-weight: 600;
}
.mt-race-cell.mt-imminent:hover { background: var(--emerald-deep); color: #fff; }
.mt-race-cell.mt-imminent .mt-time { color: #fff; }
.mt-race-cell.mt-soon { background: #fef3c7; color: #92400e; }
.mt-race-cell.mt-soon:hover { background: #fde68a; }
.mt-race-cell.mt-pending-late { background: #fee2e2; color: #991b1b; }
.mt-race-cell.has-pick::before {
  content: ''; position: absolute; top: 4px; right: 4px;
  width: 5px; height: 5px; border-radius: 50%;
  background: var(--emerald);
}
.mt-race-cell.mt-imminent.has-pick::before { background: #fff; }

/* Loose-model pick indicator. Amber dot in same top-right position as the
   Main pick dot. When a cell has BOTH classes the green dot wins (the
   has-pick::before above runs second in the cascade). Loose-ONLY cells
   also get a subtle amber background tint so they're scannable at a
   glance without needing to read the dot. */
.mt-race-cell.has-loose-pick:not(.has-pick)::before {
  content: ''; position: absolute; top: 4px; right: 4px;
  width: 5px; height: 5px; border-radius: 50%;
  background: #d97706;
}
.mt-race-cell.has-loose-pick:not(.has-pick) {
  background: rgba(217, 119, 6, 0.06);
}
.mt-race-cell.has-loose-pick:not(.has-pick):hover {
  background: rgba(217, 119, 6, 0.14);
}
/* When loose-only cell is imminent (live/very-soon), keep the imminent
   emerald look dominant but use white amber-dot for visibility */
.mt-race-cell.mt-imminent.has-loose-pick:not(.has-pick)::before { background: #fff; }

/* Field-size strategy indicator. Bottom-right corner, mirrors the top-right
   has-pick dot. Shown when fs >= 8 - the user's metro Saturday filter
   threshold (same gate the Quaddie tab uses). Lets you scan a day's card
   and immediately see which races clear the field-size bar without
   expanding each cell. Imminent cells (green bg) and pending-late (red bg)
   override the colour so the chip stays readable on those backgrounds. */
.mt-race-cell.mt-fsok::after {
  content: 'F+'; position: absolute; bottom: 3px; right: 4px;
  font-family: var(--font-mono); font-size: 8px; font-weight: 700;
  letter-spacing: 0.02em; line-height: 1;
  padding: 1px 3px; border-radius: 2px;
  background: var(--emerald-bg); color: var(--emerald-deep);
}
.mt-race-cell.mt-fsok.mt-imminent::after {
  background: rgba(255,255,255,0.22); color: #fff;
}
.mt-race-cell.mt-fsok.mt-soon::after {
  background: rgba(146,64,14,0.12); color: #92400e;
}
.mt-race-cell.mt-fsok.mt-pending-late::after {
  background: rgba(255,255,255,0.4); color: #991b1b;
}
.mt-race-cell.mt-fsok.mt-resulted::after,
.mt-race-cell.mt-fsok.mt-empty::after { display: none; }

.mt-cd, .mt-cd-soon {
  font-family: var(--font-mono); font-size: 9px; font-weight: 700;
  margin-top: 2px;
}
.mt-cd { color: #fff; }
.mt-cd-soon { color: #92400e; }

@media (max-width: 720px) {
  .meetings-table { overflow-x: auto; }
  .mt-row { grid-template-columns: 140px repeat(12, minmax(48px, 1fr)); min-width: 600px; }
}

/* Quaddie meetings table - same layout pattern as .meetings-table on the
   Race tab but with quaddie-specific cell content: qualifier count, strategy
   chip, leg position. Rows are clickable to select a meeting; cells are
   clickable to toggle leg membership. */
.quaddie-meetings-table {
  background: var(--panel); border: 1px solid var(--line);
  border-radius: var(--radius-md); overflow: hidden; margin-bottom: 14px;
}
.qmt-row {
  display: grid;
  grid-template-columns: 220px repeat(auto-fill, minmax(64px, 1fr));
  border-bottom: 1px solid var(--line-soft); align-items: stretch;
}
.qmt-row:last-child { border-bottom: none; }
.qmt-row.qmt-head {
  background: var(--line-soft); border-bottom: 1px solid var(--line);
}
.qmt-row.qmt-head .qmt-venue-col,
.qmt-row.qmt-head .qmt-race-head {
  padding: 10px 12px; font-family: var(--font-mono);
  font-size: 9px; letter-spacing: 0.08em; color: var(--ink-mute);
  font-weight: 600; text-transform: uppercase;
}
.qmt-row.qmt-head .qmt-race-head {
  text-align: center; border-left: 1px solid var(--line-soft);
}
.qmt-venue-row.active { background: var(--emerald-bg); }
.qmt-venue-row.no-strat-races .qmt-venue-name { color: var(--ink-mute); }
.qmt-venue-row.no-strat-races { opacity: 0.65; }
.qmt-venue-col {
  padding: 12px 16px; border-right: 1px solid var(--line-soft);
  display: flex; flex-direction: column; justify-content: center;
  cursor: pointer; transition: background 0.12s;
}
.qmt-venue-col:hover { background: var(--line-soft); }
.qmt-venue-row.active .qmt-venue-col:hover { background: var(--emerald-bg); }
.qmt-venue-name {
  font-family: var(--font-body); font-weight: 600; font-size: 14px;
  color: var(--ink); letter-spacing: -0.005em;
}
.qmt-venue-state {
  font-family: var(--font-mono); font-size: 10px; color: var(--ink-mute);
  margin-top: 2px; letter-spacing: 0.04em;
}
.qmt-strat-summary {
  margin-top: 4px; font-family: var(--font-body); font-size: 10px;
  font-weight: 700; letter-spacing: 0.02em;
}
.qmt-strat-summary.qmt-strat-good { color: var(--emerald-deep); }
.qmt-strat-summary.qmt-strat-some { color: var(--amber); }
.qmt-strat-summary.qmt-strat-none { color: var(--ink-faint); }
.qmt-race-cell {
  padding: 8px 4px; border-left: 1px solid var(--line-soft);
  display: flex; flex-direction: column; align-items: center; justify-content: center;
  cursor: pointer; font-size: 11px; background: var(--panel);
  transition: background 0.12s; position: relative; min-height: 52px;
}
.qmt-race-cell:hover { background: var(--line-soft); }
.qmt-race-cell.qmt-empty { color: var(--ink-faint); cursor: default; background: var(--bg); }
.qmt-race-cell.qmt-empty:hover { background: var(--bg); }
.qmt-race-cell.strat-pass { background: rgba(16, 185, 129, 0.05); }
.qmt-race-cell.strat-pass:hover { background: rgba(16, 185, 129, 0.12); }
.qmt-race-cell.strat-fail { opacity: 0.55; }
.qmt-race-cell.strat-fail:hover { opacity: 1; }
.qmt-race-cell.resulted { color: var(--ink-mute); }
.qmt-race-cell.resulted .qmt-quals { color: var(--ink-faint); }
.qmt-race-cell.selected {
  background: var(--emerald) !important; color: #fff;
  box-shadow: 0 0 0 1px var(--emerald) inset; opacity: 1;
}
.qmt-race-cell.selected .qmt-quals,
.qmt-race-cell.selected .qmt-strat-icon { color: #fff; }
.qmt-quals {
  font-family: var(--font-body); font-weight: 700; font-size: 14px;
  color: var(--emerald-deep);
}
.qmt-strat-icon {
  font-size: 10px; font-weight: 700; margin-top: 2px;
}
.qmt-race-cell.strat-pass .qmt-strat-icon { color: var(--emerald-deep); }
.qmt-race-cell.strat-fail .qmt-strat-icon { color: var(--rose); }
.qmt-leg-tag {
  position: absolute; top: 3px; right: 4px;
  font-size: 9px; font-weight: 800;
  background: #fff; color: var(--emerald-deep);
  padding: 1px 5px; border-radius: 8px;
  box-shadow: 0 1px 2px rgba(0,0,0,0.1);
}
/* Key/legend under the table - explains the cell contents to the user */
.qmt-key {
  display: flex; flex-wrap: wrap; gap: 14px;
  padding: 8px 14px; font-family: var(--font-body); font-size: 11px;
  color: var(--ink-mute); margin-bottom: 14px;
}
.qmt-key .qmt-key-tick { color: var(--emerald-deep); font-weight: 800; }
.qmt-key .qmt-key-num { font-weight: 700; color: var(--ink); }
.qmt-key .qmt-key-leg {
  display: inline-block; background: var(--emerald); color: #fff;
  padding: 1px 5px; border-radius: 8px; font-weight: 800; font-size: 9px;
}

@media (max-width: 720px) {
  .quaddie-meetings-table { overflow-x: auto; }
  .qmt-row { grid-template-columns: 130px repeat(12, minmax(48px, 1fr)); min-width: 600px; }
  .qmt-quals { font-size: 13px; }
  .qmt-venue-name { font-size: 12px; }
  .qmt-key { font-size: 10px; gap: 8px; }
}

/* Race detail back bar */
.race-back-bar {
  display: flex; align-items: center; gap: 8px;
  margin-bottom: 12px;
}
.race-back-btn {
  font-family: var(--font-body); font-size: 12px; font-weight: 500;
  background: transparent; color: var(--ink-mute); border: 1px solid var(--line);
  border-radius: var(--radius-sm); padding: 6px 14px; cursor: pointer;
  transition: all 0.12s;
}
.race-back-btn:hover { background: var(--line-soft); color: var(--ink); }

/* Meeting jump strip - all races at the current venue */
.meeting-strip {
  display: flex; gap: 6px; padding: 8px 10px;
  background: var(--panel); border: 1px solid var(--line);
  border-radius: var(--radius-lg); margin-bottom: 12px;
  overflow-x: auto; align-items: center;
}
.meeting-strip::-webkit-scrollbar { height: 4px; }
.meeting-strip::-webkit-scrollbar-thumb { background: var(--line); border-radius: 2px; }
.meeting-strip-label {
  font-family: var(--font-body); font-size: 10px; font-weight: 700;
  letter-spacing: 0.06em; text-transform: uppercase;
  color: var(--ink-mute); padding: 0 8px; flex-shrink: 0; white-space: nowrap;
}
.meeting-tile {
  display: flex; flex-direction: column; align-items: flex-start;
  padding: 6px 10px; gap: 1px;
  background: var(--line-soft); border: 1px solid var(--line);
  border-radius: 6px; cursor: pointer; flex-shrink: 0;
  transition: all .12s; width: 100px; box-sizing: border-box;
  overflow: hidden;
}
.meeting-tile:hover { background: #ede9e1; border-color: #d6d3d1; }
.meeting-tile.active {
  background: var(--ink); border-color: var(--ink);
}
.meeting-tile.active .mt-race { color: #fff; }
.meeting-tile.active .mt-time { color: rgba(255,255,255,.7); }
.meeting-tile.has-pick {
  border-left: 3px solid var(--emerald);
  padding-left: 8px;
}
/* Loose-only meeting tile - amber border-left mirroring Main's emerald
   treatment. When BOTH classes present, has-pick (emerald) wins because
   it appears later in the cascade. */
.meeting-tile.has-loose-pick:not(.has-pick) {
  border-left: 3px solid #d97706;
  padding-left: 8px;
  /* No opacity dimming - this IS a pick, just from the experimental model */
  opacity: 1;
}
.meeting-tile.no-pick { opacity: 0.55; }
.meeting-tile.done { opacity: 0.4; }
.mt-race {
  font-family: var(--font-body); font-size: 13px; font-weight: 700;
  color: var(--ink); letter-spacing: -0.01em; line-height: 1.1;
  display: flex; align-items: center; gap: 6px; white-space: nowrap;
}
.mt-cd {
  display: inline-block; font-family: var(--font-body); font-size: 9px;
  font-weight: 700; padding: 1px 5px; border-radius: 3px;
  background: var(--line); color: var(--ink-mute);
}
.mt-cd.cd-live { background: #fbbf24; color: #0f1729; }
.mt-cd.cd-imminent { background: var(--rose); color: #fff; }
.mt-cd.cd-soon { background: #f59e0b; color: #fff; }
.mt-time {
  font-family: var(--font-body); font-size: 10px; font-weight: 500;
  color: var(--ink-mute); font-variant-numeric: tabular-nums;
}
.mt-info {
  font-family: var(--font-body); font-size: 9px; font-weight: 500;
  color: var(--ink-faint); white-space: nowrap; overflow: hidden;
  text-overflow: ellipsis; width: 100%;
}
.meeting-tile.active .mt-info { color: rgba(255,255,255,.55); }

/* Race context bar (between header and runners) */
.race-context-bar {
  background: var(--panel); border-left: 1px solid var(--line);
  border-right: 1px solid var(--line); padding: 12px 20px;
  display: flex; gap: 18px; flex-wrap: wrap;
  font-family: var(--font-body); font-size: 12px; font-weight: 500;
}
.race-context-bar .ctx-item { color: var(--ink-mute); }
.race-context-bar .ctx-item .ctx-v {
  color: var(--ink); font-weight: 700; margin-left: 4px;
}
.race-context-bar .ctx-item.ctx-overridden .ctx-v {
  color: #92400e;
  border-bottom: 2px dashed #d97706;
}
.race-context-bar .ctx-item.ctx-overridden::after {
  content: ' (manual)'; color: #d97706; font-size: 10px; font-weight: 600;
  margin-left: 4px; text-transform: uppercase; letter-spacing: 0.05em;
}

.race-context-bar .ctx-item.ctx-override-inline {
  display: flex; align-items: center; gap: 6px;
  margin-left: auto;
}
.race-context-bar .ctx-override-inline .ctx-lbl {
  font-family: var(--font-body); font-size: 10px; font-weight: 600;
  text-transform: uppercase; letter-spacing: 0.06em; color: var(--ink-mute);
}
.race-context-bar .ctx-override-input {
  font-family: var(--font-body); font-size: 12px; font-weight: 600;
  padding: 4px 8px; border: 1px solid var(--line);
  border-radius: 4px; background: var(--panel); color: var(--ink);
  width: 100px;
}
.race-context-bar .ctx-override-input:focus {
  outline: 2px solid var(--emerald); outline-offset: -1px;
}
.race-context-bar .ctx-override-clear {
  border: none; background: transparent; color: var(--ink-mute);
  cursor: pointer; font-size: 16px; line-height: 1; padding: 0 4px;
  font-weight: 700;
}
.race-context-bar .ctx-override-clear:hover { color: var(--rose); }
@media (max-width: 720px) {
  /* Override input is fiddly to type on mobile and rarely needed there.
     Hide both label and input - desktop users can still set track condition
     overrides; mobile users use the system going as-is. */
  .race-context-bar .ctx-override-inline { display: none; }
}

/* PF data freshness indicator - shown above the runners table when this
   meeting's Punting Form ratings are stale or absent. Hidden when PF data
   is fresh (rated within 24h of race time). */
.pf-freshness-bar {
  display: none; /* shown via JS when relevant */
  padding: 8px 20px; font-family: var(--font-body); font-size: 12px;
  border-left: 1px solid var(--line); border-right: 1px solid var(--line);
  border-bottom: 1px solid var(--line);
  background: var(--line-soft); color: var(--ink-mute);
}
.pf-freshness-bar.warn  { background: #fef3c7; color: #92400e;
  border-bottom: 1px solid #fde68a; font-weight: 500; }
.pf-freshness-bar.error { background: #fee2e2; color: #991b1b;
  border-bottom: 1px solid #fecaca; font-weight: 600; }
.pf-freshness-bar .pf-label { font-weight: 700; margin-right: 6px; }

/* Pace estimate badge inside header */
.race-pace-est {
  display: inline-flex; align-items: center; gap: 6px;
  padding: 3px 10px; border-radius: 4px;
  font-family: var(--font-body); font-size: 11px; font-weight: 600;
  background: rgba(255,255,255,0.1); color: #fafaf9;
}
.race-pace-est .lbl {
  font-size: 9px; opacity: 0.7; text-transform: uppercase;
  letter-spacing: 0.06em;
}
.race-pace-est.hot { background: rgba(239,68,68,0.2); }
.race-pace-est.fast { background: rgba(245,158,11,0.2); }
.race-pace-est.slow { background: rgba(59,130,246,0.2); }

/* Race-detail abandon toggle. Sits alongside the other header stat items.
   Default: muted outline. Active (race abandoned): rose filled. If the
   whole meeting is marked, the toggle is replaced by a static "MEETING
   ABANDONED" tag that's read-only here (unmark on the meetings grid). */
.rd-abandon-btn {
  font-family: var(--font-body); font-size: 11px; font-weight: 600;
  background: transparent; color: var(--ink-mute);
  border: 1px solid var(--line); border-radius: var(--radius-sm);
  padding: 4px 10px; cursor: pointer;
  letter-spacing: 0.02em;
}
.rd-abandon-btn:hover { color: var(--rose); border-color: var(--rose); }
.rd-abandon-btn.is-on {
  background: var(--rose); color: #fff; border-color: var(--rose);
}
.rd-abandon-btn.is-on:hover { background: #b91c1c; }
.rd-abandon-item.is-meeting-abandoned {
  background: var(--rose); color: #fff;
  font-weight: 700; letter-spacing: 0.04em; font-size: 10px;
  padding: 4px 10px; border-radius: var(--radius-sm);
}

/* Pace map - settling positions */
.race-pace-map {
  background: var(--panel); border-left: 1px solid var(--line);
  border-right: 1px solid var(--line); border-bottom: 1px solid var(--line);
  padding: 14px 20px;
}

/* Race shape SVG - horizontal lane diagram. Sized to fill the container. */
.race-shape-wrap {
  position: relative;
  padding-top: 8px;
}
.race-pace-pill {
  position: absolute; top: 0; right: 0;
  display: inline-flex; align-items: center; gap: 8px;
  padding: 6px 14px; border-radius: 16px;
  font-family: var(--font-body); font-size: 12px;
  border: 1.5px solid; background: var(--panel);
  z-index: 2;
  box-shadow: 0 1px 2px rgba(0,0,0,0.04);
}
.race-pace-pill .rpp-lbl {
  font-size: 10px; font-weight: 600; opacity: 0.75;
  text-transform: uppercase; letter-spacing: 0.06em;
}
.race-pace-pill .rpp-val {
  font-weight: 700; letter-spacing: 0.02em;
}
.race-pace-pill.hot   { color: #991b1b; border-color: #ef4444; background: #fef2f2; }
.race-pace-pill.fast  { color: #92400e; border-color: #f59e0b; background: #fffbeb; }
.race-pace-pill.slow  { color: #1e3a8a; border-color: #3b82f6; background: #eff6ff; }
.race-pace-pill.even,
.race-pace-pill       { color: #334155; border-color: #64748b; }

.race-shape-svg {
  width: 100%; height: auto; display: block;
  max-height: 180px;
}
.race-shape-unknown {
  font-family: var(--font-body); font-size: 11px; color: var(--ink-faint);
  font-style: italic; margin-top: 6px; padding-left: 4px;
}

/* Pace pill row - HTML element above the speed map SVG */
.rsp-pill-row {
  display: flex; justify-content: flex-end;
  padding: 0 8px 8px 8px;
}
.rsp-pill {
  display: inline-flex; align-items: center; gap: 8px;
  padding: 5px 12px; border-radius: 999px;
  font-family: var(--font-body); font-size: 11px; font-weight: 700;
  letter-spacing: 0.04em;
  background: rgba(100,116,139,0.10);
  border: 1px solid #64748b;
  color: #334155;
}
.rsp-pill .rsp-pill-lbl {
  font-size: 9px; font-weight: 600; opacity: 0.75;
  text-transform: uppercase; letter-spacing: 0.08em;
}
.rsp-pill .rsp-pill-val { text-transform: uppercase; }
.rsp-pill-hot   { background: rgba(239,68,68,0.15);  border-color: #ef4444; color: #991b1b; }
.rsp-pill-fast  { background: rgba(245,158,11,0.15); border-color: #f59e0b; color: #92400e; }
.rsp-pill-slow  { background: rgba(59,130,246,0.15); border-color: #3b82f6; color: #1e3a8a; }
.rsp-pill-even  { background: rgba(16,185,129,0.12); border-color: #10b981; color: #065f46; }

/* Track conditions card - sits between context bar and race shape on detail page */
.track-conditions-card {
  background: var(--panel); border-bottom: 1px solid var(--line);
  padding: 16px 22px;
}
.tc-header {
  display: flex; gap: 24px; flex-wrap: wrap; margin-bottom: 14px;
  padding-bottom: 14px; border-bottom: 1px solid var(--line-soft);
}
.tc-header > div {
  display: flex; flex-direction: column; gap: 2px;
}
.tc-header .tc-key {
  font-family: var(--font-body); font-size: 10px; font-weight: 600;
  text-transform: uppercase; letter-spacing: 0.06em; color: var(--ink-mute);
}
.tc-header .tc-val {
  font-family: var(--font-body); font-size: 16px; font-weight: 700;
  color: var(--ink);
}
.tc-header .tc-going.overridden .tc-val { color: #92400e; }
.tc-header .tc-orig {
  font-family: var(--font-body); font-size: 10px; color: var(--ink-faint);
  font-style: italic;
}

/* Commentary block - shows winning-position bias for this venue/going combo */
.tc-commentary {
  font-family: var(--font-body); font-size: 13px; color: var(--ink-soft);
  line-height: 1.5; margin-bottom: 14px;
}
.tc-commentary.tc-insufficient {
  color: var(--ink-faint); font-style: italic;
  background: var(--line-soft); padding: 10px 12px;
  border-radius: 4px;
}
.tc-summary {
  font-size: 13px; color: var(--ink-soft); margin-bottom: 12px;
}
.tc-summary strong { color: var(--ink); font-weight: 700; }

/* Per-zone bar chart of observed vs baseline */
.tc-zones {
  display: flex; flex-direction: column; gap: 6px; margin-bottom: 10px;
}
.tc-zone-row {
  display: grid; grid-template-columns: 100px 1fr 40px 50px;
  gap: 12px; align-items: center;
  font-family: var(--font-body); font-size: 12px;
  font-variant-numeric: tabular-nums;
}
.tc-zone-lbl {
  color: var(--ink-soft); font-weight: 600;
}
.tc-zone-bar {
  height: 12px; background: var(--line-soft);
  border-radius: 3px; overflow: hidden;
}
.tc-zone-fill {
  height: 100%; background: var(--ink-faint);
  border-radius: 3px;
}
.tc-zone-pct {
  font-weight: 700; color: var(--ink); text-align: right;
}
.tc-zone-delta {
  font-size: 11px; font-weight: 600; color: var(--ink-mute);
  text-align: right;
}
.tc-zone-delta.pos { color: var(--emerald-deep); }
.tc-zone-delta.neg { color: var(--rose); }
.tc-sample {
  font-family: var(--font-body); font-size: 11px; color: var(--ink-faint);
  font-style: italic; margin-top: 8px;
}

/* Track conditions card - venue overall with AU avg overlay */
.tc-panel {
  background: var(--panel); border: 1px solid var(--line);
  border-radius: var(--radius-sm); padding: 14px 16px;
}
.tc-panel.tc-insufficient-panel {
  opacity: 0.7; font-style: italic;
}
.tc-panel-title {
  font-family: var(--font-body); font-size: 13px; font-weight: 700;
  color: var(--ink); margin-bottom: 8px;
  display: flex; justify-content: space-between; align-items: baseline;
  gap: 8px; flex-wrap: wrap;
}
.tc-panel-meta {
  font-size: 10px; font-weight: 500; color: var(--ink-mute);
  text-transform: uppercase; letter-spacing: 0.04em;
}
.tc-summary {
  font-family: var(--font-body); font-size: 13px; color: var(--ink-soft);
  margin-bottom: 12px; line-height: 1.5;
}
.tc-summary strong { color: var(--ink); font-weight: 700; }

/* Legend row - swatch + label for venue + AU avg */
.tc-dualbar-legend {
  display: flex; gap: 16px; margin-bottom: 8px;
  font-family: var(--font-body); font-size: 11px; color: var(--ink-mute);
  font-weight: 500;
}
.tc-legend-item { display: inline-flex; align-items: center; gap: 6px; }
.tc-legend-item .swatch {
  display: inline-block; width: 14px; height: 8px; border-radius: 2px;
}
.tc-legend-item .swatch-venue { background: var(--slate); }
.tc-legend-item .swatch-au    { background: var(--indigo-bg); border: 1px solid var(--indigo); }

/* Dual bars - venue on top half, AU avg on bottom half. Both equally
   visible, no overlap, easy side-by-side comparison. */
.tc-dualbars { display: flex; flex-direction: column; gap: 10px; }
.tc-dualbar-row {
  display: grid; grid-template-columns: 110px 1fr 80px;
  gap: 12px; align-items: center;
  font-family: var(--font-body); font-size: 12px;
  font-variant-numeric: tabular-nums;
}
.tc-dualbar-row .tc-zone-lbl {
  color: var(--ink-soft); font-weight: 600;
}
.tc-dualbar-track {
  position: relative; height: 26px; background: transparent;
  border-radius: 3px;
  display: flex; flex-direction: column; gap: 2px;
}
.tc-dualbar-venue {
  height: 11px; background: var(--slate); border-radius: 2px;
  min-width: 4px;
}
.tc-dualbar-au {
  height: 11px; background: #6366f1; border-radius: 2px;
  min-width: 4px;
  opacity: 0.85;
}
.tc-dualbar-pcts {
  display: flex; flex-direction: column; gap: 2px;
  justify-content: center;
  font-weight: 600; line-height: 1.1;
}
.tc-pct-venue { color: var(--ink); }
.tc-pct-au    { color: #6366f1; font-size: 11px; }

/* Legend swatches */
.tc-legend-item .swatch-au {
  background: #6366f1;
}

.tc-source-note {
  font-family: var(--font-body); font-size: 10px; color: var(--ink-faint);
  font-style: italic; margin-top: 12px;
}

/* PF barrier x runstyle A2E grid. Shows performance vs market expectations
   by barrier band (1-3, 4-7, 8+, Totals) for each run style (Forward,
   Midfield, Back). A2E = Actual To Expected; 1.00 is neutral, <0.95 is
   below expectation (red), >1.15 is above (green). PF's own thresholds. */
.pf-bias-panel {
  background: var(--panel); border: 1px solid var(--line);
  border-radius: var(--radius-md); padding: 14px 18px;
  margin-top: 12px;
}
.pf-bias-title {
  font-family: var(--font-display); font-size: 13px; font-weight: 700;
  color: var(--ink); margin-bottom: 4px;
  display: flex; justify-content: space-between; align-items: baseline;
  gap: 12px;
}
.pf-bias-meta {
  font-family: var(--font-body); font-size: 11px; font-weight: 500;
  color: var(--ink-mute);
}
.pf-bias-blurb {
  font-family: var(--font-body); font-size: 11px; color: var(--ink-mute);
  margin-bottom: 10px; line-height: 1.4;
}
.pf-bias-grid {
  display: grid;
  /* Barrier label + 3 run-style cells. Cells share width via 1fr. */
  grid-template-columns: 78px repeat(3, 1fr);
  gap: 4px;
  font-family: var(--font-mono);
}
.pf-bias-cell {
  padding: 7px 6px; text-align: center;
  font-size: 12px; font-weight: 600;
  border-radius: 4px; background: var(--line-soft);
  color: var(--ink);
}
/* Header row - styled distinctly from data cells */
.pf-bias-cell.pf-bias-h {
  background: transparent; color: var(--ink-mute);
  font-family: var(--font-body); font-size: 10px;
  font-weight: 700; text-transform: uppercase;
  letter-spacing: 0.05em; padding: 4px 6px;
}
/* Barrier label column on each data row */
.pf-bias-cell.pf-bias-band {
  background: transparent; color: var(--ink-soft);
  font-family: var(--font-body); font-size: 11px;
  font-weight: 600; text-align: left;
  padding-left: 4px;
}
.pf-bias-cell.pf-bias-band.pf-bias-totals {
  border-top: 1px solid var(--line); padding-top: 9px; margin-top: 2px;
  color: var(--ink);
}
/* Totals row gets a top divider on data cells too */
.pf-bias-cell.pf-bias-totals {
  border-top: 1px solid var(--line); padding-top: 9px; margin-top: 2px;
}
/* A2E colour gates - PF's own thresholds */
.pf-bias-cell.pf-bias-good {
  background: var(--emerald-bg); color: var(--emerald-deep);
}
.pf-bias-cell.pf-bias-bad {
  background: var(--rose-bg); color: var(--rose);
}
.pf-bias-cell.pf-bias-empty {
  background: transparent; color: var(--ink-faint);
}

/* A2E legend - shown once below the grid */
.pf-bias-legend {
  display: flex; gap: 14px; margin-top: 10px;
  font-family: var(--font-body); font-size: 10px; color: var(--ink-mute);
  align-items: center; flex-wrap: wrap;
}
.pf-bias-legend .swatch {
  display: inline-block; width: 10px; height: 10px;
  border-radius: 2px; margin-right: 4px; vertical-align: middle;
}
.pf-bias-legend .sw-good { background: var(--emerald-bg); border: 1px solid var(--emerald-line); }
.pf-bias-legend .sw-bad  { background: var(--rose-bg);    border: 1px solid var(--rose-line); }

/* Mobile */
@media (max-width: 720px) {
  .pf-bias-panel { padding: 12px 14px; }
  .pf-bias-grid { grid-template-columns: 62px repeat(3, 1fr); gap: 3px; }
  .pf-bias-cell { padding: 6px 4px; font-size: 11px; }
  .pf-bias-cell.pf-bias-h { font-size: 9px; }
  .pf-bias-cell.pf-bias-band { font-size: 10px; }
  .pf-bias-title { font-size: 12px; }
}

/* Mobile */
@media (max-width: 720px) {
  .track-conditions-card { padding: 12px 14px; }
  .tc-dualbar-row { grid-template-columns: 80px 1fr 70px; gap: 8px; font-size: 11px; }
}

/* Race detail */
.race-detail {
  background: var(--panel); border: 1px solid var(--line);
  border-radius: var(--radius-lg); padding: 0; overflow: hidden;
}
.race-header {
  background: linear-gradient(to bottom, #1c1917, #292524);
  color: #fafaf9; padding: 18px 22px;
  display: flex; align-items: baseline; justify-content: space-between;
  flex-wrap: wrap; gap: 16px;
}
.race-header h2 {
  font-family: var(--font-body); font-weight: 700; font-size: 18px;
  letter-spacing: -0.01em;
}
.race-header .race-meta-line {
  font-family: var(--font-body); font-size: 12px; color: #a8a29e;
  margin-top: 4px; font-weight: 500;
}
.race-header-stats {
  display: flex; gap: 24px; align-items: center;
  font-family: var(--font-body); font-size: 12px; font-weight: 500;
  flex-wrap: wrap;
}
.race-header-stats .item { color: #a8a29e; }
.race-header-stats .item .v { color: #fafaf9; font-weight: 700; }
@media (max-width: 720px) {
  /* Black race banner: tighter padding, smaller fonts, allow stats to wrap
     onto own line beneath title to free horizontal space */
  .race-header {
    padding: 12px 14px;
    gap: 8px;
  }
  .race-header h2 { font-size: 16px; }
  .race-header .race-meta-line { font-size: 11px; margin-top: 2px; }
  .race-header-stats { gap: 8px 12px; font-size: 11px; width: 100%; }
  .race-header-stats .item { font-size: 11px; }
  /* Score-top3 indicator inline alongside other items rather than full row.
     Brighten background and badges so the #1 #3 #10 readout is clearly
     readable on the dark banner. Previously the rgba(.15) badges rendered
     near-invisible against the black gradient. */
  .score-top3 {
    padding: 4px 10px; font-size: 11px;
    background: rgba(255,255,255,0.12);
  }
  .score-top3 .lbl { font-size: 9px; }
  .score-top3 .tab-num {
    padding: 2px 7px; font-size: 11px; font-weight: 700;
    background: rgba(255,255,255,0.28); color: #fff;
  }
}

.race-table-wrap { overflow-x: auto; }
.race-table {
  width: 100%; border-collapse: collapse;
  font-family: var(--font-body); font-size: 12px;
  font-variant-numeric: tabular-nums;
}
.race-table thead th {
  background: var(--line-soft); border-bottom: 1px solid var(--line);
  text-align: left; padding: 10px 12px;
  font-family: var(--font-body); font-size: 10px; font-weight: 700;
  text-transform: uppercase; letter-spacing: 0.06em; color: var(--ink-mute);
  cursor: pointer; user-select: none; white-space: nowrap;
  /* Sticky on desktop only - column headers stay visible while scrolling
     the runner list. Disabled on mobile because the sticky header was
     overlapping the race banner's "X above 0.60" indicator and made the
     layered headers feel crowded (sticky tabs + sticky thead = 2 sticky
     layers competing for space). On mobile, scrolling back to see header
     labels is acceptable; the table is short enough that scroll cost is low. */
  position: sticky;
  top: 0;
  z-index: 5;
}
@media (max-width: 720px) {
  /* Mobile: drop the sticky behaviour - it was conflicting with the race
     banner. Headers scroll naturally with the table. */
  .race-table thead th { position: static; }
}
.race-table thead th:hover { background: #ede9e1; }
.race-table tbody td {
  padding: 9px 12px; border-bottom: 1px solid var(--line-soft);
  white-space: nowrap; font-weight: 500;
}
.race-table tbody tr:hover { background: var(--line-soft); }
.race-table tbody tr { cursor: pointer; }
.race-table tbody tr.expanded { background: #ede9e1; }
.race-table tbody tr.race-detail-row { cursor: default; background: var(--panel) !important; }
.race-table tbody tr.race-detail-row:hover { background: var(--panel) !important; }
.race-table tbody tr.race-detail-row > td {
  padding: 14px 18px; border-top: 2px solid var(--ink);
}
.rd-runner-detail {
  display: grid; grid-template-columns: repeat(auto-fit, minmax(220px, 1fr));
  gap: 16px;
}
.rd-section {
  background: var(--line-soft); border-radius: 6px; padding: 10px 12px;
}
.rd-section-title {
  font-size: 10px; text-transform: uppercase; letter-spacing: 0.06em;
  color: var(--ink-mute); font-weight: 700; margin-bottom: 8px;
  padding-bottom: 6px; border-bottom: 1px solid var(--line);
}
.rd-section-body { display: flex; flex-direction: column; gap: 6px; }
.rd-field { display: flex; gap: 8px; align-items: baseline; font-size: 12px; }
.rd-fl { color: var(--ink-mute); min-width: 105px; flex-shrink: 0; }
.rd-fv { color: var(--ink); font-weight: 500; }
/* Inline rank pill used in detail panel for Mid/Total speed score fields.
   Shows the per-race rank (#1, #2, #3) alongside the raw value. Colour
   matches the table sectCell convention - emerald for top-3, plain for rest. */
.rd-rank-pill {
  display: inline-block; margin-left: 4px;
  font-family: var(--font-mono); font-size: 10px;
  padding: 0 4px; border-radius: 3px;
  background: var(--line); color: var(--ink-mute);
}
.rd-rank-pill.r1 { background: var(--emerald); color: #fff; font-weight: 600; }
.rd-rank-pill.r2 { background: var(--emerald-bg); color: var(--emerald-deep); }
.rd-rank-pill.r3 { background: #f0fdf4; color: var(--emerald-deep); }
@media (max-width: 720px) {
  .rd-runner-detail { grid-template-columns: 1fr; gap: 10px; }
  .rd-fl { min-width: 90px; }
}
/* Pick rows - emerald-tinted background + 4px emerald left border so they're
   unmistakable when scanning down the runners table. The border accent uses
   box-shadow inset (not border-left) because adding a real border would push
   table cells over and break alignment. box-shadow inset paints over the
   first cell's background without affecting layout. */
.race-table tbody tr.is-pick {
  background: var(--emerald-bg);
  box-shadow: inset 4px 0 0 var(--emerald);
}
.race-table tbody tr.is-pick:hover { background: #d1fae5; }
/* Loose-only pick rows - amber treatment mirroring Main's emerald. */
.race-table tbody tr.is-loose-pick {
  background: rgba(217, 119, 6, 0.08);
  box-shadow: inset 4px 0 0 #d97706;
}
.race-table tbody tr.is-loose-pick:hover { background: rgba(217, 119, 6, 0.16); }
.race-table tbody tr.muted { color: var(--ink-mute); }

/* Pick badge - compact single-letter indicator AFTER the horse name.
   Two badges can appear side-by-side when both models pick (M then L).
   - pick-badge-main:  green "M" (production model)
   - pick-badge-loose: amber "L" (experimental model) */
.pick-badge {
  display: inline-block; margin-left: 6px;
  font-family: var(--font-body); font-size: 10px; font-weight: 700;
  letter-spacing: 0.02em;
  padding: 1px 5px; border-radius: 3px;
  vertical-align: 1px; line-height: 1.2;
  min-width: 8px; text-align: center;
}
.pick-badge + .pick-badge { margin-left: 3px; }
.pick-badge-main  { background: var(--emerald); color: #fff; }
.pick-badge-loose { background: #d97706; color: #fff; }

/* Finish-position row treatment.
   Row-level background tints removed 2026-05-15 - they were visually busy
   on resulted races. The small "1st"/"2nd"/"3rd" pill before the horse
   name (.finish-badge) is sufficient to convey position. Non-runners
   (finish-other) still mute slightly so they recede visually. */
.race-table tbody tr.finish-other { color: var(--ink-mute); }

/* Finish badge - sits inline before the horse name. Gold/silver/bronze
   colours for top-3, neutral grey for everything below. Compact so it
   doesn't shove the horse name too far right. */
.finish-badge {
  display: inline-block; margin-right: 6px;
  font-family: var(--font-mono); font-size: 10px; font-weight: 700;
  letter-spacing: 0.02em;
  padding: 1px 5px; border-radius: 3px;
  vertical-align: 1px;
}
.finish-badge-1 { background: #fbbf24; color: #78350f; }   /* gold */
.finish-badge-2 { background: #cbd5e1; color: #1e293b; }   /* silver */
.finish-badge-3 { background: #fdba74; color: #7c2d12; }   /* bronze */
.finish-badge-other { background: var(--line); color: var(--ink-mute); }
.tn-cell {
  display: inline-block; min-width: 22px; height: 22px; line-height: 22px;
  text-align: center; background: var(--ink); color: var(--panel);
  font-weight: 700; border-radius: 4px; padding: 0 6px;
  font-size: 11px;
}
.horse-cell { font-weight: 700; color: var(--ink); }
.is-pick .horse-cell { color: var(--emerald-deep); }
.is-loose-pick .horse-cell { color: #b45309; }

.rank-cell { font-weight: 600; color: var(--ink-soft); }
.rank-cell.r1 { color: var(--emerald-deep); font-weight: 700; }
.rank-cell.r2 { color: var(--emerald-deep); font-weight: 600; }
.rank-cell.r3 { color: var(--ink-soft); }

/* Sectional cells: value with rank superscript-style */
.sect-cell {
  white-space: nowrap;
}
.sect-cell .v {
  font-weight: 600; color: var(--ink-soft);
}
.sect-cell .rk {
  font-size: 9px; font-weight: 700; margin-left: 4px;
  display: inline-block; padding: 1px 5px; border-radius: 8px;
  background: var(--line-soft); color: var(--ink-mute);
  vertical-align: middle;
}
.sect-cell.r1 .v { color: var(--emerald-deep); font-weight: 700; }
.sect-cell.r1 .rk { background: var(--emerald); color: #fff; }
.sect-cell.r2 .v { color: var(--emerald-deep); }
.sect-cell.r2 .rk { background: var(--emerald-bg); color: var(--emerald-deep); }
.sect-cell.r3 .rk { background: #f0fdf4; color: var(--emerald-deep); }

/* Cumulative score cell on race tab - shows numeric score + rank pill */
.score-cell { white-space: nowrap; font-weight: 600; }
.score-cell .v { color: var(--ink); }
.score-cell .rk {
  display: inline-block; margin-left: 4px;
  font-size: 9px; font-weight: 700; padding: 1px 5px; border-radius: 8px;
  background: var(--line-soft); color: var(--ink-mute);
  vertical-align: middle;
}
.score-cell.r1 .v { color: var(--emerald-deep); font-weight: 700; }
.score-cell.r1 .rk { background: var(--emerald); color: #fff; }
.score-cell.r2 .v { color: var(--emerald-deep); }
.score-cell.r2 .rk { background: var(--emerald-bg); color: var(--emerald-deep); }
.score-cell.r3 .rk { background: #f0fdf4; color: var(--emerald-deep); }

/* Votes cell on race table - shows N/6 voting signal hits at top-3 for each
   horse. Colour-coded so users can spot strong candidates without reading
   the number: 5-6 votes (the V3 threshold) = strong emerald; 4 = light;
   <=2 = muted grey to fade non-contenders. */
.votes-cell { white-space: nowrap; font-weight: 600; text-align: left; }
.votes-cell .v { font-variant-numeric: tabular-nums; }
.votes-cell .votes-star {
  font-size: 10px; color: #fbbf24; font-weight: 700; margin-left: 3px;
}
.votes-cell.votes-strong {
  background: rgba(16,185,129,0.10);
}
.votes-cell.votes-strong .v { color: var(--emerald-deep); font-weight: 700; }
.votes-cell.votes-mid .v { color: var(--emerald-deep); }
.votes-cell.votes-weak .v { color: var(--ink-faint); }
/* Confidence dot in race-table score cell - filled = unanimous, hollow = split */
.score-cell .conf-dot {
  display: inline-block; width: 7px; height: 7px; border-radius: 50%;
  vertical-align: middle; border: 1px solid var(--ink-mute);
  margin-left: 2px;
}
.score-cell .conf-dot.high { background: var(--ink-mute); }
.score-cell .conf-dot.mid {
  background: linear-gradient(to right, var(--ink-mute) 50%, transparent 50%);
}
.score-cell .conf-dot.low { background: transparent; opacity: 0.6; }
.score-cell.r1 .conf-dot { border-color: var(--emerald-deep); }
.score-cell.r1 .conf-dot.high { background: var(--emerald-deep); }
.score-cell.r1 .conf-dot.mid {
  background: linear-gradient(to right, var(--emerald-deep) 50%, transparent 50%);
}

/* Inline score pill used in Today tab pick row signals strip */
.score-pill {
  display: inline-flex; align-items: center; gap: 4px;
  padding: 2px 8px; border-radius: 10px; font-size: 11px; font-weight: 600;
  background: var(--line-soft); color: var(--ink-soft);
  white-space: nowrap;
}
.score-pill.r1 { background: var(--emerald); color: #fff; }
.score-pill.r2 { background: var(--emerald-bg); color: var(--emerald-deep); }
.score-pill.r3 { background: #f0fdf4; color: var(--emerald-deep); }
.score-pill .lbl { font-size: 9px; opacity: 0.85; letter-spacing: 0.04em; text-transform: uppercase; }

/* Race banner "Top 3 by score" inline indicator */
.score-top3 {
  display: inline-flex; align-items: center; gap: 6px;
  padding: 4px 10px; border-radius: 6px; font-size: 12px;
  background: rgba(255,255,255,0.08); color: rgba(255,255,255,0.85);
}
.score-top3 .lbl { font-size: 10px; opacity: 0.7; letter-spacing: 0.05em; text-transform: uppercase; }
.score-top3 .tabs { display: inline-flex; gap: 4px; }
.score-top3 .tab-num {
  display: inline-block; padding: 1px 7px; border-radius: 4px;
  background: rgba(255,255,255,0.15); color: #fff; font-weight: 700;
  font-size: 11px;
}
.score-top3.no-quals { background: rgba(220,80,80,0.15); }
.score-top3.no-quals .lbl { color: #fca5a5; opacity: 0.95; }

/* Race table rows that qualify by score threshold get a subtle emerald accent */
.race-table tbody tr.score-qualify {
  background: rgba(16,185,129,0.045);
}
.race-table tbody tr.score-qualify:hover {
  background: rgba(16,185,129,0.085);
}
.race-table tbody tr.is-pick.score-qualify {
  /* combine model-pick green with threshold accent */
  background: rgba(16,185,129,0.12);
}

/* Roughie pattern (CS≤3 + Late≤2 + Fxd≥$10). Amber accent — these are the
   long-shot value plays (~49% ROI in backtest at small samples). */
.race-table tbody tr.roughie-bet {
  background: rgba(245,158,11,0.06);
  box-shadow: inset 3px 0 0 #f59e0b;
}
.race-table tbody tr.roughie-bet:hover {
  background: rgba(245,158,11,0.12);
}
.race-table tbody tr.roughie-bet .horse-cell::after {
  content: 'ROUGHIE';
  display: inline-block; margin-left: 8px;
  padding: 1px 5px; border-radius: 3px;
  background: #f59e0b; color: #fff;
  font-size: 9px; font-weight: 700; letter-spacing: 0.05em;
  vertical-align: middle;
}

.sect-pill {
  display: inline-block; padding: 1px 6px; border-radius: 10px;
  font-size: 11px; font-weight: 600; min-width: 22px; text-align: center;
}
.sect-pill.top1 { background: var(--emerald); color: var(--panel); }
.sect-pill.top2 { background: var(--emerald-bg); color: var(--emerald-deep); }
.sect-pill.other { background: transparent; color: var(--ink-faint); }

.wt-cell.up { color: var(--emerald-deep); font-weight: 600; }
.wt-cell.down { color: var(--ink-faint); }

.dist-cell.has-win { color: var(--emerald-deep); font-weight: 600; }

.drift-cell.firmed { color: var(--emerald-deep); font-weight: 600; }
.drift-cell.drifted { color: var(--rose); }

.edge-cell.value { color: var(--emerald-deep); font-weight: 600; }
.edge-cell.under { color: var(--rose); }

/* Strike rate column for jky/trn */
.rate-cell {
  font-family: var(--font-body); font-weight: 600; font-size: 11px;
  font-variant-numeric: tabular-nums;
  color: var(--ink-soft);
}
.rate-cell.high { color: var(--emerald-deep); }
.rate-cell.mid { color: #92400e; }

/* Sortable column indicators */
.race-table thead th.sortable { cursor: pointer; }
.race-table thead th.sortable:hover {
  background: #ede9e1; color: var(--ink);
}
.race-table thead th.sortable::after {
  content: ' ⇅'; opacity: 0.25; font-size: 9px;
}
.race-table thead th.sort-asc::after { content: ' ↑'; color: var(--emerald); opacity: 1; }
.race-table thead th.sort-desc::after { content: ' ↓'; color: var(--emerald); opacity: 1; }

/* First-starter banner */
.race-banner {
  background: #fef3c7; border: 1px solid #f59e0b;
  border-left: 4px solid #f59e0b;
  padding: 12px 18px; border-radius: 8px;
  margin-bottom: 14px;
  display: flex; align-items: center; gap: 12px;
  font-family: var(--font-body);
}
.race-banner .icon {
  font-size: 18px; flex-shrink: 0;
}
.race-banner .text {
  font-size: 13px; color: #92400e; font-weight: 600;
}
.race-banner .sub {
  font-size: 11px; color: #92400e; font-weight: 500;
  opacity: 0.85; margin-top: 2px;
}

/* First-starter warning shown inside the pick detail panel - same colour palette
   as .race-banner but a bit more compact since it lives inside the row detail */
.pd-fs-warn {
  background: #fef3c7; border: 1px solid #f59e0b;
  border-left: 4px solid #f59e0b;
  padding: 10px 14px; border-radius: 6px;
  margin-bottom: 12px;
  display: flex; align-items: center; gap: 10px;
  font-family: var(--font-body);
}
.pd-fs-warn .icon { font-size: 16px; flex-shrink: 0; }
.pd-fs-warn .text {
  font-size: 12px; color: #92400e; font-weight: 600;
}
.pd-fs-warn .sub {
  font-size: 11px; color: #92400e; font-weight: 500;
  opacity: 0.85; margin-top: 2px;
}

.model-badge {
  display: inline-block; padding: 2px 7px;
  background: var(--emerald); color: var(--panel);
  border-radius: 4px; font-size: 10px; font-weight: 700;
  letter-spacing: 0.04em; text-transform: uppercase;
}

/* PNL tab */
/* ── P&L tab ──────────────────────────────────────────────────────────── */
.pnl-controls {
  display: flex; gap: 16px; align-items: center; flex-wrap: wrap;
  margin-bottom: 16px;
  background: var(--panel); border: 1px solid var(--line);
  border-radius: var(--radius-lg); padding: 12px 16px;
}
.pnl-period-group, .pnl-view-toggle {
  display: flex; gap: 4px; align-items: center;
}
.pnl-view-label {
  font-family: var(--font-body); font-size: 11px; font-weight: 600;
  color: var(--ink-mute); margin-right: 6px;
  text-transform: uppercase; letter-spacing: 0.05em;
}
.pnl-period-btn, .pnl-view-btn {
  font-family: var(--font-body); font-size: 12px; font-weight: 600;
  background: transparent; color: var(--ink-mute);
  border: 1px solid var(--line); border-radius: 6px;
  padding: 6px 14px; cursor: pointer; transition: all 0.12s;
  white-space: nowrap;
}
.pnl-period-btn:hover, .pnl-view-btn:hover {
  background: var(--line-soft); color: var(--ink);
}
.pnl-period-btn.active, .pnl-view-btn.active {
  background: var(--ink); color: var(--panel); border-color: var(--ink);
}
.pnl-period-custom {
  display: flex; gap: 6px; align-items: center;
}
.pnl-period-custom input[type="date"] {
  font-family: var(--font-body); font-size: 12px;
  border: 1px solid var(--line); border-radius: 6px;
  padding: 5px 10px; color: var(--ink-soft);
  background: var(--panel);
}

.pnl-stats-strip {
  display: grid; grid-template-columns: repeat(auto-fit, minmax(120px, 1fr));
  gap: 1px; background: var(--line);
  border: 1px solid var(--line);
  border-radius: var(--radius-lg); overflow: hidden;
  margin-bottom: 18px;
}
.pnl-stat {
  background: var(--panel); padding: 14px 16px;
  display: flex; flex-direction: column; gap: 4px;
}
.pnl-stat .lbl {
  font-family: var(--font-body); font-size: 10px; font-weight: 600;
  text-transform: uppercase; letter-spacing: 0.06em; color: var(--ink-mute);
}
.pnl-stat .val {
  font-family: var(--font-body); font-weight: 800; font-size: 22px;
  color: var(--ink); letter-spacing: -0.02em; line-height: 1.1;
  font-variant-numeric: tabular-nums;
}
.pnl-stat .val.pos { color: var(--emerald-deep); }
.pnl-stat .val.neg { color: var(--rose); }
.pnl-stat .sub {
  font-family: var(--font-body); font-size: 11px; font-weight: 500;
  color: var(--ink-mute);
}

.pnl-charts-grid {
  display: grid; grid-template-columns: 1fr 1fr; gap: 18px;
  margin-bottom: 18px;
}
@media (max-width: 900px) { .pnl-charts-grid { grid-template-columns: 1fr; } }

.pnl-chart-card {
  background: var(--panel); border: 1px solid var(--line);
  border-radius: var(--radius-lg); padding: 18px 22px;
}
.pnl-chart-card h3 {
  font-family: var(--font-body); font-weight: 700; font-size: 14px;
  margin-bottom: 14px; color: var(--ink); letter-spacing: -0.01em;
}
.pnl-chart-card h3 .hint {
  font-weight: 500; color: var(--ink-mute); font-size: 11px;
  margin-left: 6px;
}
.pnl-chart-svg { width: 100%; height: 200px; }
.pnl-chart-svg .axis { stroke: var(--line); }
.pnl-chart-svg .grid { stroke: var(--line-soft); stroke-dasharray: 2,3; }
.pnl-chart-svg .actual { fill: none; stroke: var(--emerald); stroke-width: 2; }
.pnl-chart-svg .expected { fill: none; stroke: var(--ink-faint); stroke-width: 1.5; stroke-dasharray: 4,3; }
.pnl-chart-svg .wr-line { fill: none; stroke: var(--emerald); stroke-width: 2; }
.pnl-chart-svg .wr-expected { fill: none; stroke: var(--ink-faint); stroke-width: 1.5; stroke-dasharray: 4,3; }
.pnl-chart-svg .axis-text {
  fill: var(--ink-mute); font-family: var(--font-body); font-size: 10px;
  font-weight: 500;
}

.pnl-chart-legend {
  display: flex; gap: 24px; margin-top: 10px;
  font-family: var(--font-body); font-size: 11px; color: var(--ink-mute);
  font-weight: 500;
}
.pnl-chart-legend .legend-line {
  display: inline-block; width: 14px; height: 2px;
  background: var(--emerald); vertical-align: middle; margin-right: 6px;
}
.pnl-chart-legend .legend-line.dashed {
  background: transparent; border-top: 1.5px dashed var(--ink-faint);
  height: 0;
}
.pnl-chart-legend .legend-line.mute { border-top-color: var(--ink-faint); }

/* Settled bets list (rich card style like Today tab) */
.bet-history {
  background: var(--panel); border: 1px solid var(--line);
  border-radius: var(--radius-lg); overflow: hidden;
}
.bh-header {
  display: flex; align-items: center; justify-content: space-between;
  padding: 14px 22px; border-bottom: 1px solid var(--line);
  flex-wrap: wrap; gap: 12px;
}
.bh-header h3 {
  font-family: var(--font-body); font-weight: 700; font-size: 14px;
  color: var(--ink); letter-spacing: -0.01em;
}
.bh-controls { display: flex; gap: 14px; align-items: center; }
.bh-filter-toggle {
  font-family: var(--font-body); font-size: 12px; font-weight: 500;
  color: var(--ink-soft); display: flex; align-items: center; gap: 6px;
  cursor: pointer; user-select: none;
}
.bh-filter-toggle input { cursor: pointer; }
.bh-export-btn {
  font-family: var(--font-body); font-size: 11px; font-weight: 600;
  background: transparent; color: var(--ink-mute);
  border: 1px solid var(--line); border-radius: 6px;
  padding: 6px 12px; cursor: pointer; transition: all 0.12s;
}
.bh-export-btn:hover { background: var(--line-soft); color: var(--ink); }

.bh-list { display: flex; flex-direction: column; }
.bh-row {
  display: grid;
  grid-template-columns:
    72px       /* date */
    1fr        /* venue + horse */
    140px      /* fixed/sp/top prices */
    100px      /* finish + result */
    100px      /* P&L */
    120px      /* placed bet toggle */
    24px;      /* expand */
  gap: 14px;
  padding: 12px 22px; align-items: center;
  border-bottom: 1px solid var(--line-soft);
  cursor: pointer; transition: background 0.12s;
  min-height: 52px;
}
.bh-row:last-child { border-bottom: none; }
.bh-row:hover { background: #fafbfc; }
.bh-row.win { background: linear-gradient(to right, rgba(16,185,129,0.05), transparent 60%); }
.bh-row.win:hover { background: linear-gradient(to right, rgba(16,185,129,0.10), #fafbfc 60%); }
.bh-row.placed { box-shadow: inset 4px 0 0 var(--emerald); }

.bh-date {
  font-family: var(--font-body); font-size: 12px; font-weight: 600;
  color: var(--ink-soft); font-variant-numeric: tabular-nums;
}
.bh-runner {
  display: flex; align-items: center; gap: 10px; min-width: 0;
}
.bh-runner .tab-bdg {
  display: inline-block; min-width: 24px; height: 24px; line-height: 24px;
  text-align: center; background: var(--ink); color: var(--panel);
  font-size: 12px; font-weight: 700; border-radius: 4px; padding: 0 6px;
  flex-shrink: 0;
}
.bh-runner .rdetails {
  display: flex; flex-direction: column; min-width: 0;
}
.bh-runner .rhorse {
  font-family: var(--font-body); font-weight: 600; font-size: 14px;
  color: var(--ink); letter-spacing: -0.005em;
  white-space: nowrap; overflow: hidden; text-overflow: ellipsis;
}
.bh-runner .rmeta {
  font-family: var(--font-body); font-weight: 500; font-size: 11px;
  color: var(--ink-mute); margin-top: 1px;
}

.bh-prices {
  display: flex; flex-direction: column; gap: 1px;
  font-family: var(--font-body); font-size: 11px;
  font-variant-numeric: tabular-nums;
}
.bh-prices .pri {
  display: flex; gap: 6px; align-items: baseline;
}
.bh-prices .pri-lbl {
  font-size: 9px; font-weight: 700; letter-spacing: 0.04em;
  text-transform: uppercase; color: var(--ink-mute); width: 22px;
}
.bh-prices .pri-v {
  color: var(--ink-soft); font-weight: 600;
}
.bh-prices .pri-v.top { color: var(--emerald-deep); }

.bh-result {
  display: flex; flex-direction: column; gap: 2px; align-items: flex-start;
}
.bh-result .pos {
  font-family: var(--font-body); font-size: 11px; font-weight: 600;
  color: var(--ink-mute);
}
.bh-result .res {
  font-family: var(--font-body); font-size: 12px; font-weight: 700;
}
.bh-result .res.won { color: var(--emerald-deep); }
.bh-result .res.lost { color: var(--rose); }

.bh-pl {
  font-family: var(--font-body); font-size: 14px; font-weight: 700;
  font-variant-numeric: tabular-nums;
}
.bh-pl.pos { color: var(--emerald-deep); }
.bh-pl.neg { color: var(--rose); }
.bh-pl-stake { font-size: 10px; color: var(--ink-mute); font-weight: 500; }

.bh-bet-cell {
  display: flex; align-items: center; gap: 6px; justify-content: flex-end;
}
.bh-bet-cell .bet-btn {
  /* Reuse Today tab .bet-btn styles */
}
.bh-odds-display {
  font-family: var(--font-body); font-size: 11px; font-weight: 600;
  color: var(--ink-soft); font-variant-numeric: tabular-nums;
  white-space: nowrap;
}
.bh-odds-display.fallback {
  color: var(--ink-mute); font-style: italic;
}
.bh-odds-display .warn-icon {
  color: #f59e0b; margin-left: 3px;
}

.bh-chev {
  font-size: 12px; color: var(--ink-mute);
  transition: transform 0.15s; user-select: none;
}
.bh-row.expanded .bh-chev { transform: rotate(180deg); }

.bh-detail {
  background: #fafbfc; padding: 14px 22px;
  border-bottom: 1px solid var(--line-soft);
  display: none;
}
.bh-detail.open { display: block; }
.bh-detail-link {
  font-family: var(--font-body); font-size: 11px; font-weight: 600;
  color: var(--emerald-deep);
  text-decoration: none; cursor: pointer;
  display: inline-block; margin-bottom: 10px;
}
.bh-detail-link:hover { text-decoration: underline; }
.bh-comments {
  margin-top: 12px; display: flex; flex-direction: column; gap: 6px;
}
.bh-comments label {
  font-family: var(--font-body); font-size: 10px; font-weight: 700;
  text-transform: uppercase; letter-spacing: 0.06em; color: var(--ink-mute);
}
.bh-comments textarea {
  font-family: var(--font-body); font-size: 12px; color: var(--ink-soft);
  border: 1px solid var(--line); border-radius: 6px;
  padding: 8px 10px; resize: vertical; min-height: 50px;
  background: var(--panel);
}

.bh-record {
  margin-top: 12px; display: flex; flex-direction: column; gap: 12px;
}
.bh-record-row {
  display: flex; flex-direction: column; gap: 6px;
}
.bh-record label {
  font-family: var(--font-body); font-size: 10px; font-weight: 700;
  text-transform: uppercase; letter-spacing: 0.06em; color: var(--ink-mute);
}
.bh-record-fields {
  display: flex; gap: 12px; align-items: center;
}
.bh-record-status {
  font-family: var(--font-body); font-size: 12px; font-weight: 600;
  color: var(--ink-mute);
}
.bh-record-status.on { color: var(--emerald-deep); }
.bh-record-fields input[type="number"] {
  font-family: var(--font-body); font-size: 13px; font-weight: 600;
  width: 90px; padding: 6px 10px;
  border: 1px solid var(--line); border-radius: 6px;
  color: var(--ink); background: var(--panel);
  font-variant-numeric: tabular-nums;
}
.bh-record-fields input[type="number"]:focus {
  outline: none; border-color: var(--emerald);
}
.bh-empty {
  padding: 40px 22px; text-align: center;
  color: var(--ink-mute); font-family: var(--font-body); font-size: 13px;
}

@media (max-width: 720px) {
  .bh-row {
    grid-template-columns: 1fr auto;
    grid-template-areas:
      'date    chev'
      'runner  runner'
      'prices  prices'
      'result  pl'
      'bet     bet';
    gap: 8px 12px; padding: 12px;
  }
  .bh-date { grid-area: date; }
  .bh-runner { grid-area: runner; }
  .bh-prices { grid-area: prices; flex-direction: row; gap: 12px; }
  .bh-result { grid-area: result; }
  .bh-pl { grid-area: pl; text-align: right; }
  .bh-bet-cell { grid-area: bet; }
  .bh-chev { grid-area: chev; }
}

/* ── Quaddie tab ──────────────────────────────────────────────────────────── */
.quaddie-controls {
  background: var(--panel); border: 1px solid var(--line);
  border-radius: var(--radius-lg); padding: 16px 20px;
  margin-bottom: 16px;
}
.quaddie-control-row {
  display: flex; flex-wrap: wrap; gap: 18px; align-items: flex-end;
}
.quaddie-control-group {
  display: flex; flex-direction: column; gap: 6px;
}
.quaddie-lbl {
  font-family: var(--font-body); font-size: 10px; font-weight: 600;
  text-transform: uppercase; letter-spacing: 0.06em; color: var(--ink-mute);
}
.quaddie-select {
  font-family: var(--font-body); font-size: 13px; font-weight: 500;
  padding: 8px 12px; border: 1px solid var(--line); border-radius: 6px;
  background: var(--panel); color: var(--ink); min-width: 220px; cursor: pointer;
}
.quaddie-select:focus { outline: 2px solid var(--emerald); outline-offset: -1px; }
.quaddie-thresh-input {
  font-family: var(--font-body); font-size: 13px; font-weight: 600;
  padding: 8px 10px; border: 1px solid var(--line); border-radius: 6px;
  background: var(--panel); color: var(--ink); width: 80px;
  font-variant-numeric: tabular-nums;
}
.btn-tiny {
  font-family: var(--font-body); font-size: 14px; font-weight: 600;
  padding: 6px 10px; border: 1px solid var(--line); border-radius: 6px;
  background: var(--panel); color: var(--ink-mute); cursor: pointer;
}
.btn-tiny:hover { background: var(--line-soft); color: var(--ink); }
.quaddie-help {
  font-family: var(--font-body); font-size: 12px; color: var(--ink-mute);
  margin-top: 14px; line-height: 1.5;
}

/* Race chooser grid - shows all races at the meeting; click to add as leg */
.quaddie-race-grid {
  display: grid; grid-template-columns: repeat(auto-fill, minmax(160px, 1fr));
  gap: 10px; margin-bottom: 18px;
}
.quaddie-race-card {
  background: var(--panel); border: 1px solid var(--line);
  border-radius: 8px; padding: 12px 14px; cursor: pointer;
  transition: all 0.12s; position: relative;
}
.quaddie-race-card:hover {
  border-color: var(--emerald); background: var(--emerald-bg);
}
.quaddie-race-card.selected {
  border-color: var(--emerald); background: var(--emerald-bg);
  box-shadow: 0 0 0 1px var(--emerald) inset;
}
.quaddie-race-card .qr-num {
  font-family: var(--font-body); font-weight: 700; font-size: 14px;
  color: var(--ink);
}
.quaddie-race-card .qr-time {
  font-family: var(--font-mono); font-size: 11px; color: var(--ink-mute);
  margin-top: 2px;
}
.quaddie-race-card .qr-quals {
  font-family: var(--font-body); font-size: 11px; font-weight: 600;
  color: var(--emerald-deep); margin-top: 6px;
}
.quaddie-race-card .qr-quals.zero { color: #b91c1c; }
.quaddie-race-card .qr-leg-tag {
  position: absolute; top: 6px; right: 8px;
  font-size: 9px; font-weight: 700; letter-spacing: 0.05em;
  background: var(--emerald); color: #fff; padding: 2px 6px; border-radius: 10px;
}
.quaddie-race-card .qr-firststarter {
  position: absolute; bottom: 6px; right: 8px;
  font-size: 11px; color: #f59e0b;
}

/* Strategy filter chip - top-left corner of each race card. ✓ for races
   that pass the user's quaddie bet criteria (prize >= $50k AND field >= 8),
   ✗ for ones that fail. Failing cards also get a subtle visual dim so they
   stand out as "would not normally bet" when scanning the meeting. */
.quaddie-race-card .qr-strat {
  position: absolute; top: 6px; left: 8px;
  font-size: 11px; font-weight: 800; line-height: 1;
  padding: 3px 6px; border-radius: 10px;
  cursor: help;
}
.quaddie-race-card .qr-strat.pass {
  background: var(--emerald-bg); color: var(--emerald-deep);
}
.quaddie-race-card .qr-strat.fail {
  background: var(--rose-bg); color: var(--rose);
}
.quaddie-race-card.strat-fail {
  opacity: 0.55;
}
.quaddie-race-card.strat-fail:hover,
.quaddie-race-card.strat-fail.selected {
  opacity: 1;  /* restore full opacity when interacting/selected */
}
/* Push qr-num down a touch so it doesn't collide with the strat chip on
   narrow cards (mobile compact layout especially). */
.quaddie-race-card .qr-num {
  margin-top: 10px;
}

/* Strategy banner above the race grid - meeting-level summary or full
   quaddie pass/fail when 4 legs are selected. */
.quaddie-strategy-banner {
  margin-bottom: 12px;
}
.quaddie-strategy-banner .stratb {
  display: flex; align-items: center; gap: 10px;
  padding: 10px 16px; border-radius: var(--radius-md);
  font-family: var(--font-body); font-size: 13px;
}
.quaddie-strategy-banner .stratb .ico {
  font-weight: 800; font-size: 16px; line-height: 1;
}
.quaddie-strategy-banner .stratb .lbl {
  font-weight: 700; color: var(--ink);
}
.quaddie-strategy-banner .stratb .meta {
  color: var(--ink-mute); font-size: 12px;
}
.quaddie-strategy-banner .stratb.info {
  background: var(--panel); border: 1px solid var(--line);
}
.quaddie-strategy-banner .stratb.pass-quaddie {
  background: var(--emerald-bg); border: 1px solid var(--emerald-line);
}
.quaddie-strategy-banner .stratb.pass-quaddie .ico { color: var(--emerald-deep); }
.quaddie-strategy-banner .stratb.fail-quaddie {
  background: var(--rose-bg); border: 1px solid var(--rose-line);
}
.quaddie-strategy-banner .stratb.fail-quaddie .ico { color: var(--rose); }

/* Summary panel: combos, hit rate, $ at unit */
.quaddie-summary {
  background: var(--panel); border: 1px solid var(--line);
  border-radius: var(--radius-lg); padding: 16px 22px; margin-bottom: 16px;
  display: grid; grid-template-columns: repeat(auto-fit, minmax(140px, 1fr));
  gap: 18px;
}
.quaddie-summary .qs-stat {
  display: flex; flex-direction: column; gap: 4px;
}
.quaddie-summary .qs-stat .lbl {
  font-family: var(--font-body); font-size: 10px; font-weight: 600;
  text-transform: uppercase; letter-spacing: 0.06em; color: var(--ink-mute);
}
.quaddie-summary .qs-stat .val {
  font-family: var(--font-body); font-weight: 800; font-size: 20px;
  color: var(--ink); font-variant-numeric: tabular-nums;
}
.quaddie-summary .qs-stat .val.pos { color: var(--emerald-deep); }
.quaddie-summary .qs-stat .val.neg { color: #b91c1c; }
.quaddie-summary .qs-stat .sub {
  font-family: var(--font-body); font-size: 11px; color: var(--ink-mute);
}
.quaddie-summary .qs-actions {
  display: flex; gap: 8px; align-items: center; justify-self: end;
}

/* Leg cards: 4 cards side by side, one per leg */
.quaddie-legs {
  display: grid; grid-template-columns: repeat(auto-fit, minmax(220px, 1fr));
  gap: 14px;
}
.quaddie-leg-card {
  background: var(--panel); border: 1px solid var(--line);
  border-radius: var(--radius-md); padding: 14px 16px;
}
.quaddie-leg-card .ql-head {
  display: flex; justify-content: space-between; align-items: baseline;
  margin-bottom: 4px;
}
.quaddie-leg-card .ql-title {
  font-family: var(--font-body); font-weight: 700; font-size: 13px;
  color: var(--ink);
}
.quaddie-leg-card .ql-remove {
  font-family: var(--font-body); font-size: 11px; font-weight: 600;
  color: var(--ink-faint); cursor: pointer; padding: 2px 6px;
  border-radius: 4px; border: none; background: none;
}
.quaddie-leg-card .ql-remove:hover { color: #b91c1c; background: #fef2f2; }
.quaddie-leg-card .ql-meta {
  font-family: var(--font-body); font-size: 11px; color: var(--ink-mute);
  margin-bottom: 10px;
}
.quaddie-leg-card .ql-coverage {
  font-family: var(--font-body); font-size: 11px; font-weight: 600;
  color: var(--emerald-deep); margin-bottom: 10px; padding: 4px 8px;
  background: var(--emerald-bg); border-radius: 4px; display: inline-block;
}
.quaddie-leg-card .ql-coverage.warn { color: #92400e; background: #fef3c7; }
.quaddie-leg-card .ql-runners {
  display: flex; flex-direction: column; gap: 6px;
}
.quaddie-leg-card .ql-runner {
  display: grid; grid-template-columns: 28px 1fr auto; gap: 8px; align-items: center;
  padding: 6px 8px; border-radius: 4px; background: var(--line-soft);
  font-family: var(--font-body); font-size: 12px;
}
.quaddie-leg-card .ql-runner.qualifies {
  background: var(--emerald-bg);
}
.quaddie-leg-card .ql-runner .qr-tab {
  font-weight: 700; color: var(--ink); text-align: center;
}
.quaddie-leg-card .ql-runner .qr-horse {
  font-weight: 600; color: var(--ink);
  white-space: nowrap; overflow: hidden; text-overflow: ellipsis;
}
.quaddie-leg-card .ql-runner .qr-score {
  font-weight: 700; color: var(--emerald-deep); font-variant-numeric: tabular-nums;
}
.quaddie-leg-card .ql-runner.qualifies .qr-score { color: var(--emerald-deep); }
.quaddie-leg-card .ql-runner:not(.qualifies) .qr-score { color: var(--ink-faint); }
.quaddie-leg-card .ql-empty {
  font-family: var(--font-body); font-size: 12px; color: var(--ink-faint);
  font-style: italic; padding: 6px 0;
}
.quaddie-leg-card .ql-fs-warn {
  background: #fef3c7; color: #92400e;
  font-family: var(--font-body); font-size: 11px; font-weight: 600;
  padding: 6px 8px; border-radius: 4px; margin-bottom: 10px;
  display: flex; gap: 6px; align-items: center;
}

.quaddie-empty {
  text-align: center; padding: 60px 20px;
  font-family: var(--font-body); color: var(--ink-mute); font-size: 13px;
}

/* ── Insights tab ──────────────────────────────────────────────────────── */
.insights-controls {
  display: flex; justify-content: space-between; align-items: center;
  background: var(--panel); border: 1px solid var(--line);
  border-radius: var(--radius-lg); padding: 12px 18px;
  margin-bottom: 16px; gap: 16px; flex-wrap: wrap;
}
.ic-period-toggle {
  display: inline-flex; gap: 1px; background: var(--line);
  border-radius: var(--radius-sm); padding: 1px;
}
.ic-period-btn {
  font-family: var(--font-body); font-size: 11px; font-weight: 600;
  padding: 6px 12px; border: none; cursor: pointer;
  background: var(--panel); color: var(--ink-mute);
  border-radius: 4px;
}
.ic-period-btn.active { background: var(--ink); color: var(--panel); }
/* Tracking mode toggle - same shape as period toggle so the two pairs read
   as parallel control groups. Selecting 'All theoretical' switches the 6
   pick-based sections to operate on every horse in resulted races. */
.ic-mode-toggle {
  display: inline-flex; gap: 1px; background: var(--line);
  border-radius: var(--radius-sm); padding: 1px;
}
.ic-mode-btn {
  font-family: var(--font-body); font-size: 11px; font-weight: 600;
  padding: 6px 12px; border: none; cursor: pointer;
  background: var(--panel); color: var(--ink-mute);
  border-radius: 4px;
}
.ic-mode-btn.active { background: var(--ink); color: var(--panel); }
/* Model toggle - styled the same as mode toggle. Active button uses
   model-specific color (emerald for main, amber for loose) so the user
   can tell at a glance which model the displayed stats belong to. */
.ic-model-toggle {
  display: inline-flex; gap: 1px; background: var(--line);
  border-radius: var(--radius-sm); padding: 1px;
}
.ic-model-btn {
  font-family: var(--font-body); font-size: 11px; font-weight: 600;
  padding: 6px 12px; border: none; cursor: pointer;
  background: var(--panel); color: var(--ink-mute);
  border-radius: 4px;
}
.ic-model-btn.active { background: var(--ink); color: var(--panel); }
.ic-model-btn[data-imodel="main"].active  { background: var(--emerald); color: #fff; }
.ic-model-btn[data-imodel="loose"].active { background: #d97706; color: #fff; }
/* Toggle hides entirely in "All races" mode - model filter is meaningless
   when not looking at picks at all */
.ic-model-toggle.hidden { display: none; }
.ic-info {
  font-family: var(--font-body); font-size: 12px; color: var(--ink-mute);
  font-variant-numeric: tabular-nums;
}
.ic-info strong { color: var(--ink); font-weight: 700; }

/* Wide insight cards span the full width vs the 2-column grid below */
.insight-wide { margin-bottom: 16px; }

.insights-grid {
  display: grid; grid-template-columns: 1fr 1fr; gap: 18px;
  margin-bottom: 18px;
}
@media (max-width: 900px) { .insights-grid { grid-template-columns: 1fr; } }

.insight-card {
  background: var(--panel); border: 1px solid var(--line);
  border-radius: var(--radius-lg); padding: 18px 22px;
}
.insight-card h3 {
  font-family: var(--font-body); font-weight: 700; font-size: 14px;
  margin-bottom: 8px; color: var(--ink); letter-spacing: -0.01em;
}
.insight-card .desc {
  font-family: var(--font-body); font-size: 12px; font-weight: 500;
  color: var(--ink-mute); margin-bottom: 16px; line-height: 1.5;
}
.insight-card .empty-text {
  font-family: var(--font-body); font-size: 12px; color: var(--ink-faint);
  font-style: italic; padding: 12px 0;
}

/* ── Tracking tab tables ─────────────────────────────────────────────── */
/* Heatmap grid: signal name + 3 columns (top1/top3/top5 WR%) */
.heatmap-grid {
  display: grid; grid-template-columns: minmax(140px, 1fr) repeat(3, 100px);
  gap: 1px; background: var(--line);
  border: 1px solid var(--line); border-radius: var(--radius-sm);
  overflow: hidden;
  font-family: var(--font-body); font-variant-numeric: tabular-nums;
}
.heatmap-grid .hm-cell {
  background: var(--panel); padding: 8px 12px; font-size: 12px;
  display: flex; align-items: center;
}
.heatmap-grid .hm-head {
  background: #f5f3ee; font-weight: 700; font-size: 11px;
  text-transform: uppercase; letter-spacing: 0.04em;
  color: var(--ink); justify-content: center;
}
.heatmap-grid .hm-name { font-weight: 600; color: var(--ink); }
.heatmap-grid .hm-val {
  justify-content: center; font-weight: 600; font-size: 13px;
  flex-direction: column; gap: 1px;
}
/* Heatmap cell colour by WR%: 0 = grey, 50% = mid green, 80%+ = deep green
   Legacy bucketed classes - kept for fallback. Continuous gradient applied
   via inline style (heatmapStyle function) takes precedence. */
.hm-val.hm0 { background: #fafaf9; color: var(--ink-faint); }
.hm-val.hm10 { background: #fef3c7; color: #92400e; }
.hm-val.hm20 { background: #d1fae5; color: #065f46; }
.hm-val.hm30 { background: #a7f3d0; color: #064e3b; }
.hm-val.hm40 { background: #6ee7b7; color: #064e3b; }
.hm-val.hm50 { background: #34d399; color: #064e3b; }
.hm-val.hm60 { background: #10b981; color: #fff; }
.hm-val.hm70 { background: #059669; color: #fff; }
.hm-val.hm80 { background: #047857; color: #fff; }

/* Baseline annotation in heatmap headers - tells users what random
   performance looks like at each top-N level so 13% top-1 (+3 over random)
   reads differently from 13% top-3 (-17 below random). */
.heatmap-grid .hm-baseline {
  font-size: 9px; font-weight: 400; color: var(--ink-faint);
  text-transform: none; letter-spacing: 0; margin-top: 2px;
}

/* Edge indicator under each WR% value - shows signed pp difference from
   random baseline. Tiny subscript so it doesn't dominate the cell. */
.heatmap-grid .hm-edge {
  font-size: 9px; font-weight: 700;
  font-variant-numeric: tabular-nums;
  opacity: 0.85;
  line-height: 1;
}
.heatmap-grid .hm-edge.hm-edge-strong { color: #064e3b; }
.heatmap-grid .hm-edge.hm-edge-pos { color: #065f46; }
.heatmap-grid .hm-edge.hm-edge-flat { color: var(--ink-faint); opacity: 0.6; }
.heatmap-grid .hm-edge.hm-edge-neg { color: #c2410c; }

@media (max-width: 720px) {
  .heatmap-grid {
    grid-template-columns: minmax(70px, 1fr) repeat(3, 1fr);
  }
  .heatmap-grid .hm-cell { padding: 5px 4px; font-size: 11px; }
  .heatmap-grid .hm-head { font-size: 9px; letter-spacing: 0.02em; padding: 5px 2px; }
  .heatmap-grid .hm-val { font-size: 11px; }
  .heatmap-grid .hm-baseline { display: none; }
  .heatmap-grid .hm-edge { font-size: 8px; }
}

/* Period comparison strip - shows top-1 WR for strongest signals across
   7/30/90 day windows. Current window highlighted in emerald. */
.hm-period-cmp {
  margin-top: 14px; padding-top: 12px;
  border-top: 1px dashed var(--line);
}
.hm-period-cmp:empty { display: none; }
.hm-cmp-title {
  font-family: var(--font-body); font-size: 10px; font-weight: 700;
  text-transform: uppercase; letter-spacing: 0.06em;
  color: var(--ink-mute); margin-bottom: 8px;
}
.hm-cmp-rows { display: flex; flex-direction: column; gap: 6px; }
.hm-cmp-row {
  display: flex; align-items: center; gap: 12px;
  font-family: var(--font-body); font-size: 12px;
}
.hm-cmp-sig {
  min-width: 56px; font-weight: 600; color: var(--ink);
}
.hm-cmp-cell {
  display: inline-flex; align-items: baseline; gap: 4px;
  padding: 3px 8px; border-radius: 4px;
  background: var(--line-soft);
  font-variant-numeric: tabular-nums;
}
.hm-cmp-cell.cur {
  background: var(--emerald-bg); color: var(--emerald-deep);
  font-weight: 700;
}
.hm-cmp-cell .lbl {
  font-size: 9px; color: var(--ink-mute); font-weight: 500;
}
.hm-cmp-cell.cur .lbl { color: var(--emerald-deep); opacity: 0.7; }
.hm-cmp-cell .val { font-weight: 600; }
@media (max-width: 720px) {
  .hm-cmp-row { gap: 6px; font-size: 11px; flex-wrap: wrap; }
  .hm-cmp-sig { min-width: 44px; }
  .hm-cmp-cell { padding: 2px 6px; }
}

/* Winners table filter bar - sits above the table, lets users filter by
   signal-rank and free-text. Shows "X of Y" count when filters active. */
.winners-filter-bar {
  display: flex; flex-wrap: wrap; gap: 12px 18px;
  padding: 10px 12px; margin-bottom: 8px;
  background: var(--line-soft);
  border-radius: 6px;
  font-family: var(--font-body); font-size: 12px;
  align-items: center;
}
.wfb-group { display: flex; align-items: center; gap: 6px; }
.wfb-lbl {
  font-size: 10px; font-weight: 700; text-transform: uppercase;
  letter-spacing: 0.06em; color: var(--ink-mute);
}
.wfb-select, .wfb-text, .wfb-num {
  font-family: var(--font-body); font-size: 12px;
  padding: 4px 8px; border: 1px solid var(--line);
  border-radius: 4px; background: var(--panel); color: var(--ink);
}
.wfb-text { width: 140px; }
.wfb-num { width: 48px; text-align: center; }
.wfb-range { display: inline-flex; align-items: center; gap: 4px; }
.wfb-dash { font-size: 10px; color: var(--ink-mute); }
.wfb-info { margin-left: auto; }
.wfb-clear {
  font-family: var(--font-body); font-size: 11px; font-weight: 600;
  padding: 4px 10px; border: 1px solid var(--line);
  border-radius: 4px; background: var(--panel); color: var(--ink-mute);
  cursor: pointer; transition: all 0.12s;
}
.wfb-clear:hover { background: var(--rose-bg); color: var(--rose); border-color: var(--rose); }
.wfb-count {
  font-size: 11px; color: var(--ink-mute); font-weight: 500;
  font-variant-numeric: tabular-nums;
}
@media (max-width: 720px) {
  .winners-filter-bar { gap: 8px 10px; padding: 8px; }
  .wfb-text { width: 100%; }
  .wfb-info { margin-left: 0; width: 100%; justify-content: space-between; }
}

/* Signal correlation matrix: pairwise agreement grid. Diagonal cells are
   100% (self). Off-diagonal cells gradient from emerald (independent) to
   amber (redundant). Helps the user see which signals add unique value. */
.corr-grid {
  display: grid; gap: 2px;
  margin-top: 8px;
  font-family: var(--font-body); font-size: 12px;
}
.corr-cell {
  padding: 8px 6px; text-align: center;
  display: flex; align-items: center; justify-content: center;
  background: var(--panel); min-height: 32px;
}
.corr-head {
  font-family: var(--font-body); font-size: 10px; font-weight: 700;
  text-transform: uppercase; letter-spacing: 0.04em;
  color: var(--ink-mute); background: var(--line-soft);
}
.corr-row-head {
  font-weight: 600; color: var(--ink);
  background: var(--line-soft);
  font-size: 11px;
  justify-content: flex-end; padding-right: 10px;
}
.corr-val {
  font-variant-numeric: tabular-nums; cursor: help;
}
.corr-summary {
  margin-top: 12px; padding: 10px 12px;
  background: var(--line-soft); border-radius: 6px;
  font-family: var(--font-body); font-size: 12px;
  display: flex; flex-direction: column; gap: 4px;
}
.corr-summary .lbl {
  font-size: 10px; font-weight: 700; text-transform: uppercase;
  letter-spacing: 0.04em; color: var(--ink-mute);
  margin-right: 6px;
}
@media (max-width: 720px) {
  .corr-grid { font-size: 10px; }
  .corr-cell { padding: 4px 2px; min-height: 26px; }
  .corr-head, .corr-row-head { font-size: 9px; }
}

/* Mini-tables shared by threshold curve, day-of-week, venue, distance,
   going, and field-size breakdowns. Simpler than the full tracking tables -
   no sticky headers, no horizontal scroll, just clean rows of stats. */
.tracking-mini-table {
  width: 100%; border-collapse: collapse;
  font-family: var(--font-body); font-size: 12px;
  font-variant-numeric: tabular-nums;
}
.tracking-mini-table thead th {
  background: var(--line-soft);
  text-align: left; padding: 8px 10px;
  font-size: 10px; font-weight: 700;
  text-transform: uppercase; letter-spacing: 0.06em;
  color: var(--ink-mute);
  border-bottom: 1px solid var(--line);
}
.tracking-mini-table thead th + th { text-align: right; }
.tracking-mini-table tbody td {
  padding: 7px 10px; border-bottom: 1px solid var(--line-soft);
}
.tracking-mini-table tbody td.lbl { font-weight: 600; color: var(--ink); }
.tracking-mini-table tbody td.num { text-align: right; }
.tracking-mini-table tbody td.num.pos { color: var(--emerald-deep); font-weight: 700; }
.tracking-mini-table tbody td.num.neg { color: var(--rose); font-weight: 700; }
.tracking-mini-table tbody td.empty {
  color: var(--ink-faint); font-style: italic; text-align: center;
}
.tracking-mini-table tbody tr:last-child td { border-bottom: none; }
.tracking-mini-table .small-sample {
  color: var(--amber); font-weight: 700; cursor: help;
}
.tracking-note {
  margin-top: 10px;
  font-family: var(--font-body); font-size: 11px;
  color: var(--ink-mute); line-height: 1.5;
  padding: 8px 12px; background: var(--line-soft);
  border-left: 3px solid var(--ink-faint); border-radius: 3px;
}

/* ── Database tab ─────────────────────────────────────────────────────────
   Filter bar, stats strip, runners table. Filter bar can collapse to save
   space once user has set their query. Table uses horizontal scroll on all
   viewports since 20+ columns don't fit narrow screens. */
.db-controls {
  background: var(--panel); border: 1px solid var(--line);
  border-radius: var(--radius-md); margin-bottom: 14px;
}
.db-controls-toggle {
  display: flex; align-items: center; gap: 8px;
  width: 100%; padding: 10px 14px;
  background: transparent; border: 0; cursor: pointer;
  font-family: var(--font-body); font-size: 12px; font-weight: 600;
  color: var(--ink); text-align: left;
  border-bottom: 1px solid var(--line);
}
.db-controls-toggle:hover { background: var(--line-soft); }
.db-controls.collapsed .db-controls-toggle { border-bottom: none; }
.db-controls-toggle-label { letter-spacing: 0.04em; text-transform: uppercase; font-size: 11px; }
.db-controls-toggle-chev {
  margin-left: auto; color: var(--ink-mute);
  transition: transform 0.12s;
}
.db-controls.collapsed .db-controls-toggle-chev { transform: rotate(-90deg); }
.db-filters {
  padding: 12px 14px;
}
.db-controls.collapsed .db-filters { display: none; }
.db-filter-row {
  display: flex; flex-wrap: wrap; gap: 10px;
  margin-bottom: 10px; align-items: flex-end;
}
.db-filter-row:last-child { margin-bottom: 0; }
.db-filter-group { display: flex; flex-direction: column; gap: 3px; }
.db-filter-group label {
  font-family: var(--font-body); font-size: 9px; font-weight: 700;
  letter-spacing: 0.06em; text-transform: uppercase;
  color: var(--ink-mute);
}
.db-input {
  font-family: var(--font-body); font-size: 12px;
  background: var(--panel); color: var(--ink);
  border: 1px solid var(--line); border-radius: var(--radius-sm);
  padding: 5px 8px; min-width: 120px;
}
.db-input:hover { border-color: var(--ink-faint); }
.db-input-narrow { min-width: 70px; max-width: 90px; }
.db-input-tiny   { min-width: 60px; padding: 4px 6px; font-size: 11px; }

.db-filter-signals { align-items: flex-end; }
.db-filter-group-label {
  font-family: var(--font-body); font-size: 10px; font-weight: 700;
  letter-spacing: 0.06em; text-transform: uppercase;
  color: var(--ink-mute);
  padding-bottom: 5px; margin-right: 4px;
}
.db-signal-filter { display: flex; flex-direction: column; gap: 3px; }
.db-signal-filter label {
  font-family: var(--font-body); font-size: 10px; font-weight: 600;
  color: var(--ink-soft); text-align: center;
}
.db-quick-btn {
  font-family: var(--font-body); font-size: 11px; font-weight: 600;
  background: var(--ink); color: var(--panel);
  border: 0; border-radius: var(--radius-sm);
  padding: 6px 10px; cursor: pointer; margin-left: 4px;
  height: 28px;
}
.db-quick-btn:hover { background: var(--emerald); }
.db-quick-btn.active { background: var(--emerald); }

.db-filter-actions { justify-content: space-between; }
.db-reset {
  font-family: var(--font-body); font-size: 11px; font-weight: 600;
  background: transparent; color: var(--rose);
  border: 1px solid var(--rose); border-radius: var(--radius-sm);
  padding: 5px 10px; cursor: pointer;
}
.db-reset:hover { background: var(--rose); color: #fff; }
.db-filter-summary {
  font-family: var(--font-mono); font-size: 11px; color: var(--ink-mute);
}

/* Stats strip - computed metrics over visible rows */
.db-stats-strip {
  display: grid; grid-template-columns: repeat(auto-fit, minmax(140px, 1fr));
  gap: 1px; background: var(--line); border-radius: var(--radius-md);
  border: 1px solid var(--line); overflow: hidden;
  margin-bottom: 14px;
}
.db-stat {
  background: var(--panel); padding: 10px 14px;
}
.db-stat .lbl {
  font-family: var(--font-body); font-size: 9px; font-weight: 700;
  letter-spacing: 0.06em; text-transform: uppercase;
  color: var(--ink-mute);
}
.db-stat .val {
  font-family: var(--font-body); font-size: 18px; font-weight: 700;
  color: var(--ink); font-variant-numeric: tabular-nums;
  margin-top: 2px;
}
.db-stat .val.pos { color: var(--emerald-deep); }
.db-stat .val.neg { color: var(--rose); }
.db-stat .sub {
  font-family: var(--font-body); font-size: 10px; color: var(--ink-mute);
  margin-top: 2px;
}

/* Table - horizontal scroll, sticky header */
.db-table-wrap {
  background: var(--panel); border: 1px solid var(--line);
  border-radius: var(--radius-md); overflow: auto;
  max-height: 75vh;
}
.db-table {
  width: 100%; border-collapse: collapse;
  font-family: var(--font-body); font-size: 12px;
  font-variant-numeric: tabular-nums;
}
.db-table thead th {
  background: var(--line-soft);
  position: sticky; top: 0; z-index: 1;
  padding: 8px 10px; text-align: left;
  font-size: 10px; font-weight: 700;
  text-transform: uppercase; letter-spacing: 0.04em;
  color: var(--ink-mute); white-space: nowrap;
  border-bottom: 1px solid var(--line); cursor: pointer;
  user-select: none;
}
.db-table thead th:hover { color: var(--ink); }
.db-table thead th.sort-asc::after  { content: ' ↑'; color: var(--emerald); }
.db-table thead th.sort-desc::after { content: ' ↓'; color: var(--emerald); }
.db-table tbody td {
  padding: 6px 10px; border-bottom: 1px solid var(--line-soft);
  white-space: nowrap;
}
.db-table tbody tr:hover td { background: var(--line-soft); }
.db-table tbody tr.is-pick td { background: rgba(16, 185, 129, 0.08); }
.db-table tbody tr.is-pick:hover td { background: rgba(16, 185, 129, 0.16); }
.db-table tbody tr.is-loose-pick td { background: rgba(217, 119, 6, 0.08); }
.db-table tbody tr.is-loose-pick:hover td { background: rgba(217, 119, 6, 0.16); }
.db-table .horse-link {
  color: var(--ink); font-weight: 600; cursor: pointer;
  border-bottom: 1px dotted var(--ink-faint);
}
.db-table .horse-link:hover { color: var(--emerald-deep); border-bottom-color: var(--emerald); }
.db-table .rk-1 { color: var(--emerald-deep); font-weight: 700; }
.db-table .rk-2, .db-table .rk-3 { color: var(--emerald); font-weight: 600; }
.db-table td.num { text-align: right; }
.db-table .db-pick-pill {
  display: inline-block; font-size: 9px; font-weight: 700;
  padding: 1px 4px; border-radius: 3px; margin-left: 4px;
}
.db-table .db-pick-pill.main  { background: var(--emerald); color: #fff; }
.db-table .db-pick-pill.loose { background: #d97706; color: #fff; }
.db-table .db-finish {
  display: inline-block; min-width: 22px;
  font-size: 11px; font-weight: 700; text-align: center;
  padding: 1px 4px; border-radius: 3px;
}
.db-table .db-finish.f1 { background: #fbbf24; color: #78350f; }
.db-table .db-finish.f2 { background: #cbd5e1; color: #1e293b; }
.db-table .db-finish.f3 { background: #fdba74; color: #7c2d12; }
.db-table .db-finish.fo { background: var(--line); color: var(--ink-mute); }
.db-table-empty {
  padding: 30px; text-align: center;
  font-family: var(--font-body); font-size: 13px; color: var(--ink-mute);
}

/* Threshold curve mode toggle - sits above the table, lets user switch
   between picks-only and all-runners view. Same pill style as P&L period
   buttons so the toggle visual language is consistent across the app. */
.threshold-mode-toggle {
  display: inline-flex; gap: 4px; margin-bottom: 10px;
  padding: 3px; background: var(--line-soft); border-radius: 6px;
}
.th-mode-btn {
  padding: 5px 12px; font-family: var(--font-body); font-size: 11px;
  font-weight: 600; color: var(--ink-mute);
  background: transparent; border: none; border-radius: 4px;
  cursor: pointer; transition: all 0.12s;
}
.th-mode-btn:hover { color: var(--ink); }
.th-mode-btn.active {
  background: var(--ink); color: #fafaf9;
}
@media (max-width: 720px) {
  .tracking-mini-table { font-size: 11px; }
  .tracking-mini-table thead th, .tracking-mini-table tbody td {
    padding: 6px 6px;
  }
}

/* Winners and placegetters tables - similar shape, scrollable */
.tracking-table-wrap { overflow-x: auto; }
.tracking-table {
  width: 100%; border-collapse: collapse;
  font-family: var(--font-body); font-size: 12px;
  font-variant-numeric: tabular-nums; min-width: 1100px;
}
.tracking-table thead th {
  background: var(--ink); color: #fafaf9;
  text-align: left; padding: 8px 10px; font-weight: 600;
  font-size: 11px; text-transform: uppercase; letter-spacing: 0.04em;
  position: sticky; top: 0;
}
.tracking-table thead th.sortable { cursor: pointer; }
.tracking-table thead th.sortable:hover { background: #1f1d1a; }
.tracking-table thead th.sort-asc::after  { content: ' ↑'; color: var(--emerald); }
.tracking-table thead th.sort-desc::after { content: ' ↓'; color: var(--emerald); }
.tracking-table tbody td {
  padding: 6px 10px; border-bottom: 1px solid var(--line-soft);
}
.tracking-table tbody tr:hover { background: var(--line-soft); }
.tracking-table tbody tr.race-row { background: #f5f3ee; font-weight: 600; }
.tracking-table .rank-pill {
  display: inline-block; min-width: 22px; padding: 1px 6px;
  border-radius: 3px; text-align: center; font-weight: 600; font-size: 11px;
  background: var(--line-soft); color: var(--ink-mute);
}
.tracking-table .rank-pill.r-top { background: #d1fae5; color: #065f46; }
.tracking-table .rank-pill.r-mid { background: #fef3c7; color: #92400e; }
.tracking-table .rank-pill.r-out { background: var(--line-soft); color: var(--ink-faint); }
.tracking-table .meeting-link {
  color: var(--ink); text-decoration: none; font-weight: 600;
}
.tracking-table .meeting-link:hover { color: var(--emerald-deep); text-decoration: underline; }
.tracking-table .pos-1 { color: var(--emerald-deep); font-weight: 700; }
.tracking-table .pos-2 { color: #92400e; font-weight: 600; }
.tracking-table .pos-3 { color: #b45309; font-weight: 600; }
.tracking-table .horse-cell { font-weight: 600; min-width: 130px; }
.tracking-table .price-cell { color: var(--ink); font-weight: 500; }

/* ── Mobile responsive layout for tracking tables ─────────────────────────
   Two tables:
     .tracking-winners columns:
       1=Date, 2=Meeting, 3=Race, 4=Dist, 5=Winner, 6=SP,
       7=WPR, 8=Late, 9=Class, 10=L600, 11=PFAI, 12=TR,
       13=Mid, 14=Total, 15=L400, 16=L200, 17=Time
     .tracking-places columns:
       1=Date, 2=Meeting, 3=Race, 4=Pos, 5=Horse, 6=SP,
       7=WPR, 8=Late, 9=Class, 10=L600, 11=PFAI, 12=TR,
       13=Mid, 14=Total, 15=L400, 16=L200, 17=Time

   On mobile: hide long-tail signal columns (Mid/Total/L400/L200/Time = cols
   13-17) on both tables. Hide Race (col 3) on both, plus Dist (col 4) on
   winners table only (Pos stays on places table since it's vital context).
*/
@media (max-width: 720px) {
  .tracking-table {
    min-width: auto;
    font-size: 11px;
  }
  .tracking-table thead th,
  .tracking-table tbody td {
    padding: 4px 5px;
  }
  .tracking-table thead th {
    font-size: 9px;
    letter-spacing: 0.02em;
  }
  /* Hide Race column (col 3) on both tables */
  .tracking-table thead th:nth-child(3),
  .tracking-table tbody td:nth-child(3) {
    display: none;
  }
  /* Hide Dist column (col 4) on Winners table only */
  .tracking-winners thead th:nth-child(4),
  .tracking-winners tbody td:nth-child(4) {
    display: none;
  }
  /* Hide Mid (13), Total (14), L400 (15), L200 (16), Time (17) */
  .tracking-table thead th:nth-child(13),
  .tracking-table thead th:nth-child(14),
  .tracking-table thead th:nth-child(15),
  .tracking-table thead th:nth-child(16),
  .tracking-table thead th:nth-child(17),
  .tracking-table tbody td:nth-child(13),
  .tracking-table tbody td:nth-child(14),
  .tracking-table tbody td:nth-child(15),
  .tracking-table tbody td:nth-child(16),
  .tracking-table tbody td:nth-child(17) {
    display: none;
  }
  /* Tighten horse cell on mobile */
  .tracking-table .horse-cell { min-width: 80px; font-size: 11px; }
  .tracking-table .rank-pill {
    min-width: 18px; padding: 1px 3px; font-size: 10px;
  }
}

/* Threshold P&L table */
.thresh-table {
  display: grid; grid-template-columns: auto auto auto auto auto auto;
  gap: 1px; background: var(--line);
  border: 1px solid var(--line); border-radius: var(--radius-sm);
  overflow: hidden; margin-top: 14px;
  font-family: var(--font-body); font-variant-numeric: tabular-nums;
}
.thresh-table > div {
  background: var(--panel); padding: 8px 12px; font-size: 12px;
}
.thresh-table .h {
  font-weight: 600; color: var(--ink-mute); font-size: 10px;
  text-transform: uppercase; letter-spacing: 0.05em;
  background: var(--line-soft);
}
.thresh-table .row-thresh {
  font-weight: 700; color: var(--ink);
}
.thresh-table .row-current {
  background: var(--emerald-bg);
}
.thresh-table .pos { color: var(--emerald-deep); font-weight: 600; }
.thresh-table .neg { color: var(--rose); font-weight: 600; }

/* Variance stats grid - 4 KPIs in a row */
.var-stats {
  display: grid; grid-template-columns: repeat(4, 1fr); gap: 14px;
  margin-bottom: 14px;
}
@media (max-width: 720px) { .var-stats { grid-template-columns: repeat(2, 1fr); } }
.var-stat {
  background: var(--line-soft); border-radius: var(--radius-sm);
  padding: 10px 12px;
}
.var-stat .lbl {
  font-family: var(--font-body); font-size: 10px; font-weight: 600;
  text-transform: uppercase; letter-spacing: 0.05em; color: var(--ink-mute);
  margin-bottom: 2px;
}
.var-stat .val {
  font-family: var(--font-body); font-weight: 700; font-size: 18px;
  color: var(--ink); font-variant-numeric: tabular-nums;
}
.var-stat .val.pos { color: var(--emerald-deep); }
.var-stat .val.neg { color: var(--rose); }
.var-stat .sub {
  font-family: var(--font-body); font-size: 11px; color: var(--ink-mute);
  margin-top: 2px;
}

/* Inline SVG charts in insight cards */
.insight-card svg.line-chart {
  width: 100%; height: 240px; display: block;
}

/* Edge by price band rows with confidence intervals */
.edge-band-row {
  display: grid; grid-template-columns: 110px 1fr 80px 80px;
  gap: 12px; align-items: center; padding: 6px 0;
  font-family: var(--font-body); font-size: 12px;
  font-variant-numeric: tabular-nums;
}
.edge-band-row .label { font-weight: 600; color: var(--ink); }
.edge-band-row .ci-track {
  position: relative; height: 18px;
  background: var(--line-soft); border-radius: 3px;
  overflow: hidden;
}
.edge-band-row .ci-zero {
  position: absolute; top: 0; bottom: 0;
  width: 1px; background: var(--ink-mute);
  /* JS sets left% based on ROI range mapping */
}
.edge-band-row .ci-bar {
  position: absolute; top: 4px; height: 10px;
  /* JS sets left% and width% based on lower/upper CI */
}
.edge-band-row .ci-bar.pos { background: var(--emerald); }
.edge-band-row .ci-bar.neg { background: var(--rose); }
.edge-band-row .ci-bar.unclear { background: var(--ink-faint); }
.edge-band-row .ci-mean {
  position: absolute; top: 0; bottom: 0; width: 2px;
  background: var(--ink); /* central tendency mark */
}
.edge-band-row .roi-val { font-weight: 700; }
.edge-band-row .roi-val.pos { color: var(--emerald-deep); }
.edge-band-row .roi-val.neg { color: var(--rose); }
.edge-band-row .n-val { color: var(--ink-mute); font-size: 11px; text-align: right; }

.dist-bars { display: flex; flex-direction: column; gap: 8px; }
.dist-bar {
  display: grid; grid-template-columns: 90px 1fr auto;
  gap: 10px; align-items: center;
  font-family: var(--font-body); font-size: 12px; font-weight: 500;
}
.dist-bar .label {
  color: var(--ink-soft); font-weight: 600; white-space: nowrap;
  overflow: hidden; text-overflow: ellipsis;
}
.dist-bar .bar-track {
  height: 8px; background: var(--line-soft); border-radius: 4px;
  overflow: hidden; position: relative;
}
.dist-bar .bar-fill {
  height: 100%; background: var(--emerald); border-radius: 4px;
  transition: width 0.3s ease;
}
.dist-bar .bar-fill.amber { background: #f59e0b; }
.dist-bar .bar-fill.rose  { background: var(--rose); }
.dist-bar .count {
  color: var(--ink-mute); font-size: 11px; min-width: 30px;
  text-align: right; font-variant-numeric: tabular-nums;
}

/* Performance bar - shows WR + ROI side by side */
.perf-bar {
  display: grid; grid-template-columns: 100px 1fr auto auto;
  gap: 10px; align-items: center;
  font-family: var(--font-body); font-size: 12px; font-weight: 500;
  padding: 4px 0;
}
.perf-bar .label {
  color: var(--ink-soft); font-weight: 600;
}
.perf-bar .label .sub {
  color: var(--ink-mute); font-weight: 500; font-size: 10px;
  margin-left: 4px;
}
.perf-bar .bar-track {
  height: 8px; background: var(--line-soft); border-radius: 4px;
  overflow: hidden;
}
.perf-bar .bar-fill {
  height: 100%; background: var(--emerald); border-radius: 4px;
}
.perf-bar .wr {
  font-variant-numeric: tabular-nums; font-weight: 700;
  color: var(--ink); font-size: 12px; min-width: 48px; text-align: right;
}
.perf-bar .roi {
  font-variant-numeric: tabular-nums; font-weight: 700;
  font-size: 12px; min-width: 56px; text-align: right;
}
.perf-bar .roi.pos { color: var(--emerald-deep); }
.perf-bar .roi.neg { color: var(--rose); }
.perf-bar .roi.neutral { color: var(--ink-mute); }

/* ── Settings tab ─────────────────────────────────────────────────────── */
.settings-card {
  background: var(--panel); border: 1px solid var(--line);
  border-radius: var(--radius-lg); padding: 22px 26px;
  max-width: 640px; margin-bottom: 18px;
}
.settings-card h3 {
  font-family: var(--font-body); font-weight: 700; font-size: 16px;
  margin-bottom: 18px; color: var(--ink); letter-spacing: -0.01em;
}
.setting-row {
  display: flex; align-items: center; justify-content: space-between;
  padding: 14px 0; border-top: 1px solid var(--line-soft);
  gap: 14px;
}
.setting-row > div:first-child { flex: 1; min-width: 0; }
.setting-row:first-of-type { border-top: none; }
.setting-row .lbl {
  font-family: var(--font-body); font-weight: 600; font-size: 13px;
  color: var(--ink); letter-spacing: -0.005em;
}
.setting-row .desc {
  font-family: var(--font-body); font-size: 12px; font-weight: 500;
  color: var(--ink-mute); margin-top: 3px; line-height: 1.45;
}
.setting-row .desc code {
  font-family: var(--font-mono); font-size: 11px;
  background: var(--line-soft); padding: 1px 5px; border-radius: 3px;
  color: var(--ink-soft);
}
.setting-input {
  font-family: var(--font-body); font-size: 13px; font-weight: 500;
  background: var(--panel); border: 1px solid var(--line);
  border-radius: var(--radius-sm); padding: 7px 11px;
  width: 110px; text-align: right; color: var(--ink);
  font-variant-numeric: tabular-nums;
}
.setting-input.wide {
  width: 240px; text-align: left;
}
.setting-input:focus {
  outline: none; border-color: var(--emerald);
  box-shadow: 0 0 0 3px var(--emerald-bg);
}

.btn {
  font-family: var(--font-body); font-weight: 600; font-size: 12px;
  background: var(--panel); color: var(--ink-soft);
  border: 1px solid var(--line); border-radius: var(--radius-sm);
  padding: 7px 14px; cursor: pointer; transition: all 0.15s;
  text-decoration: none; display: inline-block; line-height: 1.2;
  white-space: nowrap;
}
.btn:hover { background: var(--line-soft); color: var(--ink); border-color: #d6d3d1; }
.btn-primary {
  background: var(--ink); color: var(--panel); border-color: var(--ink);
}
.btn-primary:hover { background: var(--ink-soft); color: var(--panel); border-color: var(--ink-soft); }
.btn-danger {
  background: var(--panel); color: var(--rose); border-color: var(--rose-line);
}
.btn-danger:hover { background: var(--rose-bg); color: var(--rose); border-color: var(--rose); }

.state-pill {
  display: inline-block; padding: 4px 11px; border-radius: 999px;
  font-family: var(--font-body); font-size: 10px; font-weight: 700;
  letter-spacing: 0.05em; text-transform: uppercase;
}
.state-pill.state-on  { background: var(--emerald-bg); color: var(--emerald-deep); }
.state-pill.state-off { background: var(--line-soft); color: var(--ink-mute); }
.state-pill.state-err { background: var(--rose-bg); color: var(--rose); }

.sync-log {
  font-family: var(--font-mono); font-size: 10.5px; color: var(--ink-mute);
  background: var(--line-soft); border-radius: var(--radius-sm);
  padding: 10px 14px; margin-top: 14px; min-height: 36px;
  white-space: pre-wrap; max-height: 180px; overflow-y: auto;
}
.sync-log:empty::before {
  content: 'sync log appears here';
  color: var(--ink-faint); font-style: italic;
}

.fetch-status {
  font-family: var(--font-body); font-size: 12px; font-weight: 500;
  color: var(--ink-mute);
}
.fetch-status.ok  { color: var(--emerald-deep); }
.fetch-status.err { color: var(--rose); }

.about-text {
  font-family: var(--font-body); font-size: 13px; font-weight: 500;
  color: var(--ink-soft); line-height: 1.6;
}
.about-text p { margin-bottom: 10px; }
.about-text p:last-child { margin-bottom: 0; }
.about-text strong {
  font-weight: 700; color: var(--ink);
}

/* Settings mobile - stack inputs below labels for narrow screens */
@media (max-width: 720px) {
  .settings-card { padding: 18px 20px; }
  .setting-row {
    flex-direction: column; align-items: stretch; gap: 10px;
    padding: 14px 0;
  }
  .setting-row > div:first-child { width: 100%; }
  .setting-input { width: 100%; box-sizing: border-box; }
  .setting-input.wide { width: 100%; }
  .setting-row .btn { align-self: flex-start; }
}

/* Mobile adjustments - global */
@media (max-width: 720px) {
  .topbar { padding: 12px 0; margin-bottom: 14px; }
  .brand { font-size: 17px; }
  .tabs { overflow-x: auto; -webkit-overflow-scrolling: touch; }
  .tab { padding: 10px 12px; font-size: 11px; flex-shrink: 0; }
  .hero { padding: 14px 16px; }
  .hero-title { font-size: 16px; }
  /* Force 2-column hero stats on mobile so the 4 Today KPIs always fit 2x2,
     not 3+1 on wider phones (Pro Max etc) which leaves an orphan ROI row. */
  .hero-stats { grid-template-columns: repeat(2, 1fr); gap: 12px; }
  .hero-stat .val { font-size: 18px; }
  .hero-stat .lbl { font-size: 9px; }

  /* Race tab */
  .race-table { font-size: 11px; }
  .race-table thead th, .race-table tbody td { padding: 8px 6px; }
  .race-table-wrap { overflow-x: auto; }
  /* Hide low-priority columns on mobile so the essential ones (Tab, Horse,
     Bar, TR$, Fxd, Score) fit without horizontal scroll. The full table is
     still available in the detail panel by tapping the horse name on Today
     tab, or by viewing in landscape mode (table will horizontally scroll). */
  /* Race table mobile column structure (1-based indices after restructure):
     1=Tab 2=Horse 3=Fxd 4=Score 5=Votes
     6=WPR 7=Late 8=Class 9=L600 10=PF AI 11=TR
     12=Bar 13=Style 14=Settles 15=Mid 16=Total
     17=L400 18=Class Δ 19=Distance 20=Going(?)

     On mobile we show columns 1-11 (the primary scan columns) and hide
     everything else (Bar, Style, Settles, Mid, Total, L400, ClassΔ, Dist,
     Going). The hidden columns are accessible by tapping a row to expand
     the detail panel. This keeps the table readable on phones while
     preserving all data on tap. */
  .race-table thead th:nth-child(12), /* Bar */
  .race-table thead th:nth-child(13), /* Style */
  .race-table thead th:nth-child(14), /* Settles */
  .race-table thead th:nth-child(15), /* Mid */
  .race-table thead th:nth-child(16), /* Total */
  .race-table thead th:nth-child(17), /* L400 */
  .race-table thead th:nth-child(18), /* Class Δ */
  .race-table thead th:nth-child(19), /* Distance */
  .race-table thead th:nth-child(20), /* Going */
  .race-table tbody td:nth-child(12),
  .race-table tbody td:nth-child(13),
  .race-table tbody td:nth-child(14),
  .race-table tbody td:nth-child(15),
  .race-table tbody td:nth-child(16),
  .race-table tbody td:nth-child(17),
  .race-table tbody td:nth-child(18),
  .race-table tbody td:nth-child(19),
  .race-table tbody td:nth-child(20) {
    display: none;
  }
  /* Tighter cell padding on mobile - 11 visible columns need compact cells
     to fit phone widths without horizontal scroll */
  .race-table thead th { padding: 6px 4px; font-size: 9px; }
  .race-table tbody td { padding: 6px 4px; font-size: 11px; }
  .race-table .horse-cell { max-width: 110px; overflow: hidden; text-overflow: ellipsis; }
  .meeting-strip { padding: 6px 8px; gap: 4px; }
  .meeting-tile { width: 86px; padding: 5px 8px; }
  .mt-race { font-size: 12px; }

  /* P&L tab */
  .pnl-controls {
    padding: 10px 12px; gap: 10px;
  }
  .pnl-period-btn, .pnl-view-btn {
    padding: 5px 10px; font-size: 11px;
  }
  .pnl-view-toggle { flex-wrap: wrap; }
  .pnl-stats-strip {
    /* 2 cols on phones: 7 KPIs become 3 rows of 2 + 1 orphan. The orphan is
       acceptable because 2-col gives readable stat values; 3-col makes them
       cramped at <380px viewport widths. */
    grid-template-columns: repeat(2, 1fr);
  }
  /* If there are 7 stats (odd), the last one is alone on its row and looks
     unbalanced with empty space next to it. Span it full-width instead. */
  .pnl-stats-strip > .pnl-stat:nth-child(7):last-child {
    grid-column: 1 / -1;
  }
  .pnl-stat { padding: 10px 12px; }
  .pnl-stat .val { font-size: 18px; }
  .pnl-stat .lbl { font-size: 9px; }
  .pnl-stat .sub { font-size: 10px; }
  .pnl-chart-card { padding: 14px 16px; }

  /* Insights */
  .insight-card { padding: 14px 16px; }
  .insight-card h3 { font-size: 13px; }
  .insight-card .desc { font-size: 11px; }
  .perf-bar { grid-template-columns: 80px 1fr auto auto; gap: 8px; }
  .perf-bar .label { font-size: 11px; }
  .perf-bar .label .sub { display: block; margin-left: 0; }
  .dist-bar { grid-template-columns: 70px 1fr auto; gap: 8px; }

  /* Quaddie tab mobile */
  .quaddie-controls { padding: 12px 14px; }
  .quaddie-control-row { gap: 12px; }
  .quaddie-select { min-width: 0; width: 100%; }
  .quaddie-control-group { width: 100%; }
  .quaddie-help { font-size: 11px; }
  .quaddie-race-grid {
    grid-template-columns: repeat(auto-fill, minmax(110px, 1fr));
    gap: 8px;
  }
  .quaddie-race-card { padding: 10px 12px; }
  .quaddie-race-card .qr-num { font-size: 13px; }
  .quaddie-race-card .qr-quals { font-size: 10px; }
  .quaddie-summary {
    padding: 12px 14px;
    grid-template-columns: 1fr 1fr;
    gap: 12px;
  }
  .quaddie-summary .qs-stat .val { font-size: 16px; }
  .quaddie-summary .qs-actions { grid-column: 1 / -1; justify-self: stretch; }
  .quaddie-legs { grid-template-columns: 1fr; gap: 10px; }
  .quaddie-leg-card { padding: 12px 14px; }

  /* First-starter warning sized for mobile */
  .pd-fs-warn { padding: 8px 10px; }
  .pd-fs-warn .text { font-size: 11px; }
  .pd-fs-warn .sub { font-size: 10px; }
}
"""


# ── HTML template ───────────────────────────────────────────────────────────
_HTML_TEMPLATE = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0, viewport-fit=cover">
<title>TopRate — {primary_label}</title>
<style>
@import url('https://fonts.googleapis.com/css2?family=IBM+Plex+Mono:wght@400;500&family=Outfit:wght@300;400;500;600;700;900&display=swap');
{css_tokens}
{css}
</style>
</head>
<body>
<div class="shell">

  <header class="topbar topbar-compact">
    <div class="topbar-right">
      <span class="run-stamp" id="header-run-stamp" title="{run_date}"><span id="header-run-rel">just now</span></span>
      <span class="sync-pill" id="sync-pill" title="Tap to pull latest bets/odds from cloud sync">sync off</span>
      <span class="unit-control" id="unit-display">1u = $100</span>
    </div>
  </header>

  <div class="ntj-ticker" id="ntj-ticker">
    <button class="ntj-toggle" id="ntj-toggle" aria-label="Toggle next-to-jump"><span id="ntj-toggle-icon">▼</span></button>
    <div class="ntj-label">Next to jump</div>
    <div class="ntj-pills" id="ntj-pills"></div>
  </div>

  <nav class="tabs">
    <div class="tab active" data-tab="today">Today</div>
    <div class="tab" data-tab="race">Race</div>
    <div class="tab" data-tab="quaddie">Quaddie</div>
    <div class="tab" data-tab="pnl">P&amp;L</div>
    <div class="tab" data-tab="insights">Tracking</div>
    <div class="tab" data-tab="database">Database</div>
    <div class="tab" data-tab="settings">Settings</div>
  </nav>

  <!-- TODAY -->
  <section class="section active" id="sec-today">
    <div class="hero">
      <div class="hero-stats">
        <div class="hero-stat">
          <div class="lbl">P&amp;L</div>
          <div class="val" id="hs-today-pnl">&mdash;</div>
          <div class="sub" id="hs-today-pnl-units">&mdash;</div>
        </div>
        <div class="hero-stat">
          <div class="lbl">Win rate</div>
          <div class="val" id="hs-today-wr">&mdash;</div>
          <div class="sub" id="hs-today-wr-sub">&mdash;</div>
        </div>
        <div class="hero-stat">
          <div class="lbl">Place rate</div>
          <div class="val" id="hs-today-pr">&mdash;</div>
          <div class="sub" id="hs-today-pr-sub">&mdash;</div>
        </div>
        <div class="hero-stat">
          <div class="lbl">ROI</div>
          <div class="val" id="hs-today-roi">&mdash;</div>
          <div class="sub" id="hs-today-roi-sub">&mdash;</div>
        </div>
      </div>
    </div>

    <!-- Model sub-tabs - switches which model's picks fill the rows below.
         Badge count is filled in by JS on render. Two models currently:
         "main" (production rule, 3 top-1 votes + 5 top-3) and "loose"
         (experimental, 2 top-1 + 4 top-3). Switching also drives the hero
         stats above - WR/ROI/etc reflect only the active model's bets. -->
    <div class="subtabs-row" id="today-subtabs">
      <button class="subtab active" data-model="main">Main<span class="subtab-badge" id="today-subtab-count-main">0</span></button>
      <button class="subtab" data-model="loose">Loose<span class="subtab-badge" id="today-subtab-count-loose">0</span></button>
    </div>

    <div class="race-date-bar" id="today-date-bar">
      <div class="race-date-controls">
        <button class="today-date-quick race-date-quick" data-tdate="yesterday">Yesterday</button>
        <button class="today-date-quick race-date-quick active" data-tdate="today">Today</button>
        <button class="today-date-quick race-date-quick" data-tdate="tomorrow">Tomorrow</button>
        <input type="date" id="today-date-input" class="race-date-input">
      </div>
      <div class="race-date-info" id="today-date-info">&mdash;</div>
    </div>

    <!-- Today filters bar - field size, jockey rating. Filters narrow which
         model picks show up in the row list below. Filtered-out rows dim
         but stay visible/clickable so user can still inspect them. Filters
         persist across reloads via localStorage. -->
    <div class="race-filters-bar">
      <div class="race-filter-group">
        <label for="today-filter-fs">Field</label>
        <select class="race-filter-select" id="today-filter-fs">
          <option value="0">All</option>
          <option value="8">8+</option>
          <option value="10">10+</option>
          <option value="12">12+</option>
        </select>
      </div>
      <div class="race-filter-group">
        <label for="today-filter-jky">Jky rating</label>
        <select class="race-filter-select" id="today-filter-jky">
          <option value="0">All</option>
          <option value="75">75+</option>
          <option value="80">80+</option>
          <option value="85">85+</option>
          <option value="90">90+</option>
        </select>
      </div>
      <button class="race-filter-reset" id="today-filter-reset" type="button">Reset</button>
      <div class="race-filter-summary" id="today-filter-summary"></div>
    </div>

    <div class="picks-scroll" id="picks-scroll">
    <div class="picks-header" id="picks-header">
      <div>Time</div>
      <div>Meeting</div>
      <div>Runner</div>
      <div>Signals</div>
      <div class="th-right">Fxd</div>
      <div class="th-right">Stake</div>
      <div class="th-right">Return</div>
      <div>Result</div>
      <div class="th-right">Odds taken</div>
      <div></div>
    </div>

    <!-- Two-section list: Pending bets above, Resulted below. Both share the
         same .picks-scroll container so column widths stay aligned and a
         single horizontal scroll moves them together. Section heads carry
         their per-section counts and hide-when-empty. -->
    <div class="picks-section-head" id="pending-head" style="display:none;">
      <span class="picks-section-label">Pending</span>
      <span class="picks-section-count" id="pending-count">0</span>
    </div>
    <div class="picks-list" id="picks-list-pending">
      <!-- populated by JS - rows without official/manual results -->
    </div>

    <div class="picks-section-head" id="resulted-head" style="display:none;">
      <span class="picks-section-label">Resulted</span>
      <span class="picks-section-count" id="resulted-count">0</span>
    </div>
    <div class="picks-list" id="picks-list-resulted">
      <!-- populated by JS - rows with official or manual results -->
    </div>
    </div>

  </section>

  <!-- RACE -->
  <section class="section" id="sec-race">
    <!-- Browser view: date picker + meetings grid -->
    <div id="race-browser">
      <div class="race-date-bar">
        <div class="race-date-controls">
          <button class="race-date-quick" data-rdate="yesterday">Yesterday</button>
          <button class="race-date-quick active" data-rdate="today">Today</button>
          <button class="race-date-quick" data-rdate="tomorrow">Tomorrow</button>
          <input type="date" id="race-date-input" class="race-date-input">
        </div>
        <div class="race-date-info" id="race-date-info">—</div>
      </div>

      <div id="race-meetings-list">
        <div class="empty-state">
          <div class="head">Loading meetings…</div>
        </div>
      </div>
    </div>

    <!-- Detail view: shown when a race is selected -->
    <div id="race-detail" style="display:none;">
      <div class="race-back-bar">
        <button class="race-back-btn" id="race-back-btn">← Back to meetings</button>
      </div>
      <div class="meeting-strip" id="rd-meeting-strip"></div>
      <div class="race-detail">
        <div class="race-banner" id="rd-banner" style="display:none;"></div>
        <div class="race-header">
          <div>
            <h2 id="rd-title">—</h2>
            <div class="race-meta-line" id="rd-subtitle">—</div>
          </div>
          <div class="race-header-stats" id="rd-header-stats"></div>
        </div>
        <div class="race-context-bar" id="rd-context-bar"></div>
        <div class="pf-freshness-bar" id="rd-pf-freshness"></div>
        <div class="race-table-wrap" id="rd-runners-table"></div>
        <div class="race-pace-map" id="rd-pace-map"></div>
        <div class="track-conditions-card" id="rd-track-conditions"></div>
        <div class="pf-bias-panel" id="rd-pf-bias" style="display:none;"></div>
      </div>
    </div>
  </section>

  <!-- QUADDIE -->
  <section class="section" id="sec-quaddie">
    <!-- Top: date + threshold controls. Meeting picker is now a grid below
         (was a dropdown - too much friction when the meetings list could fit
         on screen). The Race tab uses a similar meetings-grid layout, so the
         Quaddie tab now mirrors it for consistency. -->
    <div class="quaddie-controls">
      <div class="quaddie-control-row">
        <div class="quaddie-control-group">
          <label class="quaddie-lbl">Date</label>
          <div class="race-date-controls">
            <button class="quaddie-date-quick race-date-quick" data-qdate="yesterday">Yesterday</button>
            <button class="quaddie-date-quick race-date-quick active" data-qdate="today">Today</button>
            <button class="quaddie-date-quick race-date-quick" data-qdate="tomorrow">Tomorrow</button>
            <input type="date" id="quaddie-date-input" class="race-date-input">
          </div>
        </div>
        <div class="quaddie-control-group">
          <label class="quaddie-lbl">Threshold</label>
          <input type="number" id="quaddie-thresh" class="quaddie-thresh-input" min="0" max="1" step="0.05">
          <button class="btn-tiny" id="quaddie-thresh-reset" title="Reset to your default in Settings">↺</button>
        </div>
      </div>
      <div class="quaddie-help">
        Pick a meeting then click 4 races for your quaddie. Race cells show how many horses meet the score threshold,
        plus a ✓ or ✗ flag indicating whether the race meets your bet criteria (prize $50k+ and 8+ runners).
      </div>
    </div>

    <!-- Meetings grid: all meetings on the date, races as cells across.
         Click a meeting row to select it; click race cells to add as legs.
         Layout matches the Race tab so users have one mental model. -->
    <div id="quaddie-meetings-list">
      <div class="empty-state">
        <div class="head">Loading meetings…</div>
      </div>
    </div>

    <!-- Strategy filter summary - shows whether the active meeting meets
         the user's quaddie bet criteria (prize >= $50k AND field >= 8 per
         leg). Populated by renderQuaddie when a meeting is selected. -->
    <div class="quaddie-strategy-banner" id="quaddie-strategy-banner" style="display:none;"></div>

    <!-- Legacy race-grid: still populated by renderQuaddie for the strategy
         banner code path, but hidden visually since the meetings-table above
         already shows every race with the same data. Keeping the rendering
         code intact avoids a riskier rewrite; one day this element can be
         removed entirely. -->
    <div class="quaddie-race-grid" id="quaddie-race-grid" style="display:none;">
      <!-- populated by JS but hidden - meetings-table above is the new picker -->
    </div>

    <!-- Selected legs and combo summary -->
    <div class="quaddie-legs-wrap" id="quaddie-legs-wrap" style="display:none;">
      <div class="quaddie-summary" id="quaddie-summary">
        <!-- populated by JS: combo count, hit rate estimate, $ at unit -->
      </div>
      <div class="quaddie-legs" id="quaddie-legs">
        <!-- populated by JS: 4 leg cards with qualifying horses each -->
      </div>
    </div>

    <!-- Empty state -->
    <div class="quaddie-empty" id="quaddie-empty">
      Pick a meeting above to get started. Then click race cards to add them as legs.
    </div>
  </section>

  <!-- PNL -->
  <section class="section" id="sec-pnl">
    <!-- Model sub-tabs - filters all P&L stats, charts, and settled bet
         rows to the selected model. Counts updated on render to show
         settled bets per model in current period. Switching reloads
         everything below. -->
    <div class="subtabs-row" id="pnl-subtabs">
      <button class="subtab active" data-model="main">Main<span class="subtab-badge" id="pnl-subtab-count-main">0</span></button>
      <button class="subtab" data-model="loose">Loose<span class="subtab-badge" id="pnl-subtab-count-loose">0</span></button>
    </div>

    <!-- Top control bar: period selector + view mode toggle -->
    <div class="pnl-controls">
      <div class="pnl-period-group" role="group" aria-label="Time period">
        <button class="pnl-period-btn" data-period="7d">7d</button>
        <button class="pnl-period-btn" data-period="30d">30d</button>
        <button class="pnl-period-btn active" data-period="all">All time</button>
        <button class="pnl-period-btn" data-period="custom">Custom</button>
      </div>
      <div class="pnl-period-custom" id="pnl-custom-range" style="display:none;">
        <input type="date" id="pnl-date-from" />
        <span style="color:var(--ink-mute);">→</span>
        <input type="date" id="pnl-date-to" />
      </div>
      <div class="pnl-view-toggle" role="group" aria-label="View mode">
        <span class="pnl-view-label">View:</span>
        <button class="pnl-view-btn active" data-view="actual"
                title="Actual: P&L based on bets you actually placed and the odds you took. Reflects your real bankroll change.">Actual</button>
        <button class="pnl-view-btn" data-view="theoretical"
                title="Theoretical: P&L if you had bet 1u flat at SP on every model pick. Use this to see how the model performed independent of your bet sizing or odds-shopping.">Theoretical</button>
      </div>
    </div>

    <!-- Top stats strip -->
    <div class="pnl-stats-strip" id="pnl-stats-strip"></div>

    <!-- Two charts side by side -->
    <div class="pnl-charts-grid">
      <div class="pnl-chart-card">
        <h3>Cumulative units</h3>
        <svg class="pnl-chart-svg" id="pnl-chart-cum" viewBox="0 0 600 200" preserveAspectRatio="none"></svg>
        <div class="pnl-chart-legend">
          <div><span class="legend-line solid"></span>Actual</div>
          <div><span class="legend-line dashed"></span>Expected (model)</div>
        </div>
      </div>
      <div class="pnl-chart-card">
        <h3>Rolling win rate <span class="hint">(last 20 bets)</span></h3>
        <svg class="pnl-chart-svg" id="pnl-chart-wr" viewBox="0 0 600 200" preserveAspectRatio="none"></svg>
        <div class="pnl-chart-legend">
          <div><span class="legend-line solid"></span>Rolling WR</div>
          <div><span class="legend-line dashed mute"></span>Expected WR</div>
        </div>
      </div>
    </div>

    <!-- Settled bets section -->
    <div class="bet-history">
      <div class="bh-header">
        <h3>Settled bets &middot; <span id="bh-count">0</span></h3>
        <div class="bh-controls">
          <label class="bh-filter-toggle">
            <input type="checkbox" id="bh-filter-only-bet" />
            <span>Only bets I placed</span>
          </label>
          <button class="bh-export-btn" id="bh-export">Export CSV</button>
        </div>
      </div>
      <div class="picks-scroll">
      <div class="picks-header" id="bh-picks-header">
        <div>Date</div>
        <div>Meeting</div>
        <div>Runner</div>
        <div>Signals</div>
        <div class="th-right">Fxd</div>
        <div class="th-right">Stake</div>
        <div class="th-right">Return</div>
        <div>Result</div>
        <div class="th-right">Odds taken</div>
        <div></div>
      </div>
      <div class="bh-list picks-list" id="bh-list">
        <!-- populated by JS - rich cards like Today tab -->
      </div>
      </div>
    </div>
  </section>

  <!-- INSIGHTS -->
  <section class="section" id="sec-insights">
    <!-- Period selector applies to all tracking sections below -->
    <div class="insights-controls">
      <div class="ic-period-toggle">
        <button class="ic-period-btn" data-iperiod="7">Last 7 days</button>
        <button class="ic-period-btn active" data-iperiod="30">Last 30 days</button>
        <button class="ic-period-btn" data-iperiod="90">Last 90 days</button>
      </div>
      <!-- Mode toggle: 3-way - Actual (bets you placed) / Theoretical (all
           V3 picks regardless of placement) / All races (every horse in every
           resulted race, no filter). Naming matches P&L tab's Actual vs
           Theoretical convention. Applies to the 6 pick-based sections
           (threshold, dow, venue, distance, going, field size). The other
           sections (heatmap, correlation, winners, placegetters) inherently
           operate on all resulted races and are unaffected by this toggle. -->
      <div class="ic-mode-toggle">
        <button class="ic-mode-btn" data-imode="actual" title="Bets you actually placed (bet toggle = on in P&L). What you actually wagered.">Actual</button>
        <button class="ic-mode-btn active" data-imode="theoretical" title="All V3 model picks regardless of whether you bet them. The model's full output.">Theoretical</button>
        <button class="ic-mode-btn" data-imode="all" title="Every horse in every resulted race, no model filtering. Raw cumulative-score predictive power.">All races</button>
      </div>
      <!-- Model toggle - filters the 6 pick-based sections by which model
           produced the pick. Defaults to "Main" so the user sees production
           model performance first. "Both" unions Main and Loose picks
           (note: duplicates if both models picked the same horse). Toggle
           is hidden when mode = 'all' (model filter is meaningless when
           we're analysing every runner regardless of pick). -->
      <div class="ic-model-toggle" id="ic-model-toggle">
        <button class="ic-model-btn active" data-imodel="main" title="Production main model picks only (3 of 6 top-1 votes, 5 of 6 top-3 votes).">Main</button>
        <button class="ic-model-btn" data-imodel="loose" title="Experimental loose model picks only (2 of 6 top-1, 4 of 6 top-3).">Loose</button>
        <button class="ic-model-btn" data-imodel="both" title="Union of Main and Loose picks. A horse picked by both models counts in each section's totals separately.">Both</button>
      </div>
      <div class="ic-info" id="insights-summary"></div>
    </div>

    <!-- 1. Signal heatmap - which signals are most predictive of winners -->
    <div class="insight-card insight-wide">
      <h3>Signal heatmap</h3>
      <div class="desc">
        Win rate of horses ranked top-1, top-3, and top-5 in each signal across all
        resulted races in the period. Darker green = stronger predictive power. Use
        this to spot which signals are working now and which have decayed.
      </div>
      <div id="signal-heatmap"></div>
      <!-- Period comparison: top-1 WR across 7/30/90 day windows for the
           strongest signals in the current view. Helps spot decay vs improvement. -->
      <div id="heatmap-period-cmp" class="hm-period-cmp"></div>
    </div>

    <!-- 3. Signal correlation matrix - shows agreement between pairs of signals.
         High agreement = signal redundancy (one of them adds little info beyond
         the other). Low agreement = signals are picking different horses, so
         a voting model genuinely combines them. -->
    <div class="insight-card insight-wide">
      <h3>Signal correlation</h3>
      <div class="desc">
        How often each pair of signals agrees on the top horse in a race.
        High % = signals are redundant. Low % = signals capture different
        information and combine well in the voting model.
      </div>
      <div id="signal-correlation"></div>
    </div>

    <!-- 4. Score threshold performance curve - what threshold should you bet at?
         Shows pick count, WR%, ROI% at each threshold step so the sweet spot is
         visible. The single most actionable analytic on this tab. -->
    <div class="insight-card insight-wide">
      <h3>Score threshold performance</h3>
      <div class="desc">
        Performance at each Score threshold step. Higher threshold = fewer picks
        but stronger conviction. Use this to set your stake threshold in Settings
        based on actual live data, not assumption.
      </div>
      <div id="threshold-curve"></div>
    </div>

    <!-- 5. Day-of-week breakdown - some days have more meetings/quality (esp Sat).
         Useful to confirm the model is performing across the week, not just one day. -->
    <div class="insight-card insight-wide">
      <h3>Day of week</h3>
      <div class="desc">
        Pick count, win rate, and ROI by weekday. Saturday is typically the heaviest
        day; check if performance is concentrated there or spread evenly.
      </div>
      <div id="dow-breakdown"></div>
    </div>

    <!-- 6. Venue performance - top 10 venues by pick volume. Some tracks
         suit the model better than others. -->
    <div class="insight-card insight-wide">
      <h3>Venue performance</h3>
      <div class="desc">
        Top venues by pick count in the period. Sortable. Small samples are noisy -
        venues with under 5 picks are de-emphasised but still shown.
      </div>
      <div id="venue-performance"></div>
    </div>

    <!-- 7. Distance bracket - WR/ROI by race distance band -->
    <div class="insight-card insight-wide">
      <h3>Distance bracket</h3>
      <div class="desc">
        Performance by race distance. Tells you whether the model handles sprints,
        miles, and staying races equally well.
      </div>
      <div id="distance-breakdown"></div>
    </div>

    <!-- 8. Going breakdown - track condition impact -->
    <div class="insight-card insight-wide">
      <h3>Track condition</h3>
      <div class="desc">
        Performance grouped by going (Firm/Good/Soft/Heavy). Wet-track racing
        is structurally different and signals may behave differently.
      </div>
      <div id="going-breakdown"></div>
    </div>

    <!-- 9. Field size - small fields are easier to predict; large fields are noisier -->
    <div class="insight-card insight-wide">
      <h3>Field size</h3>
      <div class="desc">
        Performance by number of runners. Smaller fields concentrate the contest;
        bigger fields dilute the signal edge.
      </div>
      <div id="fieldsize-breakdown"></div>
    </div>

    <!-- 9. Winners table (penultimate, above Placegetters): one row per
         resulted race, full signal ranks for the winner. Heavy table - sits
         near the bottom so the lighter analytic cards scroll first. -->
    <div class="insight-card insight-wide">
      <h3>Winners — signal ranks</h3>
      <div class="desc">
        Every resulted race in the period. Each row shows the winner's rank for
        all 12 signals (Score first, then the 11 individual signals). Green = top 3,
        yellow = top 5, grey = beyond. Race link opens the Race tab. Sort by clicking
        column headers.
      </div>
      <div id="tracking-winners"></div>
    </div>

    <!-- 10. Placegetters drill-down - 1st/2nd/3rd with full signal context -->
    <div class="insight-card insight-wide">
      <h3>Placegetters detail</h3>
      <div class="desc">
        First, second, and third placegetters per race with all signal ranks.
        Use to spot patterns where the model lost a photo finish to a similar
        runner. Click a race to open it in the Race tab.
      </div>
      <div id="tracking-placegetters"></div>
    </div>
  </section>

  <!-- DATABASE -->
  <!-- Runner database: flat queryable view over every runner in every
       resulted race in the last 30 days (source: RACES, pre-injected).
       Filter bar at top + computed stats strip + scrollable table.
       Designed for ad-hoc queries like "find all races where the model's
       pick had all 6 signals at rank 1" or "what's my hypothetical ROI
       on Bm65 races at Cranbourne if I bet to return 4u?". -->
  <section class="section" id="sec-database">
    <div class="db-controls">
      <button class="db-controls-toggle" id="db-controls-toggle" type="button">
        <span class="db-controls-toggle-label">Filters</span>
        <span class="db-controls-toggle-chev">▾</span>
      </button>
      <div class="db-filters" id="db-filters">

        <div class="db-filter-row">
          <div class="db-filter-group">
            <label for="db-date-from">Date from</label>
            <input type="date" id="db-date-from" class="db-input">
          </div>
          <div class="db-filter-group">
            <label for="db-date-to">Date to</label>
            <input type="date" id="db-date-to" class="db-input">
          </div>
          <div class="db-filter-group">
            <label for="db-venue">Venue</label>
            <input type="text" id="db-venue" class="db-input" placeholder="contains text…">
          </div>
          <div class="db-filter-group">
            <label for="db-horse">Horse</label>
            <input type="text" id="db-horse" class="db-input" placeholder="contains text…">
          </div>
        </div>

        <div class="db-filter-row">
          <div class="db-filter-group">
            <label for="db-min-fs">Field size ≥</label>
            <select class="db-input" id="db-min-fs">
              <option value="0">Any</option>
              <option value="6">6+</option>
              <option value="8">8+</option>
              <option value="10">10+</option>
              <option value="12">12+</option>
            </select>
          </div>
          <div class="db-filter-group">
            <label for="db-min-prize">Prize ≥</label>
            <select class="db-input" id="db-min-prize">
              <option value="0">Any</option>
              <option value="20000">$20k</option>
              <option value="50000">$50k</option>
              <option value="100000">$100k</option>
              <option value="250000">$250k</option>
            </select>
          </div>
          <div class="db-filter-group">
            <label for="db-going">Going</label>
            <select class="db-input" id="db-going">
              <option value="">Any</option>
              <option value="Firm">Firm</option>
              <option value="Good">Good</option>
              <option value="Soft">Soft</option>
              <option value="Heavy">Heavy</option>
              <option value="Synthetic">Synthetic</option>
            </select>
          </div>
          <div class="db-filter-group">
            <label for="db-min-dist">Distance ≥</label>
            <input type="number" id="db-min-dist" class="db-input db-input-narrow" placeholder="m" min="0" step="100">
          </div>
          <div class="db-filter-group">
            <label for="db-max-dist">Distance ≤</label>
            <input type="number" id="db-max-dist" class="db-input db-input-narrow" placeholder="m" min="0" step="100">
          </div>
        </div>

        <div class="db-filter-row">
          <div class="db-filter-group">
            <label for="db-min-score">Score ≥</label>
            <input type="number" id="db-min-score" class="db-input db-input-narrow" placeholder="0.50" min="0" max="1" step="0.05">
          </div>
          <div class="db-filter-group">
            <label for="db-max-score">Score ≤</label>
            <input type="number" id="db-max-score" class="db-input db-input-narrow" placeholder="1.00" min="0" max="1" step="0.05">
          </div>
          <div class="db-filter-group">
            <label for="db-min-sp" title="Starting price filter. Only applies to resulted rows (unresulted rows have no SP and will be hidden when this filter is active).">SP ≥</label>
            <input type="number" id="db-min-sp" class="db-input db-input-narrow" placeholder="$3" min="0" step="0.5">
          </div>
          <div class="db-filter-group">
            <label for="db-min-jky">Jky rating ≥</label>
            <select class="db-input" id="db-min-jky">
              <option value="0">Any</option>
              <option value="75">75+</option>
              <option value="80">80+</option>
              <option value="85">85+</option>
              <option value="90">90+</option>
            </select>
          </div>
          <div class="db-filter-group">
            <label for="db-model">Model pick</label>
            <select class="db-input" id="db-model">
              <option value="any">Any</option>
              <option value="main">Main</option>
              <option value="loose">Loose</option>
              <option value="any-pick">Any pick</option>
              <option value="none">Not a pick</option>
            </select>
          </div>
          <div class="db-filter-group">
            <label for="db-result">Result</label>
            <select class="db-input" id="db-result">
              <option value="any">Any</option>
              <option value="won">Won</option>
              <option value="placed">Placed (top 3)</option>
              <option value="lost">Lost (out of 3)</option>
              <option value="resulted">Any resulted</option>
              <option value="unresulted">Unresulted</option>
            </select>
          </div>
        </div>

        <!-- Signal rank filters - per-signal "top 1" / "top 3" / "any" -->
        <div class="db-filter-row db-filter-signals">
          <div class="db-filter-group-label">Signals:</div>
          <div class="db-signal-filter">
            <label>WPR</label>
            <select class="db-input db-input-tiny" data-sigfilter="wpr">
              <option value="any">Any</option>
              <option value="1">≤ 1</option>
              <option value="3">≤ 3</option>
            </select>
          </div>
          <div class="db-signal-filter">
            <label>Late</label>
            <select class="db-input db-input-tiny" data-sigfilter="late">
              <option value="any">Any</option>
              <option value="1">≤ 1</option>
              <option value="3">≤ 3</option>
            </select>
          </div>
          <div class="db-signal-filter">
            <label>Class</label>
            <select class="db-input db-input-tiny" data-sigfilter="wcR">
              <option value="any">Any</option>
              <option value="1">≤ 1</option>
              <option value="3">≤ 3</option>
            </select>
          </div>
          <div class="db-signal-filter">
            <label>L600</label>
            <select class="db-input db-input-tiny" data-sigfilter="l600R">
              <option value="any">Any</option>
              <option value="1">≤ 1</option>
              <option value="3">≤ 3</option>
            </select>
          </div>
          <div class="db-signal-filter">
            <label>PF AI</label>
            <select class="db-input db-input-tiny" data-sigfilter="pfaiR">
              <option value="any">Any</option>
              <option value="1">≤ 1</option>
              <option value="3">≤ 3</option>
            </select>
          </div>
          <div class="db-signal-filter">
            <label>TR</label>
            <select class="db-input db-input-tiny" data-sigfilter="tr">
              <option value="any">Any</option>
              <option value="1">≤ 1</option>
              <option value="3">≤ 3</option>
            </select>
          </div>
          <button class="db-quick-btn" id="db-all-rank-1" type="button" title="Quick filter: set all 6 signals to ≤ 1">All #1</button>
          <button class="db-quick-btn" id="db-all-top3" type="button" title="Quick filter: set all 6 signals to ≤ 3">All top-3</button>
        </div>

        <div class="db-filter-row db-filter-actions">
          <button class="db-reset" id="db-reset" type="button">Reset all</button>
          <div class="db-filter-summary" id="db-filter-summary">—</div>
        </div>

      </div>
    </div>

    <!-- Stats strip - computed metrics over CURRENTLY VISIBLE rows. The
         "bet to return 4u" stake sizing is the user's preferred analysis:
         for each row, required stake = 4 / (price-1); over resulted rows,
         total return = (4 * wins); ROI = (return - stake) / stake. -->
    <div class="db-stats-strip" id="db-stats-strip"></div>

    <!-- Table -->
    <div class="db-table-wrap" id="db-table-wrap">
      <div class="empty-state"><div class="head">Loading database…</div></div>
    </div>

  </section>

  <!-- SETTINGS -->
  <section class="section" id="sec-settings">

    <!-- Stake preferences (most-frequently-changed first) -->
    <div class="settings-card">
      <h3>Stake preferences</h3>
      <div class="setting-row" style="border-top:none;">
        <div>
          <div class="lbl">Unit size</div>
          <div class="desc">Dollar value of 1 unit. Used to convert stakes/PnL between units and dollars.</div>
        </div>
        <input type="number" class="setting-input" id="setting-unit" value="100" min="1" step="1">
      </div>
      <div class="setting-row">
        <div>
          <div class="lbl">Bet to return</div>
          <div class="desc">Target gross return per bet in units (stake + profit on a winner). Stake = target / price.</div>
        </div>
        <input type="number" class="setting-input" id="setting-target" value="4" min="0.5" step="0.5">
      </div>
      <div class="setting-row">
        <div>
          <div class="lbl">Min stake</div>
          <div class="desc">Minimum stake floor in units (caps very long shots).</div>
        </div>
        <input type="number" class="setting-input" id="setting-min" value="0.25" min="0" step="0.05">
      </div>
      <div class="setting-row">
        <div>
          <div class="lbl">Max stake</div>
          <div class="desc">Maximum stake ceiling in units (caps short prices).</div>
        </div>
        <input type="number" class="setting-input" id="setting-max" value="4" min="0.5" step="0.5">
      </div>
    </div>

    <!-- Score threshold (used by Quaddie tab + race tab highlighting) -->
    <div class="settings-card">
      <h3>Cumulative score threshold</h3>
      <div class="setting-row" style="border-top:none;">
        <div>
          <div class="lbl">Threshold</div>
          <div class="desc">
            Minimum cumulative score for a horse to qualify on the Quaddie tab.
            Higher = stricter, fewer picks. The score is a logistic-regression
            blend of TR rating, WPR, Late speed, PF AI, PF Class, and PF L600
            signals (Path C). Path C scores are sigmoid-bounded in [0, 1] and
            tend to cluster near the middle of the range; a threshold around
            0.40-0.50 matches what 0.70 used to mean for the legacy formula.
            The main betting model rule does not use this threshold.
          </div>
        </div>
        <input type="number" class="setting-input" id="setting-score-thresh" value="0.40" min="0" max="1" step="0.05">
      </div>
    </div>

    <!-- Fetch / data source -->
    <div class="settings-card">
      <h3>Data fetch</h3>
      <div class="setting-row" style="border-top:none;">
        <div>
          <div class="lbl">Last refreshed</div>
          <div class="desc" id="last-fetched-desc">
            <span id="last-fetched-rel">just now</span>
            &middot; <span id="last-fetched-abs">{run_date}</span>
          </div>
        </div>
        <div></div>
      </div>
      <div class="setting-row">
        <div>
          <div class="lbl">Re-fetch today</div>
          <div class="desc">
            Trigger toprate_daily.py via GitHub Actions for today's date.
            Refresh this page after about 2 minutes to see new data.
          </div>
        </div>
        <button class="btn btn-primary" id="btn-refetch-today">Refetch today</button>
      </div>
      <div class="setting-row">
        <div>
          <div class="lbl">Fetch a specific date</div>
          <div class="desc">
            Pick a date and trigger toprate_daily.py to fetch (or backfill results for) that day.
            Useful for grabbing past meetings that got missed or updating results that arrived late.
          </div>
        </div>
        <div style="display:flex;gap:8px;align-items:center;">
          <input type="date" class="setting-input" id="fetch-date-input" style="width:140px;">
          <button class="btn btn-primary" id="btn-fetch-date">Fetch date</button>
        </div>
      </div>
      <div class="setting-row">
        <div>
          <div class="lbl">GitHub repo</div>
          <div class="desc">Format: <code>owner/name</code> &middot; case sensitive. Used to dispatch workflows.</div>
        </div>
        <input type="text" class="setting-input wide" id="setting-repo" placeholder="owner/name" autocomplete="off">
      </div>
      <div class="setting-row" style="border-top:none;">
        <div></div>
        <div style="display:flex;gap:10px;align-items:center;">
          <a id="open-actions-link" class="btn" target="_blank" rel="noopener">Open Actions ↗</a>
          <span id="fetch-status" class="fetch-status"></span>
        </div>
      </div>
    </div>

    <!-- Cross-device sync -->
    <div class="settings-card">
      <h3>Sync across devices</h3>
      <div class="setting-row" style="border-top:none;">
        <div>
          <div class="lbl">Sync status</div>
          <div class="desc" id="sync-status">Not configured. Add a GitHub token and Gist ID below to sync results and settings between iPhone and computer.</div>
        </div>
        <span id="sync-state-pill" class="state-pill state-off">off</span>
      </div>
      <div class="setting-row">
        <div>
          <div class="lbl">GitHub Personal Access Token</div>
          <div class="desc">Classic PAT with the <code>gist</code> scope (for sync) and the <code>workflow</code> scope (for the fetch buttons above). Stored in localStorage on this device only.</div>
        </div>
        <input type="password" class="setting-input wide" id="setting-pat" placeholder="ghp_…" autocomplete="off">
      </div>
      <div class="setting-row">
        <div>
          <div class="lbl">Gist ID</div>
          <div class="desc">The ID from your private Gist URL (the bit after /username/). Use the same ID on every device.</div>
        </div>
        <input type="text" class="setting-input wide" id="setting-gist" placeholder="abc123…" autocomplete="off">
      </div>
      <div class="setting-row" style="display:flex;gap:10px;justify-content:flex-end;border-top:none;flex-wrap:wrap;">
        <button class="btn" id="btn-sync-create">Create new Gist</button>
        <button class="btn" id="btn-sync-test">Test sync</button>
        <button class="btn btn-primary" id="btn-sync-pull">Pull from Gist</button>
        <button class="btn btn-primary" id="btn-sync-push">Push to Gist</button>
      </div>
      <div id="sync-log" class="sync-log"></div>
    </div>

    <!-- Bet log admin -->
    <div class="settings-card">
      <h3>Bet log management</h3>
      <div class="setting-row" style="border-top:none;">
        <div>
          <div class="lbl">Storage usage</div>
          <div class="desc" id="storage-usage">Calculating ...</div>
        </div>
        <span id="storage-pill" class="state-pill state-off">—</span>
      </div>
      <div class="setting-row">
        <div>
          <div class="lbl">Export bet log</div>
          <div class="desc">Download a JSON backup of all your bet placements, odds taken, and comments. Independent from CSV export.</div>
        </div>
        <button class="btn" id="btn-export-betlog">Export JSON</button>
      </div>
      <div class="setting-row">
        <div>
          <div class="lbl">Import bet log</div>
          <div class="desc">Restore from a previously exported JSON file. Existing entries with the same run_id will be overwritten.</div>
        </div>
        <div style="display:flex;gap:8px;align-items:center;">
          <input type="file" id="import-betlog-input" accept=".json" style="display:none;">
          <button class="btn" id="btn-import-betlog">Choose file ...</button>
        </div>
      </div>
      <div class="setting-row">
        <div>
          <div class="lbl">Reset bet log</div>
          <div class="desc">Clear all recorded bet placements, odds taken, and comments. This cannot be undone (export first to back up).</div>
        </div>
        <button class="btn btn-danger" id="btn-reset-betlog">Reset bet log</button>
      </div>
      <div class="setting-row" style="border-top:none;">
        <div></div>
        <span id="betlog-status" class="fetch-status"></span>
      </div>
    </div>

    <!-- About -->
    <div class="settings-card">
      <h3>About</h3>
      <div class="about-text">
        <p><strong>Primary model:</strong> {primary_label} &mdash; {primary_desc}</p>
        <p><strong>Walk-forward verified:</strong> Train ROI +24%, Test ROI +37% on Apr 9 - May 7 2026 sample.</p>
        <p><strong>Expected:</strong> {primary_wr}% strike rate, {primary_roi_sp}% ROI@SP, {primary_roi_top}% ROI@Top.</p>
        <p><strong>Pick volume:</strong> ~{primary_per_day}/day average.</p>
      </div>
    </div>
  </section>

</div>

<script>
{js_data}
{js_app}
</script>
</body>
</html>
"""


# ── JavaScript app ──────────────────────────────────────────────────────────
_JS_APP = r"""
// ── Settings state ──────────────────────────────────────────────────────────
const STORAGE_KEY = 'toprate_v3_settings';
const defaultSettings = {
  unitDollar: 100,
  targetReturn: 4,
  minStake: 0.25,
  maxStake: 4,
  // Score threshold for the cumulative-score-based selection (used by
  // Quaddie tab and threshold highlighting on Race/Today).
  // Path C (LogReg) scores are sigmoid-bounded in [0, 1] and tend to cluster
  // near the middle (rarely above 0.70). 0.50 is the value chosen after
  // backtesting quaddie strategies on metro Saturdays with 8+ runners -
  // it had the lowest synthetic loss across 0.50/0.55/0.60 (best hit rate
  // per combo cost) and the field-size+prize-money filter on top removes
  // the worst of the small-field longshot drag.
  //
  // Updated 2026-05-15 from 0.50 -> 0.55 after the quaddie score backtest
  // (Apr 9 - May 7 dataset). Paired with the TR weight drop 2.97 -> 2.5
  // in toprate_daily.py, this combination is the only config in the
  // backtest that delivered positive synthetic yield (+4.3% on 134
  // windows). 0.50 + dampened TR collapses qualifier sets; 0.55 keeps
  // them tight enough to be profitable. See quaddie_score_backtest.py.
  scoreThreshold: 0.55,
  // Sync settings (configured per-device)
  syncEnabled: false,
  syncGistId: '',
  syncToken: '',
  // GitHub Actions trigger (configured once, same on all devices)
  ghOwner: '',
  ghRepo: '',
  ghWorkflow: 'daily.yml',
};
let settings = Object.assign({}, defaultSettings);
try {
  const raw = localStorage.getItem(STORAGE_KEY);
  if (raw) settings = Object.assign({}, defaultSettings, JSON.parse(raw));
} catch(e) {}

// Migration: Path C ships 2026-05-10 with new score scale. Users with the
// old 0.70 default would see zero qualifying horses on Quaddie tab since
// sigmoid scores rarely exceed 0.70. Auto-migrate exactly the old default
// (we don't touch user-customised values - if they set 0.65 or 0.85 we leave
// it alone since that signals deliberate choice).
if (settings.scoreThreshold === 0.70) {
  settings.scoreThreshold = 0.55;
  try { localStorage.setItem(STORAGE_KEY, JSON.stringify(settings)); } catch(e) {}
}
// Second migration: bump 0.40 default to 0.55 after quaddie backtest analysis.
if (settings.scoreThreshold === 0.40) {
  settings.scoreThreshold = 0.55;
  try { localStorage.setItem(STORAGE_KEY, JSON.stringify(settings)); } catch(e) {}
}
// Third migration: bump 0.50 default to 0.55 after second quaddie backtest
// (2026-05-15). Paired with the TR weight drop in toprate_daily.py - 0.50
// with the new dampened TR weights produces collapsed qualifier sets.
// As before, only the EXACT prior default 0.50 is touched. Users who
// customised to e.g. 0.52 or 0.48 stay where they put it.
if (settings.scoreThreshold === 0.50) {
  settings.scoreThreshold = 0.55;
  try { localStorage.setItem(STORAGE_KEY, JSON.stringify(settings)); } catch(e) {}
}

function saveSettings() {
  try { localStorage.setItem(STORAGE_KEY, JSON.stringify(settings)); } catch(e) {}
  document.getElementById('unit-display').textContent = '1u = $' + settings.unitDollar;
  // Re-render anything that uses settings
  renderToday();
  renderPnL();
  renderInsights();
}

// ── Model sub-tab state ─────────────────────────────────────────────────
// Each section that has model sub-tabs (Today, P&L) tracks which model is
// active independently. So you can browse Main picks on Today while
// reviewing Loose settled bets on P&L. Persisted across reloads.
const MODEL_TAB_KEY = 'toprate_v3_active_model';
let activeModels = { today: 'main', pnl: 'main' };
try {
  const stored = localStorage.getItem(MODEL_TAB_KEY);
  if (stored) {
    const parsed = JSON.parse(stored);
    if (parsed && typeof parsed === 'object') {
      activeModels = Object.assign(activeModels, parsed);
    }
  }
} catch(e) {}

function saveActiveModels() {
  try { localStorage.setItem(MODEL_TAB_KEY, JSON.stringify(activeModels)); } catch(e) {}
}

function setActiveModel(section, modelKey) {
  if (activeModels[section] === modelKey) return;
  activeModels[section] = modelKey;
  saveActiveModels();
  // Update UI - flip .active class on the sub-tab buttons
  const row = document.getElementById(section + '-subtabs');
  if (row) {
    row.querySelectorAll('.subtab').forEach(b => {
      b.classList.toggle('active', b.getAttribute('data-model') === modelKey);
    });
  }
  // Re-render the section
  if (section === 'today') renderToday();
  else if (section === 'pnl') renderPnL();
}

// Wire sub-tab clicks. Delegation pattern in case the DOM is regenerated.
['today', 'pnl'].forEach(section => {
  const row = document.getElementById(section + '-subtabs');
  if (!row) return;
  row.addEventListener('click', e => {
    const btn = e.target.closest('.subtab');
    if (!btn) return;
    const model = btn.getAttribute('data-model');
    if (model) setActiveModel(section, model);
  });
  // Initial visual state - restore active class from saved state
  row.querySelectorAll('.subtab').forEach(b => {
    b.classList.toggle('active', b.getAttribute('data-model') === activeModels[section]);
  });
});

['setting-unit','setting-target','setting-min','setting-max','setting-score-thresh'].forEach(id => {
  const el = document.getElementById(id);
  if (!el) return;
  el.addEventListener('change', () => {
    const v = parseFloat(el.value);
    if (isNaN(v)) return;
    if (id === 'setting-unit') settings.unitDollar = v;
    if (id === 'setting-target') settings.targetReturn = v;
    if (id === 'setting-min') settings.minStake = v;
    if (id === 'setting-max') settings.maxStake = v;
    if (id === 'setting-score-thresh') {
      // Clamp to [0, 1] just in case
      settings.scoreThreshold = Math.max(0, Math.min(1, v));
      // Re-render Quaddie tab if open
      if (typeof renderQuaddie === 'function') renderQuaddie();
    }
    saveSettings();
  });
});
// Apply initial values
document.getElementById('setting-unit').value = settings.unitDollar;
document.getElementById('setting-target').value = settings.targetReturn;
document.getElementById('setting-min').value = settings.minStake;
document.getElementById('setting-max').value = settings.maxStake;
document.getElementById('setting-score-thresh').value = settings.scoreThreshold;
document.getElementById('unit-display').textContent = '1u = $' + settings.unitDollar;

// ── Stake calculation ──────────────────────────────────────────────────────
// "Bet to return Nu" means: stake sized so the gross return (stake * price)
// equals Nu. Profit on a winner = N - stake.
// When the user has entered an actual oddsTaken value, they have already bet,
// so the maxStake safety cap is removed. We still respect minStake.
function calcStake(price, opts) {
  if (!price || price <= 1) return null;
  const capExempt = opts && opts.capExempt;
  const raw = settings.targetReturn / price;
  const upper = capExempt ? Infinity : settings.maxStake;
  const clamped = Math.min(upper, Math.max(settings.minStake, raw));
  return Math.round(clamped * 100) / 100;
}
function fmtUnits(u) { return u == null ? '—' : u.toFixed(2) + 'u'; }
function fmtDollar(u) { return u == null ? '—' : '$' + (u * settings.unitDollar).toFixed(0); }
function fmtPct(v, signed) {
  if (v == null || isNaN(v)) return '—';
  const s = (v * 100).toFixed(1);
  return (signed && v >= 0 ? '+' : '') + s + '%';
}

// ── Tabs ────────────────────────────────────────────────────────────────────
document.querySelectorAll('.tab').forEach(t => {
  t.addEventListener('click', () => {
    document.querySelectorAll('.tab').forEach(x => x.classList.remove('active'));
    document.querySelectorAll('.section').forEach(x => x.classList.remove('active'));
    t.classList.add('active');
    document.getElementById('sec-' + t.dataset.tab).classList.add('active');
    // Tab-specific render hooks
    if (t.dataset.tab === 'quaddie' && typeof renderQuaddie === 'function') {
      renderQuaddie();
    }
  });
});

// ── Helpers ─────────────────────────────────────────────────────────────────
function fmtTime(iso) {
  if (!iso) return '';
  try {
    const d = new Date(iso);
    return d.toLocaleTimeString([], { hour: '2-digit', minute: '2-digit', hour12: false });
  } catch(e) { return ''; }
}
function fmtDate(d) {
  if (!d) return '';
  return d.replace(/^\\d{4}-/, '');
}
function escapeHtml(s) {
  if (s == null) return '';
  return String(s).replace(/[&<>"']/g, c =>
    ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
}

// ── Abandoned meeting / race tracking ───────────────────────────────────────
// User-managed: PF and TR don't surface abandonment until results come in
// (often hours after the abandoned races would have run), so picks for
// abandoned races stay visible as "pending" until the user manually marks
// them. Two granularities:
//   abandonedMeetings: keyed by (date|venue) - covers entire cards
//   abandonedRaces:    keyed by race_id      - covers single-race edge cases
// Helpers below check BOTH (race-level OR meeting-level returns abandoned).
// Marking a meeting and then unmarking a specific race within it is not
// supported - meeting toggle dominates. Add a per-race opt-out later if
// needed.
const ABANDONED_MEETINGS_KEY = 'tr_abandoned_meetings_v1';
const ABANDONED_RACES_KEY    = 'tr_abandoned_races_v1';
let abandonedMeetings = {};
let abandonedRaces    = {};
try {
  const raw = localStorage.getItem(ABANDONED_MEETINGS_KEY);
  if (raw) abandonedMeetings = JSON.parse(raw);
} catch(e) { abandonedMeetings = {}; }
try {
  const raw = localStorage.getItem(ABANDONED_RACES_KEY);
  if (raw) abandonedRaces = JSON.parse(raw);
} catch(e) { abandonedRaces = {}; }

function abandonedMeetingKey(venue, date) {
  return (venue || '') + '|' + (date || '');
}
function isMeetingAbandoned(venue, date) {
  return !!abandonedMeetings[abandonedMeetingKey(venue, date)];
}
function isRaceAbandoned(race) {
  if (!race) return false;
  // Race-level mark takes precedence; meeting-level mark covers the rest.
  if (abandonedRaces[String(race.race_id)]) return true;
  return isMeetingAbandoned(race.venue, race.date);
}
function setMeetingAbandoned(venue, date, isAbandoned) {
  const k = abandonedMeetingKey(venue, date);
  if (isAbandoned) abandonedMeetings[k] = { ts: new Date().toISOString() };
  else delete abandonedMeetings[k];
  try { localStorage.setItem(ABANDONED_MEETINGS_KEY, JSON.stringify(abandonedMeetings)); } catch(e) {}
  if (typeof scheduleSyncPush === 'function') scheduleSyncPush();
}
function setRaceAbandoned(raceId, isAbandoned) {
  const k = String(raceId);
  if (isAbandoned) abandonedRaces[k] = { ts: new Date().toISOString() };
  else delete abandonedRaces[k];
  try { localStorage.setItem(ABANDONED_RACES_KEY, JSON.stringify(abandonedRaces)); } catch(e) {}
  if (typeof scheduleSyncPush === 'function') scheduleSyncPush();
}

// ── Legacy: manualOdds storage ──────────────────────────────────────────────
// Earlier versions let the user override the live fxprice on each pick row.
// That's been replaced by the read-only Fxd column + dedicated odds-taken
// input (which is the source of truth for stake calc, persisted via the bet
// log entry's oddsTaken field). The manualOdds storage is kept here only so
// existing Gist sync payloads still load cleanly; it is no longer read or
// written by the UI.
const ODDS_STORAGE_KEY = 'toprate_v3_odds';
let manualOdds = {};
try {
  const raw = localStorage.getItem(ODDS_STORAGE_KEY);
  if (raw) manualOdds = JSON.parse(raw);
} catch(e) { manualOdds = {}; }

// Per-pick manual result storage: {run_id: {finish: 1|2|3|0, ts: ISO}}
// Used when official results aren't yet in the data. Cleared automatically
// when official results arrive (handled in renderToday by checking r.f).
const RESULTS_STORAGE_KEY = 'toprate_v3_results';
let manualResults = {};
try {
  const raw = localStorage.getItem(RESULTS_STORAGE_KEY);
  if (raw) manualResults = JSON.parse(raw);
} catch(e) { manualResults = {}; }

function saveResults() {
  try { localStorage.setItem(RESULTS_STORAGE_KEY, JSON.stringify(manualResults)); } catch(e) {}
  if (typeof scheduleSyncPush === 'function') scheduleSyncPush();
}

// ── Manual track rating override ────────────────────────────────────────────
// User can override the going for a meeting (e.g. official says "Good 4" but
// you've been told it's playing soft). Keyed by venue|date so different days
// at same venue don't conflict. Syncs via Gist so override appears on mobile.
const TRACK_RATINGS_KEY = 'tr_track_ratings_v1';
let trackRatings = {};
try {
  const raw = localStorage.getItem(TRACK_RATINGS_KEY);
  if (raw) trackRatings = JSON.parse(raw);
} catch(e) { trackRatings = {}; }

// Per-race override key. Race-level keys win over meeting-level keys, but
// meeting-level keys (legacy) are still honoured as a fallback.
function raceTrackRatingKey(raceId) {
  return 'race:' + (raceId || '');
}
function trackRatingKey(venue, date) {
  return (venue || '') + '|' + (date || '');
}
function getRaceTrackRating(race) {
  if (!race) return null;
  const rk = raceTrackRatingKey(race.race_id);
  if (trackRatings[rk]) return trackRatings[rk];
  // Fallback to meeting-level key for legacy compatibility
  const mk = trackRatingKey(race.venue, race.date);
  return trackRatings[mk] || null;
}
function setRaceTrackRating(race, rating) {
  if (!race) return;
  const k = raceTrackRatingKey(race.race_id);
  if (rating == null || rating === '') {
    delete trackRatings[k];
  } else {
    trackRatings[k] = rating;
  }
  try { localStorage.setItem(TRACK_RATINGS_KEY, JSON.stringify(trackRatings)); } catch(e) {}
  if (typeof scheduleSyncPush === 'function') scheduleSyncPush();
}
// Returns the going string with override applied if present
function getEffectiveGoing(race) {
  if (!race) return '';
  return getRaceTrackRating(race) || race.going || '';
}
// Legacy meeting-level helpers - kept for backward compat with any callers
function getTrackRating(venue, date, fallback) {
  const k = trackRatingKey(venue, date);
  return trackRatings[k] || fallback;
}
function setTrackRating(venue, date, rating) {
  const k = trackRatingKey(venue, date);
  if (rating == null || rating === '') {
    delete trackRatings[k];
  } else {
    trackRatings[k] = rating;
  }
  try { localStorage.setItem(TRACK_RATINGS_KEY, JSON.stringify(trackRatings)); } catch(e) {}
  if (typeof scheduleSyncPush === 'function') scheduleSyncPush();
}

// ── TODAY tab rendering ────────────────────────────────────────────────────
// State: which date is being browsed in the Today tab. Null until first render,
// then defaults to local today. Persisted across re-renders within the session.
let currentTodayDate = null;

function renderToday() {
  const listPending  = document.getElementById('picks-list-pending');
  const listResulted = document.getElementById('picks-list-resulted');
  const headPending  = document.getElementById('pending-head');
  const headResulted = document.getElementById('resulted-head');
  listPending.innerHTML = '';
  listResulted.innerHTML = '';
  // Counters for section heads - updated as rows are appended below
  let countPending = 0;
  let countResulted = 0;
  // Legacy `list` reference kept for any code below that referenced it as
  // the empty-state placeholder. We'll render the empty state into the
  // pending list (above resulted) so users see it in the natural reading
  // order.
  const list = listPending;

  // Clean up stale manual results - if any official result has arrived for a
  // run_id that has a manual entry, drop the manual one.
  let cleanedManual = false;
  Object.keys(manualResults).forEach(rid => {
    const pick = (PICKS_TODAY || []).find(p => String(p.run_id) === rid);
    if (pick && pick.runner_full && pick.runner_full.f != null) {
      delete manualResults[rid];
      cleanedManual = true;
    }
  });
  if (cleanedManual) saveResults();

  // Filter to the date being browsed (defaults to today on first render)
  if (!currentTodayDate) currentTodayDate = isoDate(0);
  const browseDate = currentTodayDate;
  const localToday = isoDate(0);
  // Picks for this date across all models (used for sub-tab badge counts)
  const dateAllPicks = (PICKS_TODAY || []).filter(p => p.date === browseDate);
  // Active-model-only picks for this date (pre-filter)
  const activeModel = (activeModels && activeModels.today) || 'main';
  const modelPicksForDate = dateAllPicks.filter(p => (p.model || 'main') === activeModel);
  // Apply Today filters (field size, jky rating). Rows that fail filters
  // are hidden entirely (not dimmed) because Today rows are large and
  // action-oriented - dimming would be visually noisy. Hero stats below
  // recompute against the FILTERED set, so a user filtering to "Jky 85+"
  // sees the P&L/WR for that subset specifically.
  const todaysPicks = modelPicksForDate.filter(p => todayPickPassesFilters(p));

  // Update sub-tab badge counts to reflect picks-per-model for browsed date
  // (pre-filter so user sees total available across models)
  ['main', 'loose'].forEach(m => {
    const badge = document.getElementById('today-subtab-count-' + m);
    if (badge) badge.textContent = dateAllPicks.filter(p => (p.model || 'main') === m).length;
  });

  // Update filter-bar summary: "Showing N of M picks" when filters are active.
  // Empty when filters at defaults so the bar doesn't show stale info.
  const _todayFilterSumEl = document.getElementById('today-filter-summary');
  if (_todayFilterSumEl) {
    const anyActive = todayFilters.minFs > 0 || todayFilters.minJky > 0;
    if (anyActive && modelPicksForDate.length > 0) {
      _todayFilterSumEl.textContent =
        'Showing ' + todaysPicks.length + ' of ' + modelPicksForDate.length + ' picks';
    } else {
      _todayFilterSumEl.textContent = '';
    }
  }
  // Sync filter control values from persisted state on re-render
  const _todayFilterFsSel = document.getElementById('today-filter-fs');
  if (_todayFilterFsSel && String(_todayFilterFsSel.value) !== String(todayFilters.minFs)) {
    _todayFilterFsSel.value = String(todayFilters.minFs);
  }
  const _todayFilterJkySel = document.getElementById('today-filter-jky');
  if (_todayFilterJkySel && String(_todayFilterJkySel.value) !== String(todayFilters.minJky)) {
    _todayFilterJkySel.value = String(todayFilters.minJky);
  }

  // Update date bar UI
  const tdInput = document.getElementById('today-date-input');
  if (tdInput && tdInput.value !== browseDate) tdInput.value = browseDate;
  const _tToday = isoDate(0), _tYest = isoDate(-1), _tTom = isoDate(1);
  document.querySelectorAll('.today-date-quick').forEach(b => {
    const k = b.dataset.tdate;
    let d = _tToday;
    if (k === 'yesterday') d = _tYest;
    if (k === 'tomorrow') d = _tTom;
    b.classList.toggle('active', d === browseDate);
  });
  const tdInfo = document.getElementById('today-date-info');
  if (tdInfo) {
    tdInfo.textContent = todaysPicks.length + (todaysPicks.length === 1 ? ' pick' : ' picks');
  }

  if (todaysPicks.length === 0) {
    // Distinguish "actually no picks for this date" from "all picks failed filters"
    const filtersActive = todayFilters.minFs > 0 || todayFilters.minJky > 0;
    if (filtersActive && modelPicksForDate.length > 0) {
      list.innerHTML = '<div class="empty-state">' +
        '<div class="head">No picks match current filters</div>' +
        '<div class="sub">' + modelPicksForDate.length + ' pick' +
        (modelPicksForDate.length === 1 ? '' : 's') +
        ' for this date are hidden by your Field/Jky filters. Click Reset to show all.</div>' +
        '</div>';
    } else {
      const dates = [...new Set((PICKS_TODAY || []).map(p => p.date).filter(Boolean))];
      let hint = '';
      if (dates.length > 0) {
        hint = '<div class="sub" style="margin-top:12px;">Picks available for: ' +
          dates.slice(-3).join(', ') + '. Pick a different date above or use the Race tab to browse.</div>';
      }
      list.innerHTML = '<div class="empty-state"><div class="head">No picks for ' + browseDate + '</div>' +
        '<div class="sub">The model did not find any qualifying runners on this date, or the data has not been refreshed yet.</div>' + hint + '</div>';
    }
    const hdrEmpty = document.getElementById('picks-header');
    if (hdrEmpty) hdrEmpty.style.display = 'none';
    // Hide section heads - empty state owns the visual space
    headPending.style.display = 'none';
    headResulted.style.display = 'none';
    return;
  }
  // Show header (in case it was hidden previously)
  const hdrShow = document.getElementById('picks-header');
  if (hdrShow && window.matchMedia('(min-width: 721px)').matches) {
    hdrShow.style.display = 'grid';
  }

  // Use the active model's min_odds. Fallback to primary if active has none.
  const _activeModelMeta = MODEL_META[activeModel] || MODEL_META[PRIMARY_KEY] || {};
  const minOdds = _activeModelMeta.min_odds || 3.0;

  // Sort by start time
  todaysPicks.sort((a, b) => (a.start_time || '').localeCompare(b.start_time || ''));

  let todayWins = 0, todayLosses = 0, todayPnL = 0, todaySettled = 0, todayQualifying = 0;
  let todayPlaces = 0;        // 1st/2nd/3rd finishes among placed bets
  let todayStakeTotal = 0;    // sum of stake (for ROI denominator)
  let todayReturnTotal = 0;   // sum of (stake * settlePrice) on wins, 0 on losses (for ROI numerator)
  // Separate counter for placed bets that have settled - this is the denominator
  // for Win Rate and Place Rate KPIs. The user wants those rates to reflect bets
  // they actually held, not theoretical model performance.
  let todayPlacedSettled = 0;
  const now = new Date();

  todaysPicks.forEach((p, idx) => {
    const r = p.runner_full || {};
    const csvPrice = p.fxprice;  // Live API fixed odds (read-only)
    const betEntry = getBetEntry(p.run_id);
    const isBetPlaced = !!betEntry.placed;
    const oddsTaken = betEntry.oddsTaken;

    // Stake source of truth: oddsTaken if entered, else fall back to live fxprice
    // (muted styling when falling back so the user sees the calc is provisional).
    const stakePrice = (oddsTaken != null && oddsTaken > 1) ? oddsTaken : csvPrice;
    const usingFallback = !(oddsTaken != null && oddsTaken > 1);
    const hasOddsTaken = oddsTaken != null && oddsTaken > 1;

    // Threshold check uses the live fxprice. This is the model rule and drives
    // the "qualifies" / "below-threshold" visual state plus the qualifying
    // counter in the hero strip.
    const meetsThreshold = csvPrice != null && csvPrice >= minOdds;
    // For stake calc and settled P&L, an explicit oddsTaken entry means the
    // user has already bet (e.g. dead-heat halving where the live fxprice now
    // looks under threshold but they actually took a qualifying price).
    // The threshold is a pre-bet filter; once you have bet, calculate.
    const isActiveBet = meetsThreshold || hasOddsTaken;
    const stake = (isActiveBet && stakePrice != null && stakePrice > 1)
                    ? calcStake(stakePrice, { capExempt: hasOddsTaken }) : null;
    if (meetsThreshold) todayQualifying++;

    // Result state
    const manRes = manualResults[String(p.run_id)];
    const officialFinish = r.f;
    const hasOfficial = officialFinish != null;
    const isSettled = hasOfficial || (manRes != null);
    const displayWon = hasOfficial ? (officialFinish === 1) : (manRes ? manRes.finish === 1 : false);

    // Update settled counters
    // For settled bets, P&L uses oddsTaken if recorded, else SP, else live fxprice.
    // If deadHeat is flagged on a winning bet, the return is halved (profit and stake
    // are split with the joint-winner per Aus rules).
    // KPI accumulation rule: only bets the user has marked PLACED contribute to
    // Win Rate / Place Rate / ROI / P&L. Picks that qualified by threshold but
    // weren't bet stay in the row count (todaysPicks.length) but don't influence rates.
    let cardClass = 'pending';
    if (isSettled) {
      todaySettled++;
      const finishForPlace = hasOfficial ? officialFinish : (manRes ? manRes.finish : null);
      const isPlaceFinish = finishForPlace != null && finishForPlace >= 1 && finishForPlace <= 3;
      // Visual card class: still based on isActiveBet (so qualifying picks get
      // settled-win/loss styling even if user didn't tick "placed")
      if (isActiveBet && stake) {
        if (displayWon) cardClass = 'settled-win';
        else            cardClass = 'settled-loss';
      } else {
        cardClass = 'below-threshold';
      }
      // KPI accumulation: only count placed bets
      if (isBetPlaced && stake) {
        todayPlacedSettled++;
        if (isPlaceFinish) todayPlaces++;
        const settlePrice = hasOddsTaken ? oddsTaken : (r.sp || csvPrice);
        if (displayWon) {
          todayWins++;
          const dhMult = betEntry.deadHeat ? 0.5 : 1;
          todayPnL += stake * (settlePrice - 1) * dhMult;
          todayReturnTotal += stake + stake * (settlePrice - 1) * dhMult;
        } else {
          todayLosses++;
          todayPnL -= stake;
        }
        todayStakeTotal += stake;
      }
    } else if (!isActiveBet) {
      cardClass = 'below-threshold';
    } else {
      cardClass = 'qualifies';
    }

    // Time-to-jump (mins from now)
    let ttj = null;
    if (p.start_time) {
      const mins = Math.round((new Date(p.start_time) - now) / 60000);
      if (mins >= -2 && mins <= 240) ttj = mins;
    }
    let ttjHtml = '';
    if (ttj !== null) {
      const ttjCls = ttj <= 5 ? 'imm' : (ttj <= 30 ? 'soon' : '');
      ttjHtml = '<span class="ttj ' + ttjCls + '">' +
        (ttj <= 0 ? 'NOW' : (ttj < 60 ? ttj + 'm' : Math.floor(ttj/60) + 'h ' + (ttj%60) + 'm')) +
        '</span>';
    }

    // Signal pills - Score (cumulative composite) + TR / Mid / Late / Total + form string underneath
    function sigPill(label, rank) {
      if (rank == null) return '<span class="sig"><span class="lbl">' + label + '</span><span class="v">—</span></span>';
      const cls = rank === 1 ? 'r1' : (rank === 2 ? 'r2' : (rank === 3 ? 'r3' : ''));
      return '<span class="sig ' + cls + '"><span class="lbl">' + label + '</span><span class="v">' + rank + '</span></span>';
    }
    // The Score pill is special - shows the underlying probability score
    // (0.00-1.00, displayed as a 2-digit percentage) plus a confidence dot
    // indicating how tightly the signals agreed. The rank is still the
    // colour driver (#1 in race = emerald, #2 = light emerald, etc) so the
    // chip retains its "best in race" visual cue, but the displayed value
    // is the absolute score - which is what the 0.50 threshold actually
    // gates on. Showing the raw score makes it obvious why a pick clears
    // or fails the threshold.
    function scoreSigPill(rank, score, conf) {
      if (score == null && rank == null) return '<span class="sig"><span class="lbl">Score</span><span class="v">—</span></span>';
      const cls = rank === 1 ? 'r1' : (rank === 2 ? 'r2' : (rank === 3 ? 'r3' : ''));
      let confDot = '';
      if (conf != null) {
        // 80%+ = filled solid (high agreement), 50-80% = half (mixed), <50% = empty (split)
        const dotCls = conf >= 0.80 ? 'high' : (conf >= 0.50 ? 'mid' : 'low');
        const confTitle = 'Signal confidence ' + Math.round(conf * 100) + '% - ' +
          (conf >= 0.80 ? 'unanimous' : conf >= 0.50 ? 'mixed' : 'split');
        confDot = '<span class="conf-dot ' + dotCls + '" title="' + confTitle + '"></span>';
      }
      // Format score as 2-digit integer (0.62 -> 62). Compact for the
      // constrained 52px chip and reads as a percentage at a glance.
      const scoreDisplay = score != null ? Math.round(score * 100) : '—';
      const rankBit = rank != null ? ' (rank #' + rank + ' in this race)' : '';
      const scoreTooltip = 'Score ' + (score != null ? score.toFixed(3) : 'n/a') + rankBit +
        '. The Score is a logistic regression probability (Path C) that combines TR rating, ' +
        'WPR, Late, PF AI, PF Class, and PF L600. Threshold for picks is 0.50. ' +
        'Higher = stronger pick.';
      return '<span class="sig ' + cls + '" title="' + scoreTooltip + '">' +
        '<span class="lbl">Score</span><span class="v">' + scoreDisplay + '</span>' + confDot + '</span>';
    }
    // V3 voting model rule transparency: show how many of the 6 signals
    // hit the top-3 threshold and how many were #1. Format: "5/6 ★3" =
    // 5 of 6 signals top-3 with 3 #1s. The pick passed the rule if
    // top-3 votes >= 5 AND top-1 votes >= 3.
    // Vote badge is the ONLY signal indicator shown on mobile (everything
    // else moves to the expanded detail panel for cleaner scanning).
    const voteRanks = [p.wpr_rank, p.late_rank, p.wcR, p.l600R, p.pfaiR, p.tr_rank];
    const voteTop3 = voteRanks.filter(r => r != null && r <= 3).length;
    const voteTop1 = voteRanks.filter(r => r != null && r === 1).length;
    const voteTooltip = voteTop3 + ' of 6 signals rank top-3, ' + voteTop1 + ' rank #1. ' +
                    'V3 rule needs >=5 top-3 AND >=3 #1.';
    const voteBadgeHtml = '<span class="sig vote-badge" title="' + voteTooltip + '">' +
      '<span class="lbl">Votes</span>' +
      '<span class="v">' + voteTop3 + '/6</span>' +
      (voteTop1 >= 3 ? '<span class="vote-star" title="' + voteTop1 + ' #1 votes">★' + voteTop1 + '</span>' : '') +
      '</span>';

    // Desktop signal chips - the 6 voting signals in a 3-col grid. Score is
    // separate (stacked above the Votes badge in its own mini-column) since
    // it's NOT part of the voting rule - it's the headline metric. Visual
    // hierarchy: voting chips on the left = "why this was picked",
    // Score+Votes on the right = "how strong is the pick". Hidden on mobile
    // via CSS where only the votes badge stays visible.
    const desktopChipsHtml =
      sigPill('WPR', p.wpr_rank) +
      sigPill('Late', p.late_rank) +
      sigPill('Class', p.wcR) +
      sigPill('L600', p.l600R) +
      sigPill('PFAI', p.pfaiR) +
      sigPill('TR', p.tr_rank);
    // Score chip stacks above Votes badge in a dedicated mini-column
    const scoreChipHtml = scoreSigPill(p.crk, p.cs, p.csc);

    const sigsTopHtml =
      '<span class="desktop-chips">' + desktopChipsHtml + '</span>' +
      '<span class="score-votes-stack">' + scoreChipHtml + voteBadgeHtml + '</span>';
    // Form string row underneath: "3-1-7-2" - shown on desktop only; on
    // mobile it moves into the expand panel to keep rows tight.
    const formHtml = r.fm ?
      '<div class="pr-form desktop-only" title="Last 4 finishes">' + escapeHtml(r.fm) + '</div>' : '';
    const sigsHtml = '<div class="pr-sigs-top">' + sigsTopHtml + '</div>' + formHtml;

    // Live fixed odds display (read-only)
    const oddsCls = meetsThreshold ? 'qualifies' : 'below';
    const oddsValStr = csvPrice != null ? csvPrice.toFixed(2) : '—';
    const oddsValCls = csvPrice != null ? 'v' : 'v empty';
    // Top Fluc (TF) - the highest bookie price during the pre-race market.
    // Null until results sync, so show as '—' placeholder until post-race.
    // Rendered as a small sub-line under the Fxd so users can compare what
    // they took vs the peak available, especially for settled picks.
    const tfPrice = p.top;
    const tfStr = tfPrice != null ? '$' + tfPrice.toFixed(2) : '—';
    const tfTitle = tfPrice != null
      ? 'Top Fluc $' + tfPrice.toFixed(2) + ' - highest bookie price during pre-race market'
      : 'Top Fluc - available after results sync';
    const oddsHtml =
      '<div class="pr-odds-display ' + oddsCls + '" title="Live fixed odds at last refresh">' +
        '<div class="pr-odds-main">' +
          (csvPrice != null ? '<span class="cur">$</span>' : '') +
          '<span class="' + oddsValCls + '">' + oddsValStr + '</span>' +
        '</div>' +
        '<div class="pr-odds-tf" title="' + tfTitle + '">' +
          '<span class="tf-lbl">TF</span>' +
          '<span class="tf-val' + (tfPrice == null ? ' empty' : '') + '">' + tfStr + '</span>' +
        '</div>' +
      '</div>';

    // Stake display - units (large) + dollar value (small) below
    // Return display - same shape: units returned + dollar return below
    // Both muted when calculated from fallback fxprice (no odds-taken yet).
    const stakeWrapCls = 'pr-stake' + (usingFallback ? ' muted' : '');
    const returnWrapCls = 'pr-return' + (usingFallback ? ' muted' : '');
    let stakeHtml, returnHtml;
    // Stake/Return only populate when the user has explicitly marked the bet as
    // placed. A qualifying pick they didn't bet shouldn't imply a stake outlay.
    if (isBetPlaced && stake) {
      // Stake: how much I'm putting down
      stakeHtml = '<span class="units">' + stake.toFixed(2) + 'u</span>' +
        '<span class="ret">' + fmtDollar(stake) + '</span>';

      // Return: only show actual payout when bet has settled and won.
      // Pre-result or losing bets show em-dash so the column doesn't imply winnings.
      if (isSettled && displayWon) {
        // Dead heat halves the return (joint winner).
        const dhMult = betEntry.deadHeat ? 0.5 : 1;
        const returnUnits = stake * stakePrice * dhMult;
        returnHtml = '<span class="units">' + returnUnits.toFixed(2) + 'u</span>' +
          '<span class="ret">' + fmtDollar(returnUnits) + '</span>';
      } else {
        returnHtml = '<span class="skip">&mdash;</span>';
      }
    } else if (!isActiveBet) {
      stakeHtml = '<span class="skip">no bet</span>';
      returnHtml = '<span class="skip">&mdash;</span>';
    } else {
      // Qualifying pick but user hasn't placed the bet
      stakeHtml = '<span class="skip">&mdash;</span>';
      returnHtml = '<span class="skip">&mdash;</span>';
    }

    // Result column
    // Helper: pick a CSS class suffix for losses based on finish position so
    // "lost as 2nd" (close miss) looks visually different from "lost as 8th".
    function lossPosClass(fin) {
      if (fin == null) return '';
      if (fin === 2) return ' fin2';
      if (fin >= 3 && fin <= 5) return ' fin345';
      return ' fin6plus';
    }
    let resultHtml;
    if (hasOfficial) {
      const cls = displayWon ? 'win' : ('loss' + lossPosClass(officialFinish));
      resultHtml = '<span class="res-tag ' + cls + '">' +
        (displayWon ? 'W' : 'L') + ' · ' + officialFinish + ord(officialFinish) + '</span>';
    } else if (manRes) {
      const cls = displayWon ? 'win' : ('loss' + lossPosClass(manRes.finish));
      resultHtml = '<span class="res-tag manual ' + cls + '" onclick="event.stopPropagation();">' +
        (displayWon ? 'W' : 'L') + ' · ' + manRes.finish + ord(manRes.finish) +
        '<span class="res-clear" data-clear-rid="' + p.run_id + '" title="Clear">×</span>' +
        '</span>';
    } else {
      // Compact dropdown - takes single-control width vs 4 buttons.
      // The "—" placeholder is the unset state; selecting any option records the result.
      resultHtml = '<select class="res-select" data-set-rid="' + p.run_id + '" ' +
        'onclick="event.stopPropagation();" title="Set result">' +
        '<option value="">— set —</option>' +
        '<option value="1">1st</option>' +
        '<option value="2">2nd</option>' +
        '<option value="3">3rd</option>' +
        '<option value="0">Lost</option>' +
        '</select>';
    }

    // Bet toggle and odds-taken
    let betHtml = '<button class="bet-btn ' + (isBetPlaced ? 'placed' : '') +
                  '" data-bet-rid="' + p.run_id + '" title="' +
                  (isBetPlaced ? 'Mark as not bet' : 'Mark this bet as placed') +
                  '" onclick="event.stopPropagation();">' +
                  (isBetPlaced ? '✓' : '+') + '</button>';
    if (isBetPlaced) {
      const oddsVal = betEntry.oddsTaken != null ? betEntry.oddsTaken.toFixed(2) : '';
      const showWarning = !betEntry.oddsTaken;
      betHtml += '<span class="odds-input-wrap" onclick="event.stopPropagation();">' +
                   '<span class="cur">$</span>' +
                   '<input type="number" step="0.01" min="1" class="odds-input" ' +
                   'data-odds-rid="' + p.run_id + '" placeholder="0.00" ' +
                   'value="' + oddsVal + '" />' +
                 '</span>';
      if (showWarning) {
        betHtml += '<span class="odds-warning" title="No odds-taken entered. Stake will use live Fxd price as fallback.">⚠</span>';
      }
    }

    // Build the row
    const row = document.createElement('div');
    row.className = 'pick-row ' + cardClass + (isBetPlaced ? ' bet-placed' : '');
    row.dataset.idx = idx;
    row.dataset.runId = p.run_id;

    // Meta line shows: distance · going · jky · trn (venue/race # now in its own column)
    const metaParts = [];
    if (p.distance) metaParts.push(p.distance + 'm');
    if (p.going) metaParts.push(escapeHtml(p.going));
    if (r.j) metaParts.push(escapeHtml(r.j));
    if (r.tn) metaParts.push(escapeHtml(r.tn));
    const metaLine = metaParts.join(' · ');

    // Field size chip - shown next to horse name. Small fields (<=7) get
    // a warn-style red badge to flag "manual skip" candidates. Below the
    // small-field threshold the model tends to pick longshots (favs under
    // the SP filter are excluded), so user wants a visual flag.
    const fsValue = p.field_size || (r.fs || null);
    let fsChipHtml = '';
    if (fsValue != null) {
      const fsWarn = fsValue <= 7;
      const fsTip = fsWarn
        ? 'Small field (' + fsValue + ' runners). User strategy: skip bets in fields of 7 or fewer.'
        : fsValue + ' runners in this race';
      fsChipHtml = '<span class="fs-chip ' + (fsWarn ? 'warn' : '') + '" title="' + fsTip + '">' +
        'F' + fsValue + '</span>';
    }

    // Jockey rating chip - absolute rating buckets (delta dropped for simplicity).
    // 4 bands: red <75, amber 75-79, grey 80-84, green 85+.
    // Based on jockey_rating_analysis: rating >=85 was the +2.6% ROI bucket,
    // 80-84 the worst at -22.9%, 75-79 mediocre at -9.6%, <75 weak.
    // (Earlier combined Abs+Delta rule was simpler to read but the user
    // preference is to just see the rating - no race-context maths needed
    // since the rating itself encodes jockey quality on its own.)
    let jkyChipHtml = '';
    if (r.jrt != null) {
      const myRating = Math.round(r.jrt);
      let cls = '';
      let lbl = '';
      if (myRating >= 85) {
        cls = 'good';
        lbl = 'Elite jockey rating (85+). +2.6% ROI bucket in backtest, 29.6% WR.';
      } else if (myRating >= 80) {
        cls = '';  // grey neutral
        lbl = 'Decent jockey rating (80-84). Underperforming bucket in backtest (-22.9% ROI).';
      } else if (myRating >= 75) {
        cls = 'warn';
        lbl = 'Mediocre jockey rating (75-79). -9.6% ROI bucket in backtest.';
      } else {
        cls = 'bad';
        lbl = 'Weak jockey rating (below 75). Worst-performing bucket in backtest.';
      }
      const tip = 'Jockey rating ' + myRating + '. ' + lbl;
      jkyChipHtml = '<span class="jky-chip ' + cls + '" title="' + tip + '">Jky ' + myRating + '</span>';
    }
    const fsAndJkyChips = fsChipHtml + jkyChipHtml;

    row.innerHTML =
      '<div class="pr-time">' + fmtTime(p.start_time) + ttjHtml + '</div>' +
      '<div class="pr-venue clickable" data-nav-rid="' + (p.race_id || '') + '" title="Open race detail">' +
        '<div class="v-name">' + escapeHtml(p.venue || '') + '</div>' +
        '<div class="v-race">R' + p.race + ' ↗</div>' +
      '</div>' +
      '<div class="pr-runner">' +
        '<span class="tab-bdg">' + (p.tab || '?') + '</span>' +
        '<div class="rdetails">' +
          '<div class="rhorse">' + escapeHtml(p.horse || '') + fsAndJkyChips + '</div>' +
          '<div class="rmeta">' + metaLine + '</div>' +
        '</div>' +
      '</div>' +
      '<div class="pr-sigs">' + sigsHtml + '</div>' +
      '<div class="pr-odds"><span class="cell-lbl">Fxd</span>' + oddsHtml + '</div>' +
      '<div class="' + stakeWrapCls + '"><span class="cell-lbl">Stake</span>' + stakeHtml + '</div>' +
      '<div class="' + returnWrapCls + '"><span class="cell-lbl">Return</span>' + returnHtml + '</div>' +
      '<div class="pr-result"><span class="cell-lbl">Result</span>' + resultHtml + '</div>' +
      '<div class="pr-bet"><span class="cell-lbl">Bet</span>' + betHtml + '</div>' +
      '<div class="pr-chev">▾</div>';

    // Route row + detail to the correct section list. isSettled was computed
    // earlier in this loop (line ~5440) from hasOfficial OR manRes.
    const sectionList = isSettled ? listResulted : listPending;
    if (isSettled) countResulted++; else countPending++;
    sectionList.appendChild(row);

    // Detail panel (initially hidden)
    const detail = document.createElement('div');
    detail.className = 'pick-detail';
    detail.dataset.idx = idx;
    detail.innerHTML = buildDetailHTML(p, r);
    sectionList.appendChild(detail);

    // Click row to expand/collapse (but not when clicking inputs/buttons or
    // the clickable venue block which navigates to race detail)
    row.addEventListener('click', e => {
      if (e.target.closest('.odds-input, .odds-input-wrap, .pr-result button, .res-clear, .bet-btn')) return;
      // Venue block click - navigate to race detail and stop here, don't expand
      const navTarget = e.target.closest('.pr-venue.clickable');
      if (navTarget) {
        e.stopPropagation();
        navigateToRace(navTarget.dataset.navRid);
        return;
      }
      const isExpanded = row.classList.toggle('expanded');
      detail.classList.toggle('show', isExpanded);
    });
  });

  // Update section heads with counts. Hide a section's head when empty so
  // we don't show "Resulted (0)" before any race has run. When BOTH are
  // empty the larger empty-state branch above has already taken over.
  document.getElementById('pending-count').textContent  = countPending;
  document.getElementById('resulted-count').textContent = countResulted;
  headPending.style.display  = countPending  > 0 ? 'flex' : 'none';
  headResulted.style.display = countResulted > 0 ? 'flex' : 'none';

  // Handlers must scope across BOTH pending and resulted lists since rows
  // can live in either. Use the shared parent (.picks-scroll) so the
  // existing single querySelectorAll pattern still works.
  const picksScroll = document.getElementById('picks-scroll');

  // Result chip handlers - works for both <button data-pos> (legacy) and
  // <select> (new compact dropdown). The handler picks the right event type.
  picksScroll.querySelectorAll('[data-set-rid]').forEach(el => {
    const eventName = el.tagName === 'SELECT' ? 'change' : 'click';
    el.addEventListener(eventName, e => {
      e.stopPropagation();
      const rid = el.dataset.setRid;
      // For select: pos comes from el.value. For button: from data-pos.
      const raw = el.tagName === 'SELECT' ? el.value : el.dataset.pos;
      if (raw === '' || raw == null) return;  // empty placeholder option
      const pos = parseInt(raw);
      if (isNaN(pos)) return;
      manualResults[String(rid)] = { finish: pos, ts: new Date().toISOString() };
      saveResults();
      renderToday();
    });
  });
  picksScroll.querySelectorAll('[data-clear-rid]').forEach(el => {
    el.addEventListener('click', e => {
      e.stopPropagation();
      const rid = el.dataset.clearRid;
      delete manualResults[String(rid)];
      saveResults();
      renderToday();
    });
  });
  // Bet toggle button
  picksScroll.querySelectorAll('[data-bet-rid]').forEach(el => {
    el.addEventListener('click', e => {
      e.stopPropagation();
      const rid = el.dataset.betRid;
      const cur = isPlaced(rid);
      setBetEntry(rid, { placed: !cur });
      renderToday();
      if (typeof renderPnL === 'function') renderPnL();
    });
  });
  // Odds input field
  picksScroll.querySelectorAll('[data-odds-rid]').forEach(el => {
    el.addEventListener('input', e => {
      const rid = el.dataset.oddsRid;
      const v = parseFloat(e.target.value);
      setBetEntry(rid, { oddsTaken: (isNaN(v) || v <= 0) ? null : v });
      // Don't full re-render on every keystroke; just update the warning indicator visibility
      const row = el.closest('.pick-row');
      const warn = row ? row.querySelector('.odds-warning') : null;
      if (v > 0 && warn) warn.style.display = 'none';
    });
    el.addEventListener('blur', e => {
      // Re-render so the stake column picks up the new oddsTaken (or fallback)
      // and PnL updates flow through.
      renderToday();
      if (typeof renderPnL === 'function') renderPnL();
    });
    // Stop click on input from triggering row expand
    el.addEventListener('click', e => e.stopPropagation());
  });
  // Dead heat toggle (in detail panel)
  picksScroll.querySelectorAll('[data-deadheat-rid]').forEach(el => {
    el.addEventListener('change', e => {
      e.stopPropagation();
      const rid = el.dataset.deadheatRid;
      setBetEntry(rid, { deadHeat: el.checked });
      renderToday();
      if (typeof renderPnL === 'function') renderPnL();
    });
    el.addEventListener('click', e => e.stopPropagation());
  });

  // ── Update hero strip (4 KPIs, all today-only) ─────────────────────────

  // 1) Today P&L
  const pnlEl = document.getElementById('hs-today-pnl');
  if (todayPlacedSettled > 0 && todayStakeTotal > 0) {
    pnlEl.textContent = (todayPnL >= 0 ? '+' : '') + todayPnL.toFixed(2) + 'u';
    pnlEl.classList.remove('pos', 'neg');
    if (todayPnL > 0) pnlEl.classList.add('pos');
    else if (todayPnL < 0) pnlEl.classList.add('neg');
    document.getElementById('hs-today-pnl-units').textContent =
      (todayPnL >= 0 ? '+' : '') + fmtDollar(todayPnL);
  } else {
    pnlEl.textContent = '—';
    pnlEl.classList.remove('pos', 'neg');
    document.getElementById('hs-today-pnl-units').textContent =
      todaysPicks.length + ' picks · 0 placed bets settled';
  }

  // 2) Win Rate (today, placed bets that have settled)
  const wrEl = document.getElementById('hs-today-wr');
  const wrSubEl = document.getElementById('hs-today-wr-sub');
  if (todayPlacedSettled > 0) {
    const wr = todayWins / todayPlacedSettled;
    wrEl.textContent = (wr * 100).toFixed(1) + '%';
    wrSubEl.textContent = todayWins + ' of ' + todayPlacedSettled + ' settled';
  } else {
    wrEl.textContent = '—';
    wrSubEl.textContent = 'no placed bets settled';
  }

  // 3) Place Rate (today, placed bets that have settled - 1st/2nd/3rd)
  const prEl = document.getElementById('hs-today-pr');
  const prSubEl = document.getElementById('hs-today-pr-sub');
  if (todayPlacedSettled > 0) {
    const pr = todayPlaces / todayPlacedSettled;
    prEl.textContent = (pr * 100).toFixed(1) + '%';
    prSubEl.textContent = todayPlaces + ' of ' + todayPlacedSettled + ' settled';
  } else {
    prEl.textContent = '—';
    prSubEl.textContent = 'no placed bets settled';
  }

  // 4) ROI (today, placed bets only)
  const roiEl = document.getElementById('hs-today-roi');
  const roiSubEl = document.getElementById('hs-today-roi-sub');
  if (todayStakeTotal > 0) {
    const roi = (todayReturnTotal - todayStakeTotal) / todayStakeTotal;
    roiEl.textContent = (roi >= 0 ? '+' : '') + (roi * 100).toFixed(1) + '%';
    roiEl.classList.remove('pos', 'neg');
    if (roi > 0) roiEl.classList.add('pos');
    else if (roi < 0) roiEl.classList.add('neg');
    roiSubEl.textContent = 'on ' + todayStakeTotal.toFixed(2) + 'u staked';
  } else {
    roiEl.textContent = '—';
    roiEl.classList.remove('pos', 'neg');
    roiSubEl.textContent = 'no placed bets settled';
  }
}

// Build the expanded detail panel for a pick
function buildDetailHTML(p, r) {
  // Speed scores - 4 cells
  function speedCell(label, value, rank) {
    if (value == null) {
      return '<div class="pd-speed-cell">' +
        '<span class="sp-lbl">' + label + '</span>' +
        '<span class="sp-val" style="color:var(--ink-faint)">—</span>' +
        '<span class="sp-rk">—</span></div>';
    }
    const rkCls = rank === 1 ? 'r1' : (rank === 2 ? 'r2' : '');
    return '<div class="pd-speed-cell ' + rkCls + '">' +
      '<span class="sp-lbl">' + label + '</span>' +
      '<span class="sp-val">' + value.toFixed(1) + '</span>' +
      '<span class="sp-rk">' + (rank ? '#' + rank : '') + '</span></div>';
  }
  const speedHtml =
    '<div class="pd-speed">' +
      speedCell('Early', r.es, p.early_rank) +
      speedCell('Mid',   r.ms, p.mid_rank) +
      speedCell('Late',  r.ls, p.late_rank) +
      speedCell('Total', r.ts, p.total_rank) +
    '</div>';

  // Going category
  function goingCategory(g) {
    if (!g) return null;
    const gl = g.toLowerCase();
    if (gl.startsWith('firm')) return 'firm';
    if (gl.startsWith('good')) return 'good';
    if (gl.startsWith('soft')) return 'soft';
    if (gl.startsWith('heavy')) return 'heavy';
    if (gl.startsWith('synth')) return 'synth';
    return null;
  }
  const todayGoing = goingCategory(p.going);

  function perfStr(starts, wins, places) {
    if (!starts || starts === 0) return null;
    const w = wins || 0, pl = places || 0;
    return w + 'W ' + Math.max(0, pl - w) + 'P / ' + starts + ' starts';
  }
  const distPerf = perfStr(r.ds, r.dw, r.dp) || 'no runs';
  let goingPerf = 'no runs';
  if (todayGoing && r.gb && r.gb[todayGoing]) {
    const g = r.gb[todayGoing];
    goingPerf = perfStr(g.starts, g.wins, g.places) || 'no runs';
  }
  // Wet-track form (Soft + Heavy combined). Surfaced only when today's
  // track is wet, because that's when the question "can this horse handle
  // wet?" actually matters. Analysis showed Soft form transfers to Heavy
  // tracks (Soft-placers on Heavy: WR 31.8%, ROI -9.8% on n=22) - so a
  // combined Wet metric is the most decision-useful framing.
  let wetPerf = null;
  if ((todayGoing === 'soft' || todayGoing === 'heavy') && r.gb) {
    const soft  = r.gb.soft  || {};
    const heavy = r.gb.heavy || {};
    const s_starts = (soft.starts  || 0) + (heavy.starts  || 0);
    const s_wins   = (soft.wins    || 0) + (heavy.wins    || 0);
    const s_places = (soft.places  || 0) + (heavy.places  || 0);
    if (s_starts > 0) {
      wetPerf = perfStr(s_starts, s_wins, s_places);
    } else {
      wetPerf = 'no wet runs';
    }
  }

  // Recent WPR
  const wpr1 = r.wpr1, wpra = r.wpra, wprt = r.wprt;
  const wprStr = wpr1 != null ?
    (wpr1.toFixed(0) + ' · avg ' + (wpra != null ? wpra.toFixed(0) : '—') +
      (wprt != null ? ' · ' + (wprt > 0 ? '↑' : '↓') + Math.abs(wprt).toFixed(1) : '')) :
    '—';

  // Drift since open: today's price movement
  let driftStr = null, driftCls = '';
  const ph = (typeof PRICE_HIST !== 'undefined' && PRICE_HIST) ? PRICE_HIST[String(p.run_id)] : null;
  if (ph && ph.o && ph.r) {
    const pct = ((ph.r - ph.o) / ph.o) * 100;
    if (Math.abs(pct) >= 1) {
      driftStr = '$' + ph.o.toFixed(2) + ' → $' + ph.r.toFixed(2) +
                 ' (' + (pct > 0 ? '+' : '') + pct.toFixed(0) + '%)';
      // Firmed = price went down (steamer, market backed it)
      // Drifted = price went up (eased, market against it)
      driftCls = pct < 0 ? 'pos' : 'neg';
    } else {
      driftStr = '$' + ph.o.toFixed(2) + ' (steady)';
    }
  }

  // Settling type (from avg settled position)
  let settleStr = null;
  if (r.asp != null) {
    if (r.asp <= 2.5) settleStr = 'Leader (' + r.asp.toFixed(1) + ')';
    else if (r.asp <= 4.5) settleStr = 'On-pace (' + r.asp.toFixed(1) + ')';
    else if (r.asp <= 8.5) settleStr = 'Midfield (' + r.asp.toFixed(1) + ')';
    else settleStr = 'Back (' + r.asp.toFixed(1) + ')';
  }

  function field(label, value, cls) {
    if (value == null || value === '') return '';
    return '<div class="pd-field"><span class="fl">' + label + '</span>' +
      '<span class="fv ' + (cls || '') + '">' + escapeHtml(String(value)) + '</span></div>';
  }

  // Post-race prices - null until results sync. Render as '— (post-race)'
  // when missing so user knows it'll populate later, not that it's missing data.
  const tfDetailStr = p.top != null ? '$' + p.top.toFixed(2) : '— post-race';
  const spDetailStr = p.sp != null ? '$' + p.sp.toFixed(2) : '— post-race';
  const tfCls = p.top != null ? '' : 'muted';
  const spCls = p.sp != null ? '' : 'muted';

  // Jockey + Trainer rating context: show this runner's TR-internal rating,
  // its rank within the race field, and how far it sits behind the #1 in
  // each metric. Replaces the prior Jky 90d / Trn 365d (which were strike
  // rate % - useful but tangential to the model's rating signal). The
  // rating itself is a TopRate internal number; rank + delta puts it in
  // race context so the user can see e.g. "rating 84 (rank 3, -8 from #1)".
  function ratingContext(label, getter) {
    const myVal = getter(r);
    if (myVal == null) return null;
    // Look up the parent race + its runners to compute rank/delta
    const race = (typeof RACES !== 'undefined' && RACES)
      ? RACES.find(rc => String(rc.race_id) === String(p.race_id))
      : null;
    const runners = (race && race.runners) ? race.runners : [];
    const valid = runners.filter(u => getter(u) != null);
    if (valid.length === 0) {
      return Math.round(myVal).toString();  // just the rating if we can't rank
    }
    valid.sort((a, b) => getter(b) - getter(a));
    const myIdx = valid.findIndex(u => String(u.rid) === String(p.run_id));
    const rank = myIdx >= 0 ? (myIdx + 1) : null;
    const top = getter(valid[0]);
    const delta = myVal - top;
    let parts = [Math.round(myVal).toString()];
    if (rank != null) parts.push('#' + rank);
    if (rank != null && rank > 1) {
      // delta is negative or 0; show as -X from #1
      const d = Math.round(delta);
      if (d < 0) parts.push(d.toString() + ' from #1');
    }
    return parts.join(' · ');
  }
  const jockeyRatingStr = ratingContext('Jockey rating', u => u.jrt);
  const trainerRatingStr = ratingContext('Trainer rating', u => u.trt);

  const contextHtml = '<div class="pd-context">' +
    field('Form',          r.fm) +
    field('Drift',         driftStr, driftCls) +
    field('Settles',       settleStr) +
    field('Speed rating',  r.spd != null ? r.spd.toFixed(0) : null) +
    field('TR price',      r.trp != null ? '$' + r.trp.toFixed(2) : null) +
    field('Top Fluc',      tfDetailStr, tfCls) +
    field('SP',            spDetailStr, spCls) +
    field('Distance',      p.distance ? p.distance + 'm' : null) +
    field('Going',         p.going) +
    field('Field size',    p.field_size || r.fs) +
    field('Distance perf', distPerf) +
    field('Going perf',    goingPerf) +
    field('Wet form',      wetPerf) +
    field('Wt today',      r.wt != null ? r.wt + 'kg' : null) +
    field('Wt trend',      r.wtr != null ? (r.wtr > 0 ? '+' : '') + r.wtr.toFixed(1) + 'kg' : null) +
    field('Jockey',        r.j) +
    field('Jockey rating', jockeyRatingStr) +
    field('Trainer',       r.tn) +
    field('Trainer rating', trainerRatingStr) +
    field('Barrier',       r.b) +
    field('Recent WPR',    wprStr) +
  '</div>';

  // Bet adjustments - dead heat toggle (only shown when bet is placed)
  // Plus stake/return numbers since these are no longer in the row on mobile
  const bEntry = getBetEntry(p.run_id);
  let adjustmentsHtml = '';
  if (bEntry.placed) {
    const dhChecked = bEntry.deadHeat ? 'checked' : '';

    // Compute stake/return for display in the panel (replicates pick row logic)
    const minOdds = (MODEL_META[PRIMARY_KEY] && MODEL_META[PRIMARY_KEY].min_odds) || 3.0;
    const livePrice = p.fxprice;
    const oddsTaken = bEntry.oddsTaken;
    const stakePrice = oddsTaken || livePrice;
    const hasOddsTaken = oddsTaken != null && oddsTaken > 1;
    let stakeUnits = null, returnUnits = null, usedFallback = false;
    if (stakePrice && stakePrice > 1) {
      stakeUnits = calcStake(stakePrice, { capExempt: hasOddsTaken });
      const dhMult = bEntry.deadHeat ? 0.5 : 1;
      returnUnits = stakeUnits != null ? stakeUnits * stakePrice * dhMult : null;
      usedFallback = !hasOddsTaken;
    }
    let outlayHtml = '';
    if (stakeUnits != null) {
      outlayHtml =
        '<div class="pd-context" style="grid-template-columns: 1fr 1fr; margin-top: 6px;">' +
          '<div class="pd-field"><span class="fl">Stake</span>' +
            '<span class="fv">' + stakeUnits.toFixed(2) + 'u' +
            ' <span style="color:var(--ink-mute);font-weight:500;">' + fmtDollar(stakeUnits) + '</span>' +
            '</span></div>' +
          '<div class="pd-field"><span class="fl">Return if wins</span>' +
            '<span class="fv">' + returnUnits.toFixed(2) + 'u' +
            ' <span style="color:var(--emerald-deep);font-weight:500;">' + fmtDollar(returnUnits) + '</span>' +
            '</span></div>' +
        '</div>' +
        (usedFallback ? '<div style="font-size:10px;color:var(--ink-mute);margin-top:6px;">' +
          'Using live Fxd price as fallback - enter odds-taken for accurate stake.' +
          '</div>' : '');
    }

    adjustmentsHtml =
      '<div class="pd-section">' +
        '<div class="pd-section-title">Bet outlay</div>' +
        outlayHtml +
        '<label class="pd-toggle" onclick="event.stopPropagation();" style="margin-top: 10px;">' +
          '<input type="checkbox" data-deadheat-rid="' + p.run_id + '" ' + dhChecked + '>' +
          '<span class="pd-toggle-lbl">Dead heat</span>' +
          '<span class="pd-toggle-help">Halves the return on a winning bet (joint winner)</span>' +
        '</label>' +
      '</div>';
  }

  // First-starter warning: matches Race tab banner wording so the user gets
  // the same heads-up here that they would on the race detail
  let fsWarningHtml = '';
  if (p.hfs) {
    fsWarningHtml =
      '<div class="pd-fs-warn">' +
        '<span class="icon">⚠</span>' +
        '<div>' +
          '<div class="text">First starter in this race</div>' +
          '<div class="sub">Model signals do not apply to debut runners. Recommend skipping this race.</div>' +
        '</div>' +
      '</div>';
  }

  // Score breakdown - shows per-signal percentile so user can see which
  // signals agreed and which disagreed. Surfaces the math behind the conf dot.
  let scoreBreakdownHtml = '';
  if (r && r.cs != null) {
    const sigs = r.csg || {};
    const conf = r.csc;
    const sigNames = Object.keys(sigs);
    // Map raw signal keys to display labels
    const sigDisplayMap = {
      'toprate_rating': 'TopRate rating',
      'wpr_avg_last3':  'WPR avg last 3',
      'late_speed_score': 'Late speed',
      'jt_combo_win_pct': 'Jky/trn combo',
    };
    let sigRowsHtml = '';
    if (sigNames.length > 0) {
      sigRowsHtml = sigNames.map(sk => {
        const pct = sigs[sk];
        const lbl = sigDisplayMap[sk] || sk;
        const barW = Math.round(pct * 100);
        // Color bar by tier
        const barCls = pct >= 0.85 ? 'r1' : (pct >= 0.65 ? 'r2' : (pct >= 0.50 ? 'r3' : ''));
        return '<div class="pd-sig-row">' +
          '<span class="pd-sig-lbl">' + lbl + '</span>' +
          '<div class="pd-sig-bar"><div class="pd-sig-fill ' + barCls + '" style="width:' + barW + '%;"></div></div>' +
          '<span class="pd-sig-pct">' + Math.round(pct * 100) + '</span>' +
          '</div>';
      }).join('');
    } else {
      sigRowsHtml = '<div class="empty-text">Signal breakdown unavailable.</div>';
    }
    let confSummary = '';
    if (conf != null) {
      const confLbl = conf >= 0.80 ? 'unanimous - all signals agree' :
                     conf >= 0.50 ? 'mixed - signals partially agree' :
                                    'split - signals disagree';
      const confCls = conf >= 0.80 ? 'pos' : (conf >= 0.50 ? '' : 'warn');
      confSummary = '<div class="pd-conf-summary ' + confCls + '">' +
        'Confidence: <strong>' + Math.round(conf * 100) + '%</strong> · ' + confLbl +
        '</div>';
    }
    scoreBreakdownHtml =
      '<div class="pd-section">' +
        '<div class="pd-section-title">Score breakdown · ' + r.cs.toFixed(2) + ' (rank #' + (r.crk || '?') + ')</div>' +
        confSummary +
        '<div class="pd-sig-bars">' + sigRowsHtml + '</div>' +
      '</div>';
  }

  return fsWarningHtml +
         '<div class="pd-section"><div class="pd-section-title">Context</div>' + contextHtml + '</div>' +
         scoreBreakdownHtml +
         adjustmentsHtml;
}

function ord(n) {
  const s = ['th','st','nd','rd']; const v = n % 100;
  return s[(v - 20) % 10] || s[v] || s[0];
}

// ── RACE tab rendering ──────────────────────────────────────────────────────
// State
let currentBrowseDate = null;     // YYYY-MM-DD being browsed
let currentRaceId = null;          // race_id of the currently open detail

// Filter state for the Today tab pick rows. Persisted across reloads so
// users don't lose their filters when refreshing.
//   minFs   = minimum field size of the pick's race (race.fs >= minFs); 0 = no filter
//   minJky  = minimum jockey rating on the pick (runner.jrt >= minJky); 0 = no filter
// Re-uses the old RACE_FILTERS_KEY since the shape is identical to the
// previous race-tab implementation; users who had filters set on the Race
// tab will see them migrate to the Today tab naturally.
const TODAY_FILTERS_KEY = 'toprate_v3_today_filters';
let todayFilters = { minFs: 0, minJky: 0 };
try {
  // Try new key first, fall back to old race-filters key for migration
  let stored = localStorage.getItem(TODAY_FILTERS_KEY);
  if (!stored) stored = localStorage.getItem('toprate_v3_race_filters');
  if (stored) {
    const parsed = JSON.parse(stored);
    if (parsed && typeof parsed === 'object') {
      todayFilters = Object.assign(todayFilters, parsed);
      // Drop legacy pickOnly field if present in migrated state
      delete todayFilters.pickOnly;
    }
  }
} catch(e) {}
function saveTodayFilters() {
  try { localStorage.setItem(TODAY_FILTERS_KEY, JSON.stringify(todayFilters)); } catch(e) {}
}

// Returns true if a Today-tab pick row passes all active filters.
// `pick` is an entry from PICKS_TODAY - has run_id, race_id, field_size,
// and we look up jrt via the race's runner list.
function todayPickPassesFilters(pick) {
  // Abandoned meetings/races: hide the pick from Today entirely. This is
  // the manual override for the PF/TR blind spot - abandonment data
  // doesn't reach the API until results come in (often hours late), so
  // the user marks it themselves and we honour that immediately. Resulted
  // picks with a finish position are not filtered here - they live in
  // P&L history. The pick's race may not be in RACES if the data is
  // stale, in which case we can't check - default to letting it pass.
  const raceForAbandon = RACES.find(r => String(r.race_id) === String(pick.race_id));
  if (raceForAbandon && isRaceAbandoned(raceForAbandon)) return false;
  // Field size filter - pick.field_size is set from race.fs at build time
  if (todayFilters.minFs > 0) {
    const fs = pick.field_size || 0;
    if (fs < todayFilters.minFs) return false;
  }
  // Jockey rating filter - look up the picked runner in its race to read jrt.
  // Picks don't carry jrt directly because they're built before all race
  // context is enriched; we fetch from the runner_full reference if present
  // (set in the enrichment loop), otherwise look up via RACES.
  if (todayFilters.minJky > 0) {
    let jrt = null;
    if (pick.runner_full && pick.runner_full.jrt != null) {
      jrt = pick.runner_full.jrt;
    } else {
      const race = RACES.find(r => String(r.race_id) === String(pick.race_id));
      if (race && race.runners) {
        const runner = race.runners.find(u => String(u.rid) === String(pick.run_id));
        if (runner && runner.jrt != null) jrt = runner.jrt;
      }
    }
    // Picks without jrt data fail the filter (intentional - user is asking
    // "show me picks where the jockey rating is at least N")
    if (jrt == null || jrt < todayFilters.minJky) return false;
  }
  return true;
}

function isoDate(offsetDays) {
  const d = new Date();
  d.setDate(d.getDate() + (offsetDays || 0));
  // Use local timezone, not UTC. toISOString() gives UTC which is wrong for AU users.
  const y = d.getFullYear();
  const m = String(d.getMonth() + 1).padStart(2, '0');
  const day = String(d.getDate()).padStart(2, '0');
  return y + '-' + m + '-' + day;
}

function renderMeetingsGrid() {
  const host = document.getElementById('race-meetings-list');
  if (!host) return;

  if (!currentBrowseDate) currentBrowseDate = isoDate(0);

  // Filter races to the chosen date, group by venue
  const dateRaces = RACES.filter(r => r.date === currentBrowseDate);
  if (dateRaces.length === 0) {
    host.innerHTML = '<div class="empty-state">' +
      '<div class="head">No meetings for ' + currentBrowseDate + '</div>' +
      '<div class="sub">Try Yesterday or Tomorrow, or pick another date.</div>' +
      '</div>';
    document.getElementById('race-date-info').textContent = '0 meetings';
    return;
  }

  const byVenue = {};
  dateRaces.forEach(r => {
    const v = r.venue || 'Unknown';
    if (!byVenue[v]) byVenue[v] = [];
    byVenue[v].push(r);
  });
  const meetings = Object.keys(byVenue).sort().map(v => ({
    venue: v,
    state: (byVenue[v][0] && byVenue[v][0].state) || '',
    races: byVenue[v].sort((a, b) => (a.race || 0) - (b.race || 0)),
  }));
  const maxR = Math.max(...meetings.map(m =>
    Math.max(...m.races.map(r => r.race || 0))));

  let html = '<div class="meetings-table">';
  // Header row
  html += '<div class="mt-row mt-head">';
  html += '<div class="mt-venue-col">Venue</div>';
  for (let i = 1; i <= maxR; i++) {
    html += '<div class="mt-race-head">R' + i + '</div>';
  }
  html += '</div>';

  // Meeting rows
  const now = new Date();
  meetings.forEach(m => {
    // Abandon state - check the meeting key. Note: m.races[0] gives us the
    // date (not stored on the meeting object itself; same across all races).
    const meetingDate = m.races[0] ? m.races[0].date : currentBrowseDate;
    const meetingAbandoned = isMeetingAbandoned(m.venue, meetingDate);
    const rowCls = 'mt-row' + (meetingAbandoned ? ' is-abandoned' : '');
    html += '<div class="' + rowCls + '" data-venue="' + escapeHtml(m.venue) +
      '" data-mdate="' + escapeHtml(meetingDate) + '">';
    const btnLabel = meetingAbandoned ? 'Abandoned ✓' : 'Mark abandoned';
    const btnTitle = meetingAbandoned
      ? 'Meeting marked abandoned - all picks hidden. Click to unmark.'
      : 'Mark this meeting as abandoned (hides picks for all its races).';
    html += '<div class="mt-venue-col">' +
      '<div class="mt-venue-name">' + escapeHtml(m.venue) + '</div>' +
      (m.state ? '<div class="mt-venue-state">' + escapeHtml(m.state) + '</div>' : '') +
      '<button type="button" class="mt-abandon-btn" data-abandon-meeting="' +
      escapeHtml(m.venue) + '|' + escapeHtml(meetingDate) + '" title="' +
      escapeHtml(btnTitle) + '">' + btnLabel + '</button>' +
      '</div>';
    for (let i = 1; i <= maxR; i++) {
      const race = m.races.find(r => r.race === i);
      if (!race) {
        html += '<div class="mt-race-cell mt-empty">—</div>';
        continue;
      }
      const tm = race.start_time ? fmtTime(race.start_time) : '';
      const isResulted = race.done === 1;
      let mins = null;
      if (race.start_time) {
        mins = Math.round((new Date(race.start_time) - now) / 60000);
      }
      const isPast = mins !== null && mins < -2;
      const isImminent = mins !== null && mins >= -2 && mins <= 15;
      const isSoon = mins !== null && mins > 15 && mins <= 45;
      const racePicks = (MODEL_PICKS[race.race_id] || {});
      const hasPick = !!(racePicks[PRIMARY_KEY] || []).length;
      const hasLoose = !!(racePicks['loose'] || []).length;
      // Field-size strategy gate. Same source-of-truth pattern as the Quaddie
      // tab (race.fs falling back to runners.length). Threshold 8 is the
      // user's metro-Saturday filter - fields of 7 or fewer push picks into
      // longshot territory because SP>=3 filter excludes short favourites.
      const cellFs = race.fs || (race.runners || []).length || 0;
      const fsOk = cellFs >= 8;

      let cellCls = 'mt-race-cell';
      if (hasPick) cellCls += ' has-pick';
      if (hasLoose) cellCls += ' has-loose-pick';
      if (fsOk) cellCls += ' mt-fsok';
      // Race-level abandon (or meeting-level, since isRaceAbandoned checks both).
      // Meeting-level fade applies via the row class, but race-level marks
      // need their own cell class for the case where only a single race is
      // abandoned within an otherwise normal meeting.
      if (isRaceAbandoned(race)) cellCls += ' is-abandoned';
      let badge = '';
      let lbl = tm || ('R' + i);
      if (isResulted) {
        cellCls += ' mt-resulted';
        // Find the winner (finish_position == 1) and show tab number.
        // Mark green if Main pick won, amber if Loose pick won, neutral otherwise.
        // This lets users scan resulted cards and immediately see model accuracy.
        const winner = (race.runners || []).find(u => u.f === 1);
        const winnerTab = winner ? winner.tab : null;
        const winnerRid = winner ? String(winner.rid) : null;
        const mainPickRids = (racePicks[PRIMARY_KEY] || []).map(p => String(p.run_id));
        const loosePickRids = (racePicks['loose'] || []).map(p => String(p.run_id));
        const mainHit = winnerRid && mainPickRids.indexOf(winnerRid) >= 0;
        const looseHit = winnerRid && loosePickRids.indexOf(winnerRid) >= 0;
        if (mainHit) cellCls += ' mt-result-main-hit';
        else if (looseHit) cellCls += ' mt-result-loose-hit';
        lbl = winnerTab != null ? ('#' + winnerTab) : 'Result';
      }
      else if (isImminent) {
        cellCls += ' mt-imminent';
        badge = '<span class="mt-cd">' + (mins <= 0 ? 'NOW' : mins + 'm') + '</span>';
      }
      else if (isSoon) { cellCls += ' mt-soon'; badge = '<span class="mt-cd-soon">' + mins + 'm</span>'; }
      else if (isPast && !isResulted) cellCls += ' mt-pending-late';

      // Tooltip explains the corner indicators. Only built when there's
      // something to explain - no point on empty/plain cells.
      let titleAttr = '';
      const tipParts = [];
      if (hasPick) tipParts.push('Main model pick');
      if (hasLoose) tipParts.push('Loose model pick');
      if (isResulted) {
        const winner = (race.runners || []).find(u => u.f === 1);
        if (winner) {
          let resultTxt = 'Winner: ' + (winner.h || '#' + winner.tab);
          const winnerRid = String(winner.rid);
          const mainPickRids = (racePicks[PRIMARY_KEY] || []).map(p => String(p.run_id));
          const loosePickRids = (racePicks['loose'] || []).map(p => String(p.run_id));
          if (mainPickRids.indexOf(winnerRid) >= 0) resultTxt += ' (Main hit)';
          else if (loosePickRids.indexOf(winnerRid) >= 0) resultTxt += ' (Loose hit)';
          tipParts.push(resultTxt);
        }
      } else {
        if (fsOk) tipParts.push('Field size ' + cellFs + ' (meets bet criteria)');
        else if (cellFs > 0) tipParts.push('Field size ' + cellFs + ' (below 8-runner threshold)');
      }
      if (tipParts.length) titleAttr = ' title="' + tipParts.join(' · ') + '"';

      html += '<div class="' + cellCls + '" data-rid="' + race.race_id + '"' + titleAttr + '>' +
        '<div class="mt-time">' + lbl + '</div>' + badge + '</div>';
    }
    html += '</div>';
  });
  html += '</div>';
  host.innerHTML = html;

  document.getElementById('race-date-info').textContent =
    meetings.length + ' meeting' + (meetings.length !== 1 ? 's' : '') + ' · ' +
    dateRaces.length + ' races';

  // Wire cell clicks
  host.querySelectorAll('.mt-race-cell[data-rid]').forEach(cell => {
    cell.addEventListener('click', () => {
      currentRaceId = cell.dataset.rid;
      showRaceDetail(currentRaceId);
    });
  });

  // Wire abandon-meeting button clicks
  host.querySelectorAll('[data-abandon-meeting]').forEach(btn => {
    btn.addEventListener('click', e => {
      e.stopPropagation();
      const [venue, date] = btn.dataset.abandonMeeting.split('|');
      const currentlyAbandoned = isMeetingAbandoned(venue, date);
      // Confirm before marking, to avoid accidental clicks on a long card.
      // Unmarking doesn't need a confirm - if it was a mistake the user
      // can re-mark trivially.
      if (!currentlyAbandoned) {
        const ok = confirm('Mark all races at ' + venue + ' on ' + date +
          ' as abandoned? This will hide their picks from Today/Quaddie.');
        if (!ok) return;
      }
      setMeetingAbandoned(venue, date, !currentlyAbandoned);
      renderMeetingsGrid();
      // Cascade to other tabs that filter on abandoned state.
      if (typeof renderToday === 'function') renderToday();
      if (typeof renderQuaddie === 'function') renderQuaddie();
    });
  });

  // Update date input
  const dateInput = document.getElementById('race-date-input');
  if (dateInput && dateInput.value !== currentBrowseDate) dateInput.value = currentBrowseDate;
  // Update active state on quick buttons
  const today = isoDate(0), yesterday = isoDate(-1), tomorrow = isoDate(1);
  document.querySelectorAll('.race-date-quick').forEach(b => {
    const k = b.dataset.rdate;
    let d = today;
    if (k === 'yesterday') d = yesterday;
    if (k === 'tomorrow') d = tomorrow;
    b.classList.toggle('active', d === currentBrowseDate);
  });
}

function showRaceDetail(raceId) {
  document.getElementById('race-browser').style.display = 'none';
  document.getElementById('race-detail').style.display = 'block';
  // Reset sort to Score (cumulative model score) ascending whenever a new
  // race is opened. Score rank 1 = best model pick, so asc = best first.
  // Previously this defaulted to TR rating rank which is now just one of
  // several inputs to Score; Score is the headline metric.
  raceSortState = { col: 'score', dir: 'asc' };
  renderRaceDetail(raceId);
}

// Helper: switch to Race tab and open a specific race. Used by the Today/P&L
// pick rows (clicking horse name jumps to the race detail) and the next-to-jump
// pills. Also sets the browse date to match the race so meeting strip is correct.
function navigateToRace(raceId) {
  if (!raceId) return;
  const race = RACES.find(r => String(r.race_id) === String(raceId));
  if (!race) return;
  document.querySelectorAll('.tab').forEach(x => x.classList.remove('active'));
  document.querySelectorAll('.section').forEach(x => x.classList.remove('active'));
  document.querySelector('.tab[data-tab="race"]').classList.add('active');
  document.getElementById('sec-race').classList.add('active');
  // Sync browse date so the meeting strip lines up
  if (race.date) currentBrowseDate = race.date;
  currentRaceId = raceId;
  showRaceDetail(raceId);
  // Scroll to top of the race detail since we may have scrolled deep into Today list
  window.scrollTo({ top: 0, behavior: 'instant' });
}

function exitRaceDetail() {
  document.getElementById('race-browser').style.display = 'block';
  document.getElementById('race-detail').style.display = 'none';
  currentRaceId = null;
}

// Race detail sort state - {column: name, dir: 'asc'|'desc'}
// Default: Score asc (best model pick first). showRaceDetail() resets this
// every time a new race is opened.
let raceSortState = { col: 'score', dir: 'asc' };

// Build a rich detail panel for a single runner inside the Race tab table.
// Triggered by clicking a row. Shows what the columns no longer carry: jockey,
// trainer, their ratings/strike rates, distance/going history, full PF context.
// Build the expanded runner-detail row HTML. Shown when user clicks a row.
// rankCtx (optional): { mid: {rid: rank}, total: {rid: rank} } so the
// detail panel can show Mid/Total speed score ranks inline with their values.
// Made these per-race ranks available because the Mid/Total columns were
// removed from the table to declutter - the detail panel now carries them.
function buildRaceRunnerDetailHTML(u, race, rankCtx) {
  function fld(label, value, cls) {
    if (value == null || value === '' || value === '—') return '';
    return '<div class="rd-field"><span class="rd-fl">' + label + '</span>' +
      '<span class="rd-fv ' + (cls || '') + '">' + value + '</span></div>';
  }
  function num(v, dp) {
    if (v == null) return null;
    return Number(v).toFixed(dp == null ? 1 : dp);
  }

  // Connections section
  const jkyHtml = u.j ? escapeHtml(u.j) +
    (u.jrt != null ? ' <span style="color:var(--ink-mute);">(rt ' + Math.round(u.jrt) + ')</span>' : '') +
    (u.jw != null ? ' · ' + u.jw.toFixed(0) + '% 90d' : '') : null;
  const trnHtml = u.tn ? escapeHtml(u.tn) +
    (u.trt != null ? ' <span style="color:var(--ink-mute);">(rt ' + Math.round(u.trt) + ')</span>' : '') +
    (u.tw != null ? ' · ' + u.tw.toFixed(0) + '% 365d' : '') : null;

  // Form section
  const wprStr = u.wpr1 != null ?
    Math.round(u.wpr1) + (u.wpra != null ? ' · avg ' + Math.round(u.wpra) : '') +
    (u.wprt != null ? ' · ' + (u.wprt > 0 ? '↑' : '↓') + Math.abs(u.wprt).toFixed(1) : '') : null;
  let goingPerf = null;
  if (race && race.going && u.gb) {
    const gl = race.going.toLowerCase();
    let key = null;
    if (gl.startsWith('firm')) key = 'firm';
    else if (gl.startsWith('good')) key = 'good';
    else if (gl.startsWith('soft')) key = 'soft';
    else if (gl.startsWith('heavy')) key = 'heavy';
    if (key && u.gb[key] && u.gb[key].starts) {
      const g = u.gb[key];
      goingPerf = (g.wins||0) + 'W ' + Math.max(0, (g.places||0) - (g.wins||0)) + 'P from ' + g.starts + ' starts';
    }
  }
  // Wet-track form (Soft + Heavy combined). Surfaced only on Soft/Heavy
  // days, matching the Today/P&L panel behaviour. Mirrors the analysis
  // finding that Soft form transfers usefully to Heavy.
  let wetPerf = null;
  if (race && race.going && u.gb) {
    const gl = race.going.toLowerCase();
    if (gl.startsWith('soft') || gl.startsWith('heavy')) {
      const soft  = u.gb.soft  || {};
      const heavy = u.gb.heavy || {};
      const s_starts = (soft.starts  || 0) + (heavy.starts  || 0);
      const s_wins   = (soft.wins    || 0) + (heavy.wins    || 0);
      const s_places = (soft.places  || 0) + (heavy.places  || 0);
      if (s_starts > 0) {
        wetPerf = s_wins + 'W ' + Math.max(0, s_places - s_wins) +
                  'P from ' + s_starts + ' starts';
      } else {
        wetPerf = 'no wet runs';
      }
    }
  }
  const distPerf = (u.ds && u.ds > 0) ?
    (u.dw||0) + 'W ' + Math.max(0, (u.dp||0) - (u.dw||0)) + 'P from ' + u.ds + ' starts' : null;

  // PF section - all fields when present
  const pfReliable = u.pfaiR != null ? '<span style="color:var(--emerald-deep);font-weight:600;">✓</span>' : '';
  const pfAiHtml = u.pfaiR != null ? '#' + u.pfaiR : null;
  const pfClassHtml = u.wcR != null ?
    '#' + u.wcR + (u.tacwcR != null ? ' (adj #' + u.tacwcR + ')' : '') : null;
  const pfTimeHtml = u.tR != null ? '#' + u.tR : null;
  const pfEarlyHtml = u.etR != null ? '#' + u.etR : null;
  const pfL600Html  = u.l600R != null ? '#' + u.l600R : null;
  const pfL400Html  = u.l400R != null ? '#' + u.l400R : null;
  const pfL200Html  = u.l200R != null ? '#' + u.l200R : null;
  const pfStyleHtml = u.rs ?
    '<span style="text-transform:uppercase;font-weight:600;">' + escapeHtml(u.rs) + '</span>' : null;
  const pfClsChgHtml = (u.clsChg != null && u.clsChg !== 0) ?
    (u.clsChg > 0 ? '<span style="color:var(--emerald-deep);font-weight:700;">↑ up ' + u.clsChg + '</span>' :
     '<span style="color:#dc2626;font-weight:700;">↓ down ' + Math.abs(u.clsChg) + '</span>') : null;

  // TR signals - we keep speed rating only (TR price, Early speed removed per design)
  const trSpd = u.spd != null ? Math.round(u.spd) : null;

  // Mid/Total speed scores - moved here from the runners table to declutter
  // the table. Shows value with rank if rankCtx provided, otherwise just value.
  function speedScoreHtml(value, rank) {
    if (value == null) return null;
    const valStr = Number(value).toFixed(1);
    if (rank != null) {
      const rkCls = rank === 1 ? 'r1' : (rank === 2 ? 'r2' : (rank === 3 ? 'r3' : ''));
      return valStr + ' <span class="rd-rank-pill ' + rkCls + '">#' + rank + '</span>';
    }
    return valStr;
  }
  const midRank   = (rankCtx && rankCtx.mid)   ? rankCtx.mid[u.rid]   : null;
  const totalRank = (rankCtx && rankCtx.total) ? rankCtx.total[u.rid] : null;
  const midHtml   = speedScoreHtml(u.ms, midRank);
  const totalHtml = speedScoreHtml(u.ts, totalRank);

  // Weight
  const wtHtml = u.wt != null ?
    u.wt + 'kg' + (u.wtr != null ? ' · ' + (u.wtr > 0 ? '+' : '') + u.wtr.toFixed(1) + 'kg trend' : '') : null;

  // Pre/post-race prices section. Fxd is live (always populated when book is
  // open), TF and SP are filled when results sync. Showing them together lets
  // the user see how the market moved on this runner.
  const fxStr  = u.fx  != null ? '$' + u.fx.toFixed(2)  : '—';
  const tfStr  = u.top != null ? '$' + u.top.toFixed(2) : '— post-race';
  const spStrR = u.sp  != null ? '$' + u.sp.toFixed(2)  : '— post-race';
  const trpStr = u.trp != null ? '$' + u.trp.toFixed(2) : null;

  return '<div class="rd-runner-detail">' +
    '<div class="rd-section">' +
      '<div class="rd-section-title">Prices</div>' +
      '<div class="rd-section-body">' +
        fld('Fixed', fxStr) +
        fld('Top Fluc', tfStr) +
        fld('SP', spStrR) +
        fld('TR price', trpStr) +
      '</div>' +
    '</div>' +
    '<div class="rd-section">' +
      '<div class="rd-section-title">Connections</div>' +
      '<div class="rd-section-body">' +
        fld('Jockey', jkyHtml) +
        fld('Trainer', trnHtml) +
        fld('Barrier', u.b != null ? String(u.b) : null) +
        fld('Weight', wtHtml) +
      '</div>' +
    '</div>' +
    '<div class="rd-section">' +
      '<div class="rd-section-title">Recent form</div>' +
      '<div class="rd-section-body">' +
        fld('Form', u.fm ? escapeHtml(u.fm) : null) +
        fld('Recent WPR', wprStr) +
        fld('Distance perf', distPerf) +
        fld('Going perf', goingPerf) +
        fld('Wet form', wetPerf) +
      '</div>' +
    '</div>' +
    '<div class="rd-section">' +
      '<div class="rd-section-title">Signals ' + pfReliable + '</div>' +
      '<div class="rd-section-body">' +
        fld('Speed rating', trSpd) +
        fld('Mid speed', midHtml) +
        fld('Total speed', totalHtml) +
        fld('PF AI', pfAiHtml) +
        fld('Time rank', pfTimeHtml) +
        fld('Class rank', pfClassHtml) +
        fld('Early sect', pfEarlyHtml) +
        fld('L600 sect', pfL600Html) +
        fld('L400 sect', pfL400Html) +
        fld('L200 sect', pfL200Html) +
        fld('Run style', pfStyleHtml) +
        fld('Class change', pfClsChgHtml) +
      '</div>' +
    '</div>' +
  '</div>';
}

function renderRaceDetail(raceId) {
  const race = RACES.find(r => String(r.race_id) === String(raceId));
  if (!race) {
    document.getElementById('rd-title').textContent = 'Race not found';
    return;
  }
  const racePicksLookup = MODEL_PICKS[raceId] || {};
  const picks = racePicksLookup[PRIMARY_KEY] || [];
  const loosePicks = racePicksLookup['loose'] || [];
  const pickIds = new Set(picks.map(p => String(p.run_id)));
  const looseIds = new Set(loosePicks.map(p => String(p.run_id)));
  const runners = race.runners || [];

  // ── PF data freshness indicator ──
  // Show a banner when PF didn't rate this meeting (no picks possible) or
  // when only some runners have PF data (partial coverage).
  (function updatePfBar() {
    const bar = document.getElementById('rd-pf-freshness');
    if (!bar) return;
    const total = runners.length;
    const withPf = runners.filter(u => u.pfaiR != null).length;
    bar.className = 'pf-freshness-bar';
    bar.style.display = '';
    if (total === 0) {
      bar.style.display = 'none';
      return;
    }
    if (withPf === 0) {
      bar.classList.add('error');
      bar.innerHTML = '<span class="pf-label">⚠ Punting Form data missing</span>' +
        'No PF ratings for this meeting. Model picks unavailable.';
    } else if (withPf < total) {
      bar.classList.add('warn');
      bar.innerHTML = '<span class="pf-label">PF data partial</span>' +
        withPf + ' of ' + total + ' runners rated by Punting Form. ' +
        'Model picks may be incomplete.';
    } else {
      // Full coverage - hide
      bar.style.display = 'none';
    }
  })();

  // ── Meeting jump strip - all races at this venue on this date ──
  // Filter all RACES to same venue+date, sort by race number
  const meetingRaces = RACES.filter(r =>
    r.venue === race.venue && r.date === race.date
  ).sort((a, b) => (a.race || 0) - (b.race || 0));

  function cdClass(secondsToStart) {
    if (secondsToStart === null || secondsToStart === undefined) return '';
    if (secondsToStart < 0 && secondsToStart > -180) return 'cd-live';   // running now
    if (secondsToStart >= 0 && secondsToStart < 180) return 'cd-imminent'; // <3min
    if (secondsToStart >= 180 && secondsToStart < 900) return 'cd-soon';   // <15min
    return '';
  }
  function fmtCd(secondsToStart) {
    if (secondsToStart === null || secondsToStart === undefined) return '';
    if (secondsToStart < 0 && secondsToStart > -300) return 'LIVE';
    if (secondsToStart < 0) return '';  // already finished
    const m = Math.floor(secondsToStart / 60);
    if (m < 60) return m + 'm';
    return Math.floor(m / 60) + 'h ' + (m % 60) + 'm';
  }

  // Extract a short class label from race name
  // Examples: "Ladbrokes BM65 Handicap" -> "BM65", "Mdn Plate" -> "Maiden",
  //           "Group 1 Cox Plate" -> "G1", "Class 1 Hcp" -> "C1"
  function shortClass(raceName) {
    if (!raceName) return '';
    const n = raceName.toUpperCase();
    // Group races
    let m = n.match(/GROUP\s*([1-3])\b/);
    if (m) return 'G' + m[1];
    // Listed
    if (/\bLISTED\b/.test(n)) return 'LR';
    // BMxx benchmark
    m = n.match(/\bBM\s*(\d{2,3})\b/);
    if (m) return 'BM' + m[1];
    // Class x
    m = n.match(/\bCLASS\s*(\d|[A-Z])\b/);
    if (m) return 'C' + m[1];
    // Maiden
    if (/\bMDN\b|\bMAIDEN\b/.test(n)) return 'Maiden';
    // Restricted
    m = n.match(/\bRTG\s*(\d{2,3})/);
    if (m) return 'RTG' + m[1];
    // Open / Welter / Hcp / Plate
    if (/\bOPEN\b/.test(n)) return 'Open';
    if (/\bWELTER\b/.test(n)) return 'Welter';
    // Set Weight / WFA
    if (/\bWFA\b|\bSET\s*WEIGHT/.test(n)) return 'WFA';
    return '';  // unknown - leave blank
  }

  const nowMs = Date.now();
  const stripHtml =
    '<div class="meeting-strip-label">' + escapeHtml(race.venue) + '</div>' +
    meetingRaces.map(r => {
      const racePicks = (MODEL_PICKS[r.race_id] || {});
      const rPicks = racePicks[PRIMARY_KEY] || [];
      const hasPick = rPicks.length > 0;
      const hasLoose = !!(racePicks['loose'] || []).length;
      const isActive = String(r.race_id) === String(raceId);
      const isDone = r.done === 1;
      const startMs = r.start_time ? new Date(r.start_time).getTime() : null;
      const secs = startMs ? Math.floor((startMs - nowMs) / 1000) : null;
      const cdcls = cdClass(secs);
      const cdtxt = fmtCd(secs);
      let timeStr = '';
      if (r.start_time) {
        const dt = new Date(r.start_time);
        timeStr = dt.toLocaleTimeString('en-AU', {hour: '2-digit', minute: '2-digit', hour12: false});
      }
      const cls = ['meeting-tile'];
      if (isActive) cls.push('active');
      if (hasPick) cls.push('has-pick'); else cls.push('no-pick');
      if (hasLoose) cls.push('has-loose-pick');
      if (isDone) cls.push('done');
      const cdHtml = (cdtxt && !isDone) ? '<span class="mt-cd ' + cdcls + '">' + cdtxt + '</span>' : '';
      // Build info line: "1400m · Maiden" or just "1400m" if class unknown
      const infoParts = [];
      if (r.distance) infoParts.push(r.distance + 'm');
      const cls2 = shortClass(r.race_name);
      if (cls2) infoParts.push(cls2);
      const infoLine = infoParts.join(' · ');
      return '<div class="' + cls.join(' ') + '" data-race-id="' + r.race_id + '">' +
        '<span class="mt-race">R' + r.race + cdHtml + '</span>' +
        '<span class="mt-time">' + timeStr + '</span>' +
        (infoLine ? '<span class="mt-info">' + escapeHtml(infoLine) + '</span>' : '') +
        '</div>';
    }).join('');
  const stripEl = document.getElementById('rd-meeting-strip');
  stripEl.innerHTML = stripHtml;
  // Wire click handlers
  stripEl.querySelectorAll('.meeting-tile').forEach(tile => {
    tile.addEventListener('click', () => {
      const rid = tile.dataset.raceId;
      if (rid && rid !== String(raceId)) {
        showRaceDetail(rid);
      }
    });
  });

  // ── First-starter banner ──
  const banner = document.getElementById('rd-banner');
  if (race.hfs) {
    banner.innerHTML =
      '<span class="icon">⚠</span>' +
      '<div>' +
        '<div class="text">First starter in this race</div>' +
        '<div class="sub">Model signals do not apply to debut runners. Recommend skipping this race.</div>' +
      '</div>';
    banner.style.display = 'flex';
  } else {
    banner.style.display = 'none';
    banner.innerHTML = '';
  }

  // ── Pre-race pace estimate (settling-position derived) ──
  let leaders = 0, onpace = 0, midfield = 0, back = 0;
  runners.forEach(u => {
    const pos = u.asp;
    if (pos == null) return;
    if (pos <= 2) leaders++;
    else if (pos <= 4) onpace++;
    else if (pos <= 8) midfield++;
    else back++;
  });
  let paceEst = 'even', paceLabel = 'Even';
  if (leaders >= 3) { paceEst = 'hot'; paceLabel = 'Hot pace'; }
  else if (leaders >= 2 && onpace >= 2) { paceEst = 'fast'; paceLabel = 'Fast'; }
  else if (leaders <= 1 && (midfield + back) >= 4) { paceEst = 'slow'; paceLabel = 'Slow'; }

  let paceFromShape = null;
  if (race.rse != null) {
    if (race.rse > 0.15) paceFromShape = 'Fast early';
    else if (race.rse < -0.15) paceFromShape = 'Slow early';
    else paceFromShape = 'Even pace';
  }
  const paceDisplay = paceFromShape || (paceLabel + ' (est)');
  const paceClass = paceFromShape ? '' : paceEst;

  // ── Header ──
  document.getElementById('rd-title').textContent = race.venue + ' · R' + race.race;
  document.getElementById('rd-subtitle').textContent = race.race_name || '';

  // Adaptive selection: horses meeting the cumulative-score threshold
  // The threshold setting drives picks per race - more in open races, fewer
  // in races with a clear favourite.
  const thresh = (settings && settings.scoreThreshold != null) ? settings.scoreThreshold : 0.55;
  const qualifiers = runners.filter(u => u.cs != null && u.cs >= thresh)
    .sort((a, b) => (a.crk || 99) - (b.crk || 99));
  let scoreThreshHtml = '';
  if (qualifiers.length > 0) {
    scoreThreshHtml =
      '<div class="score-top3" title="Horses with cumulative score >= ' + thresh.toFixed(2) +
        ' (adjustable in Settings). Used by Quaddie tab.">' +
        '<span class="lbl">' + qualifiers.length + ' above ' + thresh.toFixed(2) + '</span>' +
        '<span class="tabs">' +
          qualifiers.slice(0, 6).map(u => '<span class="tab-num">#' + (u.tab || '?') + '</span>').join('') +
          (qualifiers.length > 6 ? '<span class="tab-num">+' + (qualifiers.length - 6) + '</span>' : '') +
        '</span>' +
      '</div>';
  } else {
    scoreThreshHtml =
      '<div class="score-top3 no-quals" title="No horses meet the score threshold of ' + thresh.toFixed(2) + '. Skip this leg or lower the threshold.">' +
        '<span class="lbl">0 above ' + thresh.toFixed(2) + '</span>' +
      '</div>';
  }

  // Pick count display in header stats - shows Main count plus Loose if it
  // also picked. Reads "1 model pick" or "1 Main · 2 Loose picks" so the
  // user can see both models' picks at a glance from the race header.
  let picksDisplay;
  if (picks.length === 0 && loosePicks.length === 0) {
    picksDisplay = '<span class="v">0</span> model picks';
  } else if (loosePicks.length === 0) {
    picksDisplay = '<span class="v">' + picks.length + '</span> Main pick' +
      (picks.length !== 1 ? 's' : '');
  } else if (picks.length === 0) {
    picksDisplay = '<span class="v">' + loosePicks.length + '</span> Loose pick' +
      (loosePicks.length !== 1 ? 's' : '');
  } else {
    picksDisplay = '<span class="v">' + picks.length + '</span> Main · ' +
      '<span class="v">' + loosePicks.length + '</span> Loose';
  }
  // Race-level abandon toggle. Distinct from meeting-level (which lives on
  // the meetings grid) - this is for edge cases where one race is called
  // off but the rest of the card runs. If the meeting is already marked
  // abandoned, the race inherits it; the button text reflects this.
  const raceAbandoned = isRaceAbandoned(race);
  const meetingAbandoned = isMeetingAbandoned(race.venue, race.date);
  let abandonHtml;
  if (meetingAbandoned) {
    // Meeting-level mark - cannot un-mark just this race here. Direct user
    // to the Race tab meetings grid.
    abandonHtml = '<div class="item rd-abandon-item is-meeting-abandoned" ' +
      'title="Whole meeting marked abandoned. Unmark on the meetings grid.">' +
      'MEETING ABANDONED</div>';
  } else if (raceAbandoned) {
    abandonHtml = '<button type="button" class="rd-abandon-btn is-on" ' +
      'id="rd-abandon-btn" title="Click to unmark this race.">' +
      'Race abandoned ✓</button>';
  } else {
    abandonHtml = '<button type="button" class="rd-abandon-btn" ' +
      'id="rd-abandon-btn" title="Mark this race abandoned. Hides its picks ' +
      'from Today/Quaddie.">Mark race abandoned</button>';
  }
  document.getElementById('rd-header-stats').innerHTML =
    '<div class="item">' + fmtTime(race.start_time) + '</div>' +
    '<div class="item">' + race.distance + 'm</div>' +
    '<div class="item">' + escapeHtml(race.going || '') + '</div>' +
    '<div class="item">$' + (race.prize/1000).toFixed(0) + 'k</div>' +
    '<div class="item">' + runners.length + ' runners</div>' +
    '<div class="item">' + picksDisplay + '</div>' +
    scoreThreshHtml +
    '<div class="race-pace-est ' + paceClass + '"><span class="lbl">Pace</span>' + paceDisplay + '</div>' +
    abandonHtml;

  // Context bar - includes inline track rating override
  const ctx = [];
  ctx.push({ lbl: 'Distance', v: race.distance + 'm' });
  ctx.push({ lbl: 'Going', v: getEffectiveGoing(race) || '—', overridden: !!getRaceTrackRating(race) });
  if (race.rail) ctx.push({ lbl: 'Rail', v: race.rail });
  ctx.push({ lbl: 'Prize', v: '$' + (race.prize / 1000).toFixed(0) + 'k' });
  ctx.push({ lbl: 'Field', v: runners.length });
  const currentOverride = getRaceTrackRating(race) || '';
  const overrideInput =
    '<div class="ctx-item ctx-override-inline">' +
      '<span class="ctx-lbl">Override</span>' +
      '<input type="text" class="ctx-override-input" id="ctx-override-input" ' +
        'placeholder="e.g. Soft 6" value="' + escapeHtml(currentOverride) + '" maxlength="20"/>' +
      (currentOverride ? '<button class="ctx-override-clear" id="ctx-override-clear" title="Clear override">×</button>' : '') +
    '</div>';
  document.getElementById('rd-context-bar').innerHTML =
    ctx.map(c => {
      const cls = c.overridden ? 'ctx-item ctx-overridden' : 'ctx-item';
      return '<div class="' + cls + '">' + c.lbl + '<span class="ctx-v">' + escapeHtml(String(c.v)) + '</span></div>';
    }).join('') + overrideInput;

  // Wire the inline override input
  wireContextOverride(race);

  // Wire race-level abandon toggle (rendered in rd-header-stats above).
  // Only present when meeting isn't already marked abandoned.
  const rdAbandonBtn = document.getElementById('rd-abandon-btn');
  if (rdAbandonBtn) {
    rdAbandonBtn.addEventListener('click', () => {
      const currentlyOn = isRaceAbandoned(race) && !isMeetingAbandoned(race.venue, race.date);
      if (!currentlyOn) {
        const ok = confirm('Mark this race as abandoned? It will be hidden ' +
          'from Today/Quaddie picks.');
        if (!ok) return;
      }
      setRaceAbandoned(race.race_id, !currentlyOn);
      renderRaceDetail(race.race_id);
      if (typeof renderMeetingsGrid === 'function') renderMeetingsGrid();
      if (typeof renderToday === 'function') renderToday();
      if (typeof renderQuaddie === 'function') renderQuaddie();
    });
  }

  // ── Pace map / race shape ──
  // Horizontal lane diagram: Leaders left → Back right. Horses positioned in
  // their predicted zone based on avg_settled_pos. Tab numbers shown in colored
  // cells. Unknown asp goes into a "no data" pile at the right.
  const settled = { leaders: [], onpace: [], midfield: [], back: [], unknown: [] };
  runners.forEach(u => {
    const pos = u.asp;
    if (pos == null) settled.unknown.push(u);
    else if (pos <= 2) settled.leaders.push(u);
    else if (pos <= 4) settled.onpace.push(u);
    else if (pos <= 8) settled.midfield.push(u);
    else settled.back.push(u);
  });
  // Within each zone, sort by asp ascending so closer-to-front horses go first
  Object.keys(settled).forEach(k => {
    if (k === 'unknown') return;
    settled[k].sort((a, b) => (a.asp || 99) - (b.asp || 99));
  });
  document.getElementById('rd-pace-map').innerHTML =
    '<div class="race-shape-wrap">' +
      renderRaceShapeSVG(settled, runners.length, paceDisplay, paceClass, race, runners) +
    '</div>';
  // Track conditions card - weather/going/rail + how-this-track-plays commentary
  // computed from historical races at same venue/going/rail
  document.getElementById('rd-track-conditions').innerHTML = renderTrackConditions(race);
  wireTrackConditionsCard(race);

  // PF barrier x runstyle A2E grid. Sits below the venue-bias chart. Panel
  // is hidden when there's no PF data for this venue (e.g. ingest hasn't
  // run yet, or the meeting isn't in pf_barrier_bias.csv) - no orphan title.
  const pfBiasEl = document.getElementById('rd-pf-bias');
  if (pfBiasEl) {
    const pfBiasHtml = renderPfBarrierBias(race);
    if (pfBiasHtml) {
      pfBiasEl.innerHTML = pfBiasHtml;
      pfBiasEl.style.display = '';
    } else {
      pfBiasEl.innerHTML = '';
      pfBiasEl.style.display = 'none';
    }
  }

  // ── Compute ranks ──
  function computeRanks(runners, getter) {
    const valid = runners.filter(r => getter(r) != null);
    valid.sort((a, b) => getter(b) - getter(a));
    const ranks = {};
    valid.forEach((r, i) => { ranks[r.rid] = i + 1; });
    return ranks;
  }
  const trRanks    = computeRanks(runners, r => r.trr);
  const wprRanks   = computeRanks(runners, r => r.w);
  const earlyRanks = computeRanks(runners, r => r.es);
  const midRanks   = computeRanks(runners, r => r.ms);
  const lateRanks  = computeRanks(runners, r => r.ls);
  const totalRanks = computeRanks(runners, r => r.ts);

  // Going category
  function goingCategory(g) {
    if (!g) return null;
    const gl = g.toLowerCase();
    if (gl.startsWith('firm')) return 'firm';
    if (gl.startsWith('good')) return 'good';
    if (gl.startsWith('soft')) return 'soft';
    if (gl.startsWith('heavy')) return 'heavy';
    if (gl.startsWith('synth')) return 'synth';
    return null;
  }
  const todayGoing = goingCategory(getEffectiveGoing(race));

  // Show going column only if at least one runner has going history for today's surface.
  // Otherwise the column wastes horizontal space showing all dashes.
  const showGoing = todayGoing && runners.some(u =>
    u.gb && u.gb[todayGoing] && u.gb[todayGoing].starts > 0
  );

  // Build cell helpers
  function sectCell(value, rank) {
    if (value == null) return '<td class="sect-cell">—</td>';
    const rkCls = rank === 1 ? 'r1' : (rank === 2 ? 'r2' : (rank === 3 ? 'r3' : ''));
    const rkBadge = rank ? '<span class="rk">#' + rank + '</span>' : '';
    return '<td class="sect-cell ' + rkCls + '"><span class="v">' + value.toFixed(1) + '</span>' + rkBadge + '</td>';
  }

  // Cumulative-score cell. score is 0..1, rank is within-race position (1 = best)
  function scoreCell(score, rank, conf) {
    if (score == null || rank == null) return '<td class="score-cell">—</td>';
    const rkCls = rank === 1 ? 'r1' : (rank === 2 ? 'r2' : (rank === 3 ? 'r3' : ''));
    let confDot = '';
    if (conf != null) {
      const dotCls = conf >= 0.80 ? 'high' : (conf >= 0.50 ? 'mid' : 'low');
      const confLbl = conf >= 0.80 ? 'unanimous' : conf >= 0.50 ? 'mixed' : 'split';
      confDot = ' <span class="conf-dot ' + dotCls + '" title="Signal confidence ' +
        Math.round(conf * 100) + '% - ' + confLbl + '"></span>';
    }
    return '<td class="score-cell ' + rkCls + '" title="Predictive composite (TR + form + late-speed). Rank ' + rank + ' in field.">' +
      '<span class="v">' + score.toFixed(2) + '</span>' +
      '<span class="rk">#' + rank + '</span>' + confDot +
      '</td>';
  }

  // WPR cell - shows the rating value plus its within-race rank, mirroring scoreCell layout.
  function wprCell(value, rank) {
    if (value == null) return '<td class="score-cell">—</td>';
    const rkCls = rank === 1 ? 'r1' : (rank === 2 ? 'r2' : (rank === 3 ? 'r3' : ''));
    const rkBadge = rank ? '<span class="rk">#' + rank + '</span>' : '';
    const title = rank ? 'WPR rating. Rank ' + rank + ' in field.' : 'WPR rating';
    return '<td class="score-cell ' + rkCls + '" title="' + title + '">' +
      '<span class="v">' + Math.round(value) + '</span>' + rkBadge +
      '</td>';
  }

  // PF rank cell - PF rank is already a within-race rank (1 = best). Displays
  // just the rank number with the same colour-coding as sectCell.
  // Used for pfaiR, wcR, l600R, l400R columns.
  function pfRankCell(rank, label) {
    if (rank == null) return '<td class="sect-cell">—</td>';
    const r = Math.round(rank);
    const rkCls = r === 1 ? 'r1' : (r === 2 ? 'r2' : (r === 3 ? 'r3' : ''));
    return '<td class="sect-cell ' + rkCls + '" title="' + label + ' rank ' + r + '">' +
      '<span class="v">' + r + '</span></td>';
  }

  // PF run-style cell - shows the run-style code (l/op/mf/bm etc). Coloured
  // by category: leaders=amber, on-pace=green, mid=blue, back=pink. Mirrors
  // the race-shape SVG zones.
  function pfRunStyleCell(rs) {
    if (!rs) return '<td>—</td>';
    let color = 'var(--ink-mute)';
    let bg = 'transparent';
    const s = String(rs).trim().toLowerCase();
    if (s === 'l')              { bg = '#fef3c7'; color = '#92400e'; }
    else if (s.startsWith('op')) { bg = '#d1fae5'; color = '#064e3b'; }
    else if (s.startsWith('mf') && !s.includes('bm')) { bg = '#dbeafe'; color = '#1e3a8a'; }
    else if (s.includes('bm') || s === 'bm')     { bg = '#fce7f3'; color = '#831843'; }
    else if (s === 'no data')   { return '<td style="color:var(--ink-faint);">—</td>'; }
    return '<td><span style="background:' + bg + ';color:' + color +
      ';padding:2px 6px;border-radius:3px;font-size:11px;font-weight:600;text-transform:uppercase;">' +
      s + '</span></td>';
  }

  // PF class-change cell - shows the class delta as up/down arrow.
  function pfClassChgCell(chg) {
    if (chg == null || chg === 0) return '<td style="color:var(--ink-faint);">—</td>';
    const arrow = chg > 0 ? '↑' : '↓';
    const color = chg > 0 ? 'var(--emerald-deep)' : '#dc2626';
    return '<td style="color:' + color + ';font-weight:700;">' + arrow + ' ' + Math.abs(chg) + '</td>';
  }

  // Distance perf cell - format: "starts: wins | places"
  // Color: green if win rate >= 25%, amber if 10-24%, default if <10%, faint if no history
  function perfCell(starts, wins, places, dnf) {
    if (!starts || starts === 0) {
      return '<td style="color:var(--ink-faint);">—</td>';
    }
    const winPct = wins / starts;
    let color = '';
    if (winPct >= 0.25) color = 'color:var(--emerald-deep);font-weight:700;';
    else if (winPct >= 0.10) color = 'color:#92400e;font-weight:600;';
    const tooltip = wins + 'W ' + Math.max(0, places - wins) + 'P from ' + starts + ' starts';
    return '<td title="' + tooltip + '" style="' + color + 'font-variant-numeric:tabular-nums;">' +
      starts + ': ' + wins + ' | ' + places + '</td>';
  }

  function distanceCell(runner) {
    return perfCell(runner.ds, runner.dw, runner.dp);
  }

  function goingCell(runner) {
    if (!todayGoing || !runner.gb || !runner.gb[todayGoing]) {
      return '<td style="color:var(--ink-faint);">—</td>';
    }
    const g = runner.gb[todayGoing];
    return perfCell(g.starts, g.wins, g.places);
  }

  function settlesLabel(asp) {
    if (asp == null) return '—';
    if (asp <= 2.5) return '<span style="color:var(--emerald-deep);font-weight:600;">Lead</span>';
    if (asp <= 4.5) return 'On-pace';
    if (asp <= 8.5) return 'Mid';
    return '<span style="color:var(--ink-faint);">Back</span>';
  }

  function rateClass(pct) {
    if (pct == null) return '';
    if (pct >= 18) return 'high';
    if (pct >= 11) return 'mid';
    return '';
  }

  // For TopRate's own jky/trn ratings: color by rank within the field (top 3 = high, 4-6 = mid)
  const jryRanks = computeRanks(runners, r => r.jrt);
  const tryRanks = computeRanks(runners, r => r.trt);

  function ratingClass(rank) {
    if (rank == null) return '';
    if (rank <= 3) return 'high';
    if (rank <= 6) return 'mid';
    return '';
  }

  function ratingCell(value, rank) {
    if (value == null) return '<td class="rate-cell">—</td>';
    return '<td class="rate-cell ' + ratingClass(rank) + '" title="Rank ' + rank + ' in field">' +
      value.toFixed(0) + '</td>';
  }

  // ── Sorting ──
  // Each sortable column has a getter; null/undef sorts last
  const sortGetters = {
    tab:   r => r.tab,
    horse: r => (r.h || '').toLowerCase(),
    jky:   r => (r.j || '').toLowerCase(),
    jkypc: r => r.jrt,
    trn:   r => (r.tn || '').toLowerCase(),
    trnpc: r => r.trt,
    bar:   r => r.b,
    tr:    r => trRanks[r.rid] || 99,
    wpr:   r => wprRanks[r.rid] || 99,
    early: r => earlyRanks[r.rid] || 99,
    mid:   r => midRanks[r.rid] || 99,
    late:  r => lateRanks[r.rid] || 99,
    total: r => totalRanks[r.rid] || 99,
    dist:  r => (r.ds && r.dw != null) ? (r.dw / r.ds) : -1,
    going: r => {
      if (!todayGoing || !r.gb || !r.gb[todayGoing]) return -1;
      const g = r.gb[todayGoing];
      return g.starts ? (g.wins / g.starts) : -1;
    },
    settles: r => r.asp != null ? r.asp : 99,
    fxd:   r => r.fx || 9999,
    trp:   r => r.trp || 9999,
    score: r => r.crk != null ? r.crk : 99,  // sort by rank ascending (1 = best)
    // Votes sort: compute on the fly using the same 6-signal logic as the
    // row. Higher count = stronger pick; negate so default desc = highest first.
    votes: r => {
      const tr = (typeof trRanks !== 'undefined') ? trRanks[r.rid] : null;
      const w = (typeof wprRanks !== 'undefined') ? wprRanks[r.rid] : null;
      const la = (typeof lateRanks !== 'undefined') ? lateRanks[r.rid] : null;
      const top3 =
        ((w != null && w <= 3) ? 1 : 0) +
        ((la != null && la <= 3) ? 1 : 0) +
        ((r.wcR != null && r.wcR <= 3) ? 1 : 0) +
        ((r.l600R != null && r.l600R <= 3) ? 1 : 0) +
        ((r.pfaiR != null && r.pfaiR <= 3) ? 1 : 0) +
        ((tr != null && tr <= 3) ? 1 : 0);
      return -top3;  // negate so default ASC sort = lowest top3 first
    },
    // PF columns sort ascending (1 = best PF rank)
    pfai:    r => r.pfaiR != null ? r.pfaiR : 99,
    wcR:     r => r.wcR != null ? r.wcR : 99,
    l600R:   r => r.l600R != null ? r.l600R : 99,
    l400R:   r => r.l400R != null ? r.l400R : 99,
    rs:      r => (r.rs || 'zz').toLowerCase(),  // sort alphabetic
    clsChg:  r => r.clsChg != null ? -r.clsChg : 0,  // class UP first when desc
  };

  const sortedRunners = runners.slice().sort((a, b) => {
    const getter = sortGetters[raceSortState.col] || sortGetters.tr;
    let aVal = getter(a), bVal = getter(b);
    // Nulls sort last regardless of direction
    if (aVal == null || aVal === '') return 1;
    if (bVal == null || bVal === '') return -1;
    let cmp;
    if (typeof aVal === 'string') cmp = aVal.localeCompare(bVal);
    else cmp = aVal - bVal;
    return raceSortState.dir === 'desc' ? -cmp : cmp;
  });

  let rowsHtml = '';
  sortedRunners.forEach(u => {
    const rid = u.rid;
    const isPick = pickIds.has(String(rid));
    const isLoose = looseIds.has(String(rid));
    const trR = trRanks[rid];
    const trClass = trR === 1 ? 'r1' : (trR === 2 ? 'r2' : (trR === 3 ? 'r3' : ''));
    const fxp = u.fx;
    const trp = u.trp;
    // Score-threshold flag - adds emerald row tint for adaptive selection
    const qualifies = u.cs != null && u.cs >= thresh;

    const rowClasses = [];
    if (isPick) rowClasses.push('is-pick');
    else if (isLoose) rowClasses.push('is-loose-pick');
    else if (trR > 5) rowClasses.push('muted');
    if (qualifies) rowClasses.push('score-qualify');

    // Pick badge - compact letter indicator AFTER the horse name. Two badges
    // can show together when both models pick the same horse:
    //   - Main pick: green "M"
    //   - Loose pick: amber "L"
    //   - Both: green "M" + amber "L" side by side
    let pickBadge = '';
    if (isPick) {
      pickBadge += '<span class="pick-badge pick-badge-main" title="Main model pick">M</span>';
    }
    if (isLoose) {
      pickBadge += '<span class="pick-badge pick-badge-loose" title="Loose model pick">L</span>';
    }

    // Finish-position indicators - only when the race is resulted and we
    // have a finish for this runner. Adds:
    //   1. A 'finish-N' class on the row so CSS can tint winner/placegetter rows
    //   2. A position badge ("1st"/"2nd"/"3rd"/Nth) before the horse name
    // u.f comes from finish_position on the runner payload (null pre-race).
    let finishBadge = '';
    if (u.f != null) {
      const f = parseInt(u.f, 10);
      if (!isNaN(f) && f > 0) {
        rowClasses.push('finish-' + (f <= 3 ? f : 'other'));
        let label = f + 'th';
        if (f === 1) label = '1st';
        else if (f === 2) label = '2nd';
        else if (f === 3) label = '3rd';
        finishBadge = '<span class="finish-badge finish-badge-' +
          (f <= 3 ? f : 'other') + '">' + label + '</span>';
      }
    }

    // Vote counts - the Votes column shows N/6 top-3 hits with a star
    // indicator for #1-vote density. Same six signals as the model rule
    // (WPR, Late, PF Class, PF L600, PF AI, TR).
    // (Note: trR already declared above for muted-row check.)
    const csR = u.crk;
    const wprR = wprRanks[rid];
    const midR = midRanks[rid];
    const lateR = lateRanks[rid];
    const totR = totalRanks[rid];
    // Count #1 votes (signal == 1) and top-3 votes (signal <= 3) across 6 signals.
    const _votes_top1 =
        ((wprR != null && wprR === 1) ? 1 : 0) +
        ((lateR != null && lateR === 1) ? 1 : 0) +
        ((u.wcR != null && u.wcR === 1) ? 1 : 0) +
        ((u.l600R != null && u.l600R === 1) ? 1 : 0) +
        ((u.pfaiR != null && u.pfaiR === 1) ? 1 : 0) +
        ((trR != null && trR === 1) ? 1 : 0);
    const _votes_top3 =
        ((wprR != null && wprR <= 3) ? 1 : 0) +
        ((lateR != null && lateR <= 3) ? 1 : 0) +
        ((u.wcR != null && u.wcR <= 3) ? 1 : 0) +
        ((u.l600R != null && u.l600R <= 3) ? 1 : 0) +
        ((u.pfaiR != null && u.pfaiR <= 3) ? 1 : 0) +
        ((trR != null && trR <= 3) ? 1 : 0);

    // Vote count cell - shows N/6 voting signals where this horse hit top-3
    // (the primary voting condition). Coloured by count for fast scanning:
    // 5-6 = emerald (strong), 4 = light emerald, 3 = neutral, 0-2 = muted.
    // Star indicator added when 3+ #1 votes (the second V3 condition).
    function votesCell(top3, top1) {
      let cls = '';
      if (top3 >= 5) cls = 'votes-strong';
      else if (top3 === 4) cls = 'votes-mid';
      else if (top3 === 3) cls = '';
      else cls = 'votes-weak';
      const star = top1 >= 3 ? '<span class="votes-star">★' + top1 + '</span>' : '';
      const tip = top3 + ' of 6 signals top-3, ' + top1 + ' #1';
      return '<td class="votes-cell ' + cls + '" title="' + tip + '">' +
        '<span class="v">' + top3 + '/6</span>' + star + '</td>';
    }

    rowsHtml += '<tr class="' + rowClasses.join(' ') + '" data-rid="' + escapeHtml(String(rid)) + '">' +
      // ── Primary columns (visible on mobile) ──
      '<td><span class="tn-cell">' + (u.tab || '?') + '</span></td>' +
      '<td class="horse-cell">' + finishBadge + escapeHtml(u.h || '') + pickBadge + '</td>' +
      '<td>' + (fxp ? '$' + fxp.toFixed(2) : '—') + '</td>' +
      scoreCell(u.cs, u.crk, u.csc) +
      votesCell(_votes_top3, _votes_top1) +
      wprCell(u.w, wprRanks[rid]) +
      sectCell(u.ls, lateRanks[rid]) +
      pfRankCell(u.wcR, 'PF Class') +
      pfRankCell(u.l600R, 'PF Last 600m') +
      pfRankCell(u.pfaiR, 'PF AI') +
      '<td class="rank-cell ' + trClass + '">' + (trR || '—') + '</td>' +
      // ── Supporting columns (hidden on mobile) ──
      // Style, Mid, Total, L400, Class∆ moved to detail panel (2026-05-15)
      // to declutter horizontal table scroll. Still visible by clicking row.
      '<td>' + (u.b || '') + '</td>' +
      '<td>' + settlesLabel(u.asp) + '</td>' +
      // ── Conditions / form context ──
      distanceCell(u) +
      (showGoing ? goingCell(u) : '') +
      '</tr>';
  });

  // Header with sort indicators
  function th(col, label) {
    const cls = ['sortable'];
    if (raceSortState.col === col) {
      cls.push('sort-' + raceSortState.dir);
    }
    return '<th class="' + cls.join(' ') + '" data-sort-col="' + col + '">' + label + '</th>';
  }

  document.getElementById('rd-runners-table').innerHTML =
    '<table class="race-table">' +
      '<thead><tr>' +
        // ── Primary scan columns (visible on mobile) ──
        // Order optimised for the voting model: Tab, Horse, Fxd (price),
        // then Score (logreg probability), Votes (model rule conformance),
        // then each individual voting signal so users can see WHERE the
        // votes came from. This is the same set of columns kept visible
        // on mobile.
        th('tab', 'Tab') + th('horse', 'Horse') +
        th('fxd', 'Fxd') +
        th('score', 'Score') +
        th('votes', 'Votes') +
        th('wpr', 'WPR') +
        th('late', 'Late') +
        th('wcR', 'Class') +
        th('l600R', 'L600') +
        th('pfai', 'PF AI') +
        th('tr', 'TR') +
        // ── Supporting / context columns (hidden on mobile) ──
        // Style, Mid, Total, L400, Class∆ moved to detail panel (2026-05-15)
        // to declutter horizontal table scroll.
        th('bar', 'Bar') +
        th('settles', 'Settles') +
        // Conditions
        (showGoing ? th('dist', 'Distance') + th('going', 'Going') : th('dist', 'Distance')) +
      '</tr></thead>' +
      '<tbody>' + rowsHtml + '</tbody>' +
    '</table>';

  // Wire sortable headers
  document.querySelectorAll('#rd-runners-table th.sortable').forEach(th => {
    th.addEventListener('click', () => {
      const col = th.dataset.sortCol;
      if (raceSortState.col === col) {
        // Toggle direction
        raceSortState.dir = raceSortState.dir === 'asc' ? 'desc' : 'asc';
      } else {
        raceSortState.col = col;
        // Default to ascending for ranks/text, descending for raw values
        const ascDefault = ['tab', 'horse', 'jky', 'trn', 'bar', 'tr', 'wpr',
                            'early', 'mid', 'late', 'total', 'settles', 'fxd', 'trp', 'score',
                            'pfai', 'wcR', 'l600R', 'l400R', 'rs'];
        raceSortState.dir = ascDefault.includes(col) ? 'asc' : 'desc';
      }
      renderRaceDetail(raceId);
    });
  });

  // Row-click expand: clicking a row inserts a detail panel below it.
  // Collapse other expanded rows first (only one open at a time).
  document.querySelectorAll('#rd-runners-table tbody tr').forEach(tr => {
    tr.addEventListener('click', (e) => {
      // Ignore clicks on the header
      if (tr.tagName !== 'TR' || !tr.dataset.rid) return;
      const rid = tr.dataset.rid;
      const u = runners.find(x => String(x.rid) === String(rid));
      if (!u) return;

      // Collapse any currently-open detail row
      const existing = document.querySelector('#rd-runners-table tbody tr.race-detail-row');
      if (existing) {
        const wasForThis = existing.dataset.forRid === String(rid);
        existing.remove();
        document.querySelectorAll('#rd-runners-table tbody tr.expanded').forEach(t => t.classList.remove('expanded'));
        if (wasForThis) return;  // toggle off
      }

      // Insert new detail row immediately after the clicked row
      tr.classList.add('expanded');
      const colCount = document.querySelectorAll('#rd-runners-table thead th').length;
      const detailTr = document.createElement('tr');
      detailTr.className = 'race-detail-row';
      detailTr.dataset.forRid = String(rid);
      detailTr.innerHTML = '<td colspan="' + colCount + '">' +
        buildRaceRunnerDetailHTML(u, race, { mid: midRanks, total: totalRanks }) +
      '</td>';
      tr.parentNode.insertBefore(detailTr, tr.nextSibling);
    });
  });
}

// Race shape SVG - horizontal lane diagram showing predicted positions.
// Width-proportional zones (a race with 6 leaders gets a wider Leaders zone
// than a race with 1). Tab numbers in colored cells. Picks (model picks) get
// a brighter outline so you can see which horses you're backing in context.
//
// Zone colour scheme: NEUTRAL gradient from light (front) to darker (back).
// Pace position isn't inherently good or bad - backmarkers can win, leaders
// can win. The previous coloured scheme (yellow/green/blue/pink) implied
// value judgements that don't exist. Now zones are clearly distinguishable
// but the picks (with emerald outline) are what visually pops.
function renderRaceShapeSVG(settled, totalRunners, paceDisplay, paceClass, race, runners) {
  const zones = [
    { key: 'leaders',  lbl: 'LEAD',     hint: '1-2', color: '#f3f4f6', textColor: '#374151' },
    { key: 'onpace',   lbl: 'ON-PACE',  hint: '3-4', color: '#e5e7eb', textColor: '#1f2937' },
    { key: 'midfield', lbl: 'MID',      hint: '5-8', color: '#d1d5db', textColor: '#111827' },
    { key: 'back',     lbl: 'BACK',     hint: '9+',  color: '#9ca3af', textColor: '#030712' },
  ];

  // Detect mobile viewport at render time. SVG scales proportionally via
  // viewBox, so on small screens a 22px cell in 880-unit space displays as
  // ~9.5px - illegible. Mobile renders with a smaller viewBox (so the SAME
  // pixel-sized elements appear larger relative to the viewBox) AND larger
  // font sizes. The result: cells and labels are readable on phones.
  const isMobile = (typeof window !== 'undefined') && window.innerWidth <= 720;

  // ViewBox dimensions. Mobile: narrower viewBox = larger visual elements.
  const W = isMobile ? 440 : 880;
  const H = isMobile ? 140 : 122;
  const PAD_X = 8, PAD_Y = isMobile ? 26 : 22, BOTTOM_PAD = 6;
  const plotW = W - PAD_X * 2;
  const plotH = H - PAD_Y - BOTTOM_PAD;

  // Allocate width: each zone gets a guaranteed minimum so labels don't collide,
  // then remaining width is shared proportionally to runner counts.
  const counts = zones.map(z => settled[z.key].length);
  const totalRunnersInRace = counts.reduce((a, b) => a + b, 0);
  const MIN_ZONE_W = isMobile ? 70 : 90;
  const guaranteed = MIN_ZONE_W * zones.length;
  const sharedW = Math.max(0, plotW - guaranteed);

  const zoneWidths = zones.map((z, i) => {
    const share = totalRunnersInRace > 0 ? counts[i] / totalRunnersInRace : 0.25;
    return MIN_ZONE_W + sharedW * share;
  });

  const zoneOffsets = [];
  let cum = PAD_X;
  zoneWidths.forEach(w => { zoneOffsets.push(cum); cum += w; });

  let svg = '<svg class="race-shape-svg" viewBox="0 0 ' + W + ' ' + H +
    '" preserveAspectRatio="xMidYMid meet">';

  // Zone label and tab cell sizing - larger on mobile so they're readable
  // when the SVG scales to the phone width
  const zoneLabelFontSize = isMobile ? 13 : 10;
  const cellSize = isMobile ? 30 : 22;
  const cellFontSize = isMobile ? 15 : 11;
  const cellGap = isMobile ? 5 : 4;

  zones.forEach((z, i) => {
    const x = zoneOffsets[i];
    const w = zoneWidths[i];
    const horses = settled[z.key];

    svg += '<rect x="' + x + '" y="' + PAD_Y + '" width="' + w + '" height="' + plotH +
      '" fill="' + z.color + '" fill-opacity="0.08" stroke="' + z.color +
      '" stroke-opacity="0.25" stroke-width="1" rx="4"/>';

    svg += '<text x="' + (x + w / 2) + '" y="' + (PAD_Y - 10) + '" ' +
      'font-family="Outfit" font-size="' + zoneLabelFontSize + '" font-weight="700" letter-spacing="0.06em" ' +
      'text-anchor="middle" fill="' + z.textColor + '">' +
      z.lbl + '</text>';

    const innerPad = 8;
    const availW = w - innerPad * 2;
    const cellsPerRow = Math.max(1, Math.floor((availW + cellGap) / (cellSize + cellGap)));
    // Tab cells need contrast against the (neutral grey) zone background,
    // so we use a much darker fill regardless of zone. White text remains
    // readable on the dark fill. Picks get a bright emerald outline so they
    // visually pop against the neutral palette.
    const cellFill = '#1f2937';
    // Lookup pick run_ids for this race so we can outline pick cells
    const racePicks = race ? (MODEL_PICKS[race.race_id] || {})[PRIMARY_KEY] || [] : [];
    const pickIds = new Set(racePicks.map(p => String(p.run_id)));
    horses.forEach((u, hi) => {
      const row = Math.floor(hi / cellsPerRow);
      const col = hi % cellsPerRow;
      const cellX = x + innerPad + col * (cellSize + cellGap);
      const cellY = PAD_Y + 8 + row * (cellSize + cellGap);
      if (cellY + cellSize > PAD_Y + plotH - 4) return;
      const isPick = pickIds.has(String(u.rid));
      const stroke = isPick ? ' stroke="#10b981" stroke-width="2"' : '';
      svg += '<rect x="' + cellX + '" y="' + cellY + '" width="' + cellSize + '" height="' + cellSize +
        '" fill="' + cellFill + '" rx="3"' + stroke + '/>';
      svg += '<text x="' + (cellX + cellSize / 2) + '" y="' + (cellY + cellSize / 2 + cellFontSize / 3) +
        '" font-family="Outfit" font-size="' + cellFontSize + '" font-weight="700" text-anchor="middle" ' +
        'fill="#fff">' + (u.tab || '?') + '</text>';
    });

    if (horses.length === 0) {
      svg += '<text x="' + (x + w / 2) + '" y="' + (PAD_Y + plotH / 2 + 4) + '" ' +
        'font-family="Outfit" font-size="' + (isMobile ? 13 : 11) + '" font-style="italic" fill="' + z.textColor +
        '" fill-opacity="0.4" text-anchor="middle">none</text>';
    }
  });

  svg += '</svg>';

  // Pace pill rendered as HTML element above the SVG, in its own row
  // so it never collides with zone labels. Floats to the right.
  let pacePill = '';
  if (paceDisplay) {
    const cls = paceClass ? ('rsp-pill rsp-pill-' + paceClass) : 'rsp-pill';
    pacePill = '<div class="rsp-pill-row">' +
      '<span class="' + cls + '">' +
        '<span class="rsp-pill-lbl">PACE</span>' +
        '<span class="rsp-pill-val">' + escapeHtml(paceDisplay) + '</span>' +
      '</span>' +
    '</div>';
  }

  let unknownCaption = '';
  if (settled.unknown && settled.unknown.length > 0) {
    unknownCaption = '<div class="race-shape-unknown">' +
      settled.unknown.length + ' runner' + (settled.unknown.length === 1 ? '' : 's') +
      ' with no settling history (likely first-up or limited data)</div>';
  }

  return pacePill + svg + unknownCaption;
}


// Track conditions card - shows venue's all-conditions winner-zone profile
// with AU baseline overlay for easy comparison.
function renderTrackConditions(race) {
  const venue = race.venue || '';

  const bias = (typeof VENUE_BIAS !== 'undefined') ? VENUE_BIAS :
    { byVenueGoingRail: {}, byVenue: {}, totalRaces: 0 };
  const venueStats = bias.byVenue[venue];

  function computeZoneObserved(stats) {
    if (!stats || !stats.n) return null;
    return {
      n:        stats.n,
      leaders:  stats.l / stats.n,
      onpace:   stats.o / stats.n,
      midfield: stats.m / stats.n,
      back:     stats.b / stats.n,
    };
  }
  const venueObs = computeZoneObserved(venueStats);

  // AU baseline percentages (data-derived)
  const auBaseline = { leaders: 0.091, onpace: 0.270, midfield: 0.534, back: 0.106 };
  const zoneLabels = { leaders: 'Leaders', onpace: 'On-pace', midfield: 'Midfield', back: 'Back-markers' };

  // Empty state if no data at all
  if (!venueObs) {
    const note = bias.totalRaces
      ? 'No historical races for ' + escapeHtml(venue) + ' yet. The cache will fill in over the coming weeks.'
      : 'No venue history loaded yet.';
    return '<div class="tc-panel tc-panel-venue tc-insufficient-panel">' +
        '<div class="tc-panel-title">' + escapeHtml(venue) + ' overall</div>' +
        '<div class="tc-summary">' + note + '</div>' +
      '</div>';
  }

  // Build summary - largest deviation from AU avg becomes the headline
  const deviations = ['leaders', 'onpace', 'midfield', 'back'].map(k => ({
    zone:  k,
    obs:   venueObs[k],
    base:  auBaseline[k],
    delta: venueObs[k] - auBaseline[k],
  }));
  deviations.sort((a, b) => Math.abs(b.delta) - Math.abs(a.delta));
  const top = deviations[0];

  let summary;
  if (venueObs.n < 5) {
    summary = '<strong>Tiny sample (N=' + venueObs.n + ')</strong> - read with caution.';
  } else if (Math.abs(top.delta) < 0.05) {
    summary = 'Plays close to AU average across all conditions.';
  } else if (top.delta > 0) {
    summary = '<strong>' + zoneLabels[top.zone] + ' bias</strong> overall (' +
      (venueObs[top.zone] * 100).toFixed(0) + '% winners vs ' +
      (auBaseline[top.zone] * 100).toFixed(0) + '% AU avg).';
  } else {
    summary = '<strong>Anti-' + zoneLabels[top.zone].toLowerCase() + '</strong> overall (' +
      (venueObs[top.zone] * 100).toFixed(0) + '% winners vs ' +
      (auBaseline[top.zone] * 100).toFixed(0) + '% AU avg).';
  }

  // Build dual-bar rows: venue (dark slate) + AU avg (lighter accent) overlapping.
  // Both percentages shown on the right.
  const barRows = ['leaders', 'onpace', 'midfield', 'back'].map(k => {
    const v = venueObs[k];
    const a = auBaseline[k];
    const vWidth = Math.max(2, Math.round(v * 100));
    const aWidth = Math.max(2, Math.round(a * 100));
    return '<div class="tc-dualbar-row">' +
      '<span class="tc-zone-lbl">' + zoneLabels[k] + '</span>' +
      '<div class="tc-dualbar-track">' +
        '<div class="tc-dualbar-venue" style="width:' + vWidth + '%;" title="' + escapeHtml(venue) + ' ' + (v*100).toFixed(0) + '%"></div>' +
        '<div class="tc-dualbar-au" style="width:' + aWidth + '%;" title="AU avg ' + (a*100).toFixed(0) + '%"></div>' +
      '</div>' +
      '<span class="tc-dualbar-pcts">' +
        '<span class="tc-pct-venue">' + (v * 100).toFixed(0) + '%</span>' +
        '<span class="tc-pct-au">' + (a * 100).toFixed(0) + '%</span>' +
      '</span>' +
      '</div>';
  }).join('');

  let footerNote = '';
  if (bias.totalRaces) {
    footerNote = '<div class="tc-source-note">Based on ' + bias.totalRaces +
      ' historical races. Refreshed daily.</div>';
  }

  return '<div class="tc-panel tc-panel-venue">' +
      '<div class="tc-panel-title">' + escapeHtml(venue) + ' overall' +
        '<span class="tc-panel-meta">all conditions · N=' + venueObs.n + '</span>' +
      '</div>' +
      '<div class="tc-summary">' + summary + '</div>' +
      '<div class="tc-dualbar-legend">' +
        '<span class="tc-legend-item"><span class="swatch swatch-venue"></span>' + escapeHtml(venue) + '</span>' +
        '<span class="tc-legend-item"><span class="swatch swatch-au"></span>AU average</span>' +
      '</div>' +
      '<div class="tc-dualbars">' + barRows + '</div>' +
      footerNote +
    '</div>';
}

// PF barrier x runstyle A2E grid. Reads PF_BARRIER_BIAS injected from
// pf_barrier_bias.csv (written by puntingform_ingest.py speedmaps step).
// A2E values colour-coded using PF's own thresholds: <0.95 red, >1.15 green,
// in between is neutral. Empty cells (low sample, PF returns null) render
// as a faint em-dash.
//
// Returns empty string when there's no PF data for this venue - caller
// hides the panel in that case so it doesn't render an empty box.
function renderPfBarrierBias(race) {
  const venue = race.venue || '';
  const bias = (typeof PF_BARRIER_BIAS !== 'undefined') ? PF_BARRIER_BIAS : { byVenue: {} };
  const entry = bias.byVenue ? bias.byVenue[venue] : null;
  if (!entry || !entry.bands || !entry.bands.length) return '';

  // Format a single A2E cell - empty -> em-dash, value -> 2dp with colour gate
  function cell(value, isTotalsRow) {
    let cls = 'pf-bias-cell';
    let txt;
    if (value == null) {
      cls += ' pf-bias-empty';
      txt = '—';
    } else {
      txt = value.toFixed(2);
      // PF's own thresholds for colouring (see their docs: A2E <0.95 below
      // expectation, >1.15 above expectation, in between is neutral).
      if (value < 0.95) cls += ' pf-bias-bad';
      else if (value > 1.15) cls += ' pf-bias-good';
    }
    if (isTotalsRow) cls += ' pf-bias-totals';
    return '<div class="' + cls + '">' + txt + '</div>';
  }

  // Header row
  const headerCells =
    '<div class="pf-bias-cell pf-bias-h">Barrier</div>' +
    '<div class="pf-bias-cell pf-bias-h">Forward</div>' +
    '<div class="pf-bias-cell pf-bias-h">Midfield</div>' +
    '<div class="pf-bias-cell pf-bias-h">Back</div>';

  // Data rows - one per barrier band. The Totals row is visually separated.
  const bandRows = entry.bands.map(b => {
    const isTotals = b.band === 'Totals';
    let lblCls = 'pf-bias-cell pf-bias-band';
    if (isTotals) lblCls += ' pf-bias-totals';
    return '<div class="' + lblCls + '">' + escapeHtml(b.band) + '</div>' +
           cell(b.forward,  isTotals) +
           cell(b.midfield, isTotals) +
           cell(b.back,     isTotals);
  }).join('');

  // Meta line: rail position + track direction + freshness date
  const metaParts = [];
  if (entry.railPosition) metaParts.push('Rail ' + escapeHtml(entry.railPosition));
  if (entry.antiClockwise === true)  metaParts.push('anti-clockwise');
  if (entry.antiClockwise === false) metaParts.push('clockwise');
  if (entry.asOf) metaParts.push('as of ' + escapeHtml(entry.asOf));
  const metaLine = metaParts.length
    ? '<span class="pf-bias-meta">' + metaParts.join(' · ') + '</span>'
    : '';

  return '<div class="pf-bias-title">' +
           '<span>PF Barrier × Run Style</span>' + metaLine +
         '</div>' +
         '<div class="pf-bias-blurb">' +
           'Actual to Expected (A2E) vs market price - PF lifetime data. ' +
           '1.00 is neutral; values below 0.95 underperform, above 1.15 outperform.' +
         '</div>' +
         '<div class="pf-bias-grid">' + headerCells + bandRows + '</div>' +
         '<div class="pf-bias-legend">' +
           '<span><span class="swatch sw-bad"></span>Below 0.95 (underperform)</span>' +
           '<span><span class="swatch sw-good"></span>Above 1.15 (outperform)</span>' +
         '</div>';
}

// Normalize rail strings the same way the Python loader does so the
// JS-side lookup keys match exactly (Caulfield|Good|Out 8m).
function normalizeRail(rail) {
  if (!rail) return '';
  return String(rail).replace('Entire Circuit', '').trim() || 'Unknown';
}

// Helper - bucket going string into category for matching
function goingCategoryStr(g) {
  if (!g) return '';
  const gl = g.toLowerCase();
  if (gl.startsWith('firm')) return 'Firm';
  if (gl.startsWith('good')) return 'Good';
  if (gl.startsWith('soft')) return 'Soft';
  if (gl.startsWith('heavy')) return 'Heavy';
  if (gl.startsWith('synth')) return 'Synthetic';
  return g;
}

function wireContextOverride(race) {
  const inp = document.getElementById('ctx-override-input');
  if (inp) {
    let dt = null;
    inp.addEventListener('input', e => {
      clearTimeout(dt);
      dt = setTimeout(() => {
        setRaceTrackRating(race, e.target.value.trim());
        renderRaceDetail(race.race_id);
      }, 600);
    });
  }
  const clearBtn = document.getElementById('ctx-override-clear');
  if (clearBtn) {
    clearBtn.addEventListener('click', () => {
      setRaceTrackRating(race, null);
      renderRaceDetail(race.race_id);
    });
  }
}

function wireTrackConditionsCard(race) {
  // No-op - override moved to the context bar (wireContextOverride handles it)
}

// Wire date controls
document.querySelectorAll('.race-date-quick').forEach(btn => {
  btn.addEventListener('click', () => {
    const k = btn.dataset.rdate;
    if (k === 'yesterday') currentBrowseDate = isoDate(-1);
    else if (k === 'tomorrow') currentBrowseDate = isoDate(1);
    else currentBrowseDate = isoDate(0);
    renderMeetingsGrid();
  });
});
const rdInp = document.getElementById('race-date-input');
if (rdInp) {
  rdInp.value = isoDate(0);
  rdInp.addEventListener('change', e => {
    if (e.target.value) {
      currentBrowseDate = e.target.value;
      renderMeetingsGrid();
    }
  });
}

// Wire Today tab filter controls (field size, jky rating, reset).
// Each change persists to localStorage and re-renders the picks list.
// Picks that fail the active filter dim but stay visible/clickable so
// the user can still see what's been filtered out.
const _todayFilterFs = document.getElementById('today-filter-fs');
if (_todayFilterFs) {
  _todayFilterFs.value = String(todayFilters.minFs);
  _todayFilterFs.addEventListener('change', e => {
    todayFilters.minFs = parseInt(e.target.value, 10) || 0;
    saveTodayFilters();
    renderToday();
  });
}
const _todayFilterJky = document.getElementById('today-filter-jky');
if (_todayFilterJky) {
  _todayFilterJky.value = String(todayFilters.minJky);
  _todayFilterJky.addEventListener('change', e => {
    todayFilters.minJky = parseInt(e.target.value, 10) || 0;
    saveTodayFilters();
    renderToday();
  });
}
const _todayFilterReset = document.getElementById('today-filter-reset');
if (_todayFilterReset) {
  _todayFilterReset.addEventListener('click', () => {
    todayFilters = { minFs: 0, minJky: 0 };
    saveTodayFilters();
    if (_todayFilterFs) _todayFilterFs.value = '0';
    if (_todayFilterJky) _todayFilterJky.value = '0';
    renderToday();
  });
}

// Wire Today tab date controls (mirrors the Race tab pattern)
document.querySelectorAll('.today-date-quick').forEach(btn => {
  btn.addEventListener('click', () => {
    const k = btn.dataset.tdate;
    if (k === 'yesterday') currentTodayDate = isoDate(-1);
    else if (k === 'tomorrow') currentTodayDate = isoDate(1);
    else currentTodayDate = isoDate(0);
    renderToday();
  });
});
const tdInpInit = document.getElementById('today-date-input');
if (tdInpInit) {
  tdInpInit.value = isoDate(0);
  tdInpInit.addEventListener('change', e => {
    if (e.target.value) {
      currentTodayDate = e.target.value;
      renderToday();
    }
  });
}
const backBtn = document.getElementById('race-back-btn');
if (backBtn) backBtn.addEventListener('click', exitRaceDetail);

// ── Next-to-jump ticker ────────────────────────────────────────────────────
function fmtCountdown(secs) {
  if (secs <= 0) return 'LIVE';
  if (secs < 60) return secs + 's';
  const m = Math.floor(secs / 60), s = secs % 60;
  if (m < 60) return m + 'm ' + (s < 10 ? '0' : '') + s + 's';
  const h = Math.floor(m / 60), mm = m % 60;
  return h + 'h ' + (mm < 10 ? '0' : '') + mm + 'm';
}
function renderNtjTicker() {
  const pillsEl = document.getElementById('ntj-pills');
  if (!pillsEl) return;
  const now = new Date();
  const upcoming = RACES.filter(r => {
    if (r.done === 1) return false;
    if (!r.start_time) return false;
    const tm = new Date(r.start_time);
    const diff = (tm - now) / 1000;
    return diff >= -180 && diff <= 86400;  // -3min to +24h
  }).map(r => ({ race: r, secsUntil: Math.round((new Date(r.start_time) - now) / 1000) }))
    .sort((a, b) => a.secsUntil - b.secsUntil)
    .slice(0, 6);

  if (upcoming.length === 0) {
    pillsEl.innerHTML = '<div class="ntj-empty">No races jumping soon.</div>';
    return;
  }
  pillsEl.innerHTML = upcoming.map(({ race, secsUntil }) => {
    let cdCls = 'cd-later';
    if (secsUntil <= 0) cdCls = 'cd-live';
    else if (secsUntil <= 120) cdCls = 'cd-imminent';
    else if (secsUntil <= 600) cdCls = 'cd-soon';
    const racePicks = (MODEL_PICKS[race.race_id] || {});
    const hasPick = !!(racePicks[PRIMARY_KEY] || []).length;
    const hasLoose = !!(racePicks['loose'] || []).length;
    const pillClasses = ['ntj-pill'];
    if (hasPick) pillClasses.push('has-pick');
    if (hasLoose) pillClasses.push('has-loose-pick');
    return '<div class="' + pillClasses.join(' ') + '" data-rid="' + race.race_id + '">' +
      '<span class="ntj-pill-name">' + escapeHtml(race.venue) + ' R' + race.race + '</span>' +
      '<span class="ntj-pill-cd ' + cdCls + '">' + fmtCountdown(secsUntil) + '</span>' +
      '</div>';
  }).join('');
  pillsEl.querySelectorAll('.ntj-pill').forEach(p => {
    p.addEventListener('click', () => {
      navigateToRace(p.dataset.rid);
    });
  });
}
// Toggle handler
const ntjToggle = document.getElementById('ntj-toggle');
if (ntjToggle) {
  ntjToggle.addEventListener('click', () => {
    const t = document.getElementById('ntj-ticker');
    const icon = document.getElementById('ntj-toggle-icon');
    const collapsed = t.classList.toggle('collapsed');
    if (icon) icon.textContent = collapsed ? '▶' : '▼';
    try { localStorage.setItem('ntj-collapsed', collapsed ? '1' : '0'); } catch(e) {}
  });
  // Restore collapsed state
  try {
    if (localStorage.getItem('ntj-collapsed') === '1') {
      document.getElementById('ntj-ticker').classList.add('collapsed');
      document.getElementById('ntj-toggle-icon').textContent = '▶';
    }
  } catch(e) {}
}

// ── PNL tab state ──────────────────────────────────────────────────────────
let pnlState = {
  period: 'all',         // '7d' | '30d' | 'all' | 'custom' - default to All time
  customFrom: null,      // ISO date string for custom range
  customTo: null,
  view: 'actual',        // 'actual' | 'theoretical'
  // Default true: most users browse P&L to review their own bets, not all
  // model picks. The "show all picks" toggle is one click away when needed.
  // Persisted to localStorage so the user's preference sticks.
  filterOnlyBet: (function() {
    try {
      const v = localStorage.getItem('tr_pnl_filter_only_bet_v1');
      if (v === '0') return false;
      if (v === '1') return true;
    } catch(e) {}
    return true;  // default
  })(),
};

// Bet log persisted in localStorage
//   Key: tr_betlog_v1
//   Value: { runId: { placed: true|false, oddsTaken: number|null, comments: string } }
//
// placed: true if the user marked "I bet this", false/missing means did not bet
// oddsTaken: the actual price obtained when betting. If null, P&L falls back to fxprice
//            (with a small warning indicator on the row)
// comments: free-text post-mortem notes
const BETLOG_KEY = 'tr_betlog_v1';
function getBetLog() {
  try { return JSON.parse(localStorage.getItem(BETLOG_KEY) || '{}'); }
  catch(e) { return {}; }
}
function saveBetLog(log) {
  try { localStorage.setItem(BETLOG_KEY, JSON.stringify(log)); } catch(e) {}
}
function getBetEntry(runId) {
  const log = getBetLog();
  return log[String(runId)] || { placed: false, oddsTaken: null, comments: '', deadHeat: false };
}
function setBetEntry(runId, patch) {
  const log = getBetLog();
  const existing = log[String(runId)] || {};
  log[String(runId)] = Object.assign({}, existing, patch);
  saveBetLog(log);
  // Auto-push the bet log change to the gist so other devices see it on next pull.
  // This is debounced so rapid edits coalesce into a single push.
  if (typeof scheduleSyncPush === 'function') scheduleSyncPush();
}
function isPlaced(runId) {
  return !!(getBetLog()[String(runId)] || {}).placed;
}
// Returns the price to use for P&L calc on a given bet:
//   - oddsTaken if user entered one
//   - else fall back to settled SP / Top / fxprice (in that order)
function effectivePrice(s, betLogEntry) {
  if (betLogEntry && betLogEntry.oddsTaken) return betLogEntry.oddsTaken;
  return s.sp || s.top || s.fxprice;
}

// ── PNL tab rendering ──────────────────────────────────────────────────────
function renderPnL() {
  // Get settled bets within the chosen time period
  const allSettled = SETTLED || [];
  // Filter to the active sub-tab's model. Older settled entries (pre-model-tagging)
  // default to 'main' so historical bets show up in the Main sub-tab.
  const pnlActiveModel = (activeModels && activeModels.pnl) || 'main';
  const modelSettled = allSettled.filter(s => (s.model || 'main') === pnlActiveModel);

  // Update sub-tab badge counts to reflect settled counts per model (in current period)
  const today = new Date();
  today.setHours(0,0,0,0);

  function withinPeriod(dateStr) {
    if (!dateStr) return false;
    if (pnlState.period === 'all') return true;
    const d = new Date(dateStr);
    if (isNaN(d.getTime())) return false;
    if (pnlState.period === '7d') {
      const cutoff = new Date(today.getTime() - 7 * 86400000);
      return d >= cutoff;
    }
    if (pnlState.period === '30d') {
      const cutoff = new Date(today.getTime() - 30 * 86400000);
      return d >= cutoff;
    }
    if (pnlState.period === 'custom') {
      if (pnlState.customFrom && d < new Date(pnlState.customFrom)) return false;
      if (pnlState.customTo) {
        const toDate = new Date(pnlState.customTo);
        toDate.setHours(23,59,59,999);
        if (d > toDate) return false;
      }
      return true;
    }
    return true;
  }
  // Set sub-tab badges to show settled count per model within current period
  ['main', 'loose'].forEach(m => {
    const badge = document.getElementById('pnl-subtab-count-' + m);
    if (badge) {
      badge.textContent = allSettled
        .filter(s => (s.model || 'main') === m && withinPeriod(s.date))
        .length;
    }
  });

  const settled = modelSettled.filter(s => withinPeriod(s.date));

  // Get bet log to determine which bets the user actually placed
  const log = getBetLog();
  function wasBetPlaced(s) {
    const e = log[String(s.run_id)];
    return !!(e && e.placed);
  }

  // Determine which bets contribute to "actual" view
  const actualBets = settled.filter(wasBetPlaced);
  // For "theoretical" view, all settled bets contribute
  const viewBets = pnlState.view === 'actual' ? actualBets : settled;

  // ── Stats strip ──
  // Sort viewBets chronologically for streak calc (oldest first).
  const sortedForStats = viewBets.slice().sort((a, b) => {
    const aKey = (a.date || '') + (a.start_time || '');
    const bKey = (b.date || '') + (b.start_time || '');
    return aKey.localeCompare(bKey);
  });

  let totalWins = 0, totalPlaces = 0, totalStake = 0, totalReturn = 0, totalProfit = 0;
  let curWinStreak = 0, curLossStreak = 0;
  let longestWinStreak = 0, longestLossStreak = 0;
  let runningWS = 0, runningLS = 0;
  // Timing edge tracking: average difference between oddsTaken and SP across
  // all bets that have both values recorded. Positive = you consistently beat
  // the SP (good timing). Negative = horses firmed after you bet (drift bias).
  // Only counts bets with BOTH oddsTaken and SP recorded.
  let vsSpSum = 0, vsSpCount = 0;

  sortedForStats.forEach(s => {
    const entry = log[String(s.run_id)] || { placed: false, oddsTaken: null, comments: '', deadHeat: false };
    const hasOddsTaken = entry.oddsTaken != null && entry.oddsTaken > 1;

    // Stake source same as Today/settled-row logic
    const stakePrice = hasOddsTaken ? entry.oddsTaken : s.fxprice;
    if (!stakePrice || stakePrice <= 1) return;
    const stake = calcStake(stakePrice, { capExempt: hasOddsTaken });
    if (!stake) return;

    // Track vs-SP timing edge if both values are available
    if (hasOddsTaken && s.sp != null && s.sp > 1) {
      vsSpSum += (entry.oddsTaken - s.sp);
      vsSpCount++;
    }

    // Settle price: oddsTaken if recorded, else SP, else fxprice
    const settlePrice = hasOddsTaken ? entry.oddsTaken : (s.sp || s.fxprice);
    const dhMult = entry.deadHeat ? 0.5 : 1;

    totalStake += stake;
    // Place rate denominator = bets where finish is known
    const placeFinish = (s.finish != null) && s.finish >= 1 && s.finish <= 3;
    if (placeFinish) totalPlaces++;

    if (s.won) {
      totalWins++;
      const profit = stake * (settlePrice - 1) * dhMult;
      totalReturn += stake + profit;
      totalProfit += profit;
      runningWS++; runningLS = 0;
      if (runningWS > longestWinStreak) longestWinStreak = runningWS;
    } else {
      totalProfit -= stake;
      // No return on a loss
      runningLS++; runningWS = 0;
      if (runningLS > longestLossStreak) longestLossStreak = runningLS;
    }
  });
  // Current streaks are the running counters at end of sequence
  curWinStreak = runningWS;
  curLossStreak = runningLS;

  const realWR = sortedForStats.length > 0 ? totalWins / sortedForStats.length : null;
  const realPR = sortedForStats.length > 0 ? totalPlaces / sortedForStats.length : null;
  const realROI = totalStake > 0 ? (totalReturn - totalStake) / totalStake : null;
  // Use the ACTIVE model's metadata for chart baselines (expected ROI/WR
  // lines). Each model has its own expected_roi_sp / expected_wr from
  // toprate_daily.py MODEL_DEFS - this way the dashed-line target adjusts
  // when the user flips between Main and Loose sub-tabs.
  const meta = MODEL_META[pnlActiveModel] || MODEL_META[PRIMARY_KEY] || {};

  function statBlock(lbl, val, sub, cls, tooltip) {
    const titleAttr = tooltip ? ' title="' + tooltip + '"' : '';
    return '<div class="pnl-stat"' + titleAttr + '>' +
      '<div class="lbl">' + lbl + '</div>' +
      '<div class="val ' + (cls || '') + '">' + val + '</div>' +
      '<div class="sub">' + (sub || '') + '</div>' +
      '</div>';
  }
  const profitCls = totalProfit > 0 ? 'pos' : (totalProfit < 0 ? 'neg' : '');
  const profitStr = (totalProfit >= 0 ? '+' : '') + totalProfit.toFixed(2) + 'u';
  const profitDollarSub = (totalProfit >= 0 ? '+' : '') + fmtDollar(totalProfit);
  const wrStr = realWR != null ? (realWR * 100).toFixed(1) + '%' : '—';
  const prStr = realPR != null ? (realPR * 100).toFixed(1) + '%' : '—';
  const roiStr = realROI != null ? ((realROI >= 0 ? '+' : '') + (realROI * 100).toFixed(1) + '%') : '—';
  const roiCls = realROI != null && realROI > 0 ? 'pos' : (realROI != null && realROI < 0 ? 'neg' : '');

  // Streak displays - main = current, sub = longest in period
  const winStreakStr = curWinStreak > 0 ? curWinStreak.toString() : '0';
  const winStreakSub = longestWinStreak > 0 ? 'longest ' + longestWinStreak : '—';
  const lossStreakStr = curLossStreak > 0 ? curLossStreak.toString() : '0';
  const lossStreakSub = longestLossStreak > 0 ? 'longest ' + longestLossStreak : '—';

  // Avg vs SP: average odds-taken minus SP across bets where both are known.
  // Positive = you typically beat SP (good timing); negative = horses firmed.
  const avgVsSp = vsSpCount > 0 ? vsSpSum / vsSpCount : null;
  const vsSpStr = avgVsSp != null ? (avgVsSp >= 0 ? '+' : '') + avgVsSp.toFixed(2) : '—';
  const vsSpSub = avgVsSp != null ? 'avg $ on ' + vsSpCount + ' bets' : 'no data';
  const vsSpCls = avgVsSp != null && avgVsSp > 0.05 ? 'pos' : (avgVsSp != null && avgVsSp < -0.05 ? 'neg' : '');

  // Total model picks in period regardless of placement status. The
  // "Bets" stat value depends on view mode (Actual = bets placed; Theoretical
  // = all model picks) but always shows both numbers in the tooltip so user
  // can see the gap between picks and actual bets.
  const totalAllPicks = settled.length;
  const totalPlaced = actualBets.length;
  const betsTooltip = pnlState.view === 'actual'
    ? 'Bets you placed: ' + totalPlaced + '. Total model picks in period: ' + totalAllPicks + '. Difference (' + (totalAllPicks - totalPlaced) + ') = picks you skipped.'
    : 'All model picks in period: ' + totalAllPicks + '. Bets you actually placed: ' + totalPlaced + ' (' + (totalAllPicks > 0 ? Math.round(totalPlaced / totalAllPicks * 100) : 0) + '%).';

  document.getElementById('pnl-stats-strip').innerHTML =
    statBlock('Bets', sortedForStats.length, pnlState.view === 'actual' ? 'placed of ' + totalAllPicks : 'all picks', '', betsTooltip) +
    statBlock('P&amp;L', profitStr, profitDollarSub, profitCls) +
    statBlock('Win rate', wrStr, '') +
    statBlock('Place rate', prStr, '') +
    statBlock('ROI', roiStr, '', roiCls) +
    statBlock('Win streak', winStreakStr, winStreakSub, curWinStreak > 0 ? 'pos' : '') +
    statBlock('Loss streak', lossStreakStr, lossStreakSub, curLossStreak > 0 ? 'neg' : '',
              longestLossStreak >= 10 ? 'Bankroll planning: longest streak in period was ' + longestLossStreak + ' losses. Plan for at least 15 at 1u stake.' : null) +
    statBlock('vs SP', vsSpStr, vsSpSub, vsSpCls, 'Average difference between odds-taken and starting price. Positive = you typically beat SP (good timing). Negative = horses firmed after you bet.');

  // ── Cumulative units chart ──
  // Sort by date+time chronologically
  const sortedView = viewBets.slice().sort((a, b) => {
    const aKey = (a.date || '') + (a.start_time || '');
    const bKey = (b.date || '') + (b.start_time || '');
    return aKey.localeCompare(bKey);
  });
  // Aggregate per-bet cumulative
  const cumPoints = [];
  let runningP = 0, runningS = 0;
  sortedView.forEach(s => {
    const stake = calcStake(s.fxprice);
    if (!stake) return;
    const entry = log[String(s.run_id)];
    const price = effectivePrice(s, entry);
    const profit = s.won ? stake * (price - 1) : -stake;
    runningP += profit;
    runningS += stake;
    cumPoints.push({
      date: s.date,
      cum: runningP,
      expected: runningS * (meta.roi_sp || 0),
    });
  });

  const cumSvg = document.getElementById('pnl-chart-cum');
  cumSvg.innerHTML = '';
  if (cumPoints.length === 0) {
    cumSvg.innerHTML = '<text x="300" y="100" text-anchor="middle" class="axis-text" style="font-size:12px;">' +
      (pnlState.view === 'actual' ? 'No bets placed yet in this period' : 'No settled picks in this period') + '</text>';
  } else {
    const W = 600, H = 200, pad = 30;
    // Y-axis lock: rather than auto-scaling to fit the data exactly (which
    // causes the chart to feel like it's "exploding" during a bad week as
    // a new low forces a rescale), we fix a sane minimum range based on
    // expected variance. The chart still expands to fit larger swings but
    // small day-to-day moves stay visually proportional.
    //
    // Floor min at -1.5 * longest-loss-streak (a reasonable worst case in
    // bankroll terms) or -8u (whichever is more negative), so a 5-bet
    // drawdown doesn't dominate the chart visually.
    // Ceil max at +max(actual, expected end-point + 5u).
    const observedMax = Math.max(1, ...cumPoints.map(p => Math.max(p.cum, p.expected)));
    const observedMin = Math.min(0, ...cumPoints.map(p => Math.min(p.cum, p.expected)));
    const expectedFloor = -Math.max(8, longestLossStreak * 1.5);
    const maxV = Math.max(observedMax, 5);
    const minV = Math.min(observedMin, expectedFloor);
    const range = maxV - minV || 1;
    const xs = cumPoints.map((_, i) => pad + (cumPoints.length === 1 ? (W - 2*pad) / 2 : i * (W - 2*pad) / (cumPoints.length - 1)));
    const yScale = v => H - pad - ((v - minV) / range) * (H - 2*pad);
    const zeroY = yScale(0);
    let svgHtml = '<line class="axis" x1="' + pad + '" y1="' + zeroY + '" x2="' + (W-pad) + '" y2="' + zeroY + '" stroke-width="1"/>';
    // Reference drawdown band: show the expected-floor as a thin dashed line
    // so users have a visual anchor for "how bad would a real bad week look".
    const floorY = yScale(expectedFloor);
    svgHtml += '<line x1="' + pad + '" y1="' + floorY + '" x2="' + (W-pad) + '" y2="' + floorY +
               '" stroke="#e5e7eb" stroke-width="1" stroke-dasharray="2,4"/>';
    svgHtml += '<text x="' + (W-pad) + '" y="' + (floorY - 4) + '" class="axis-text" text-anchor="end" style="font-size:9px;opacity:0.6;">' +
               'planning floor</text>';
    const actualPath = cumPoints.map((p, i) => (i === 0 ? 'M' : 'L') + xs[i] + ',' + yScale(p.cum)).join(' ');
    svgHtml += '<path class="actual" d="' + actualPath + '"/>';
    const expPath = cumPoints.map((p, i) => (i === 0 ? 'M' : 'L') + xs[i] + ',' + yScale(p.expected)).join(' ');
    svgHtml += '<path class="expected" d="' + expPath + '"/>';
    svgHtml += '<text x="4" y="' + (yScale(maxV)+4) + '" class="axis-text">' + maxV.toFixed(1) + 'u</text>';
    svgHtml += '<text x="4" y="' + (zeroY+3) + '" class="axis-text">0u</text>';
    if (minV < 0) svgHtml += '<text x="4" y="' + (yScale(minV)+4) + '" class="axis-text">' + minV.toFixed(1) + 'u</text>';
    svgHtml += '<text x="' + xs[0] + '" y="' + (H-8) + '" class="axis-text">' + cumPoints[0].date + '</text>';
    if (cumPoints.length > 1) svgHtml += '<text x="' + xs[xs.length-1] + '" y="' + (H-8) + '" class="axis-text" text-anchor="end">' + cumPoints[cumPoints.length-1].date + '</text>';
    cumSvg.innerHTML = svgHtml;
  }

  // ── Rolling win-rate chart (window=20) ──
  const wrSvg = document.getElementById('pnl-chart-wr');
  wrSvg.innerHTML = '';
  const windowSize = 20;
  if (sortedView.length < 3) {
    wrSvg.innerHTML = '<text x="300" y="100" text-anchor="middle" class="axis-text" style="font-size:12px;">Need at least 3 settled bets for rolling chart</text>';
  } else {
    const wrPoints = [];
    for (let i = 0; i < sortedView.length; i++) {
      const start = Math.max(0, i - windowSize + 1);
      const slice = sortedView.slice(start, i + 1);
      const wins = slice.filter(s => s.won).length;
      const wr = wins / slice.length;
      wrPoints.push({ idx: i, wr: wr, n: slice.length });
    }
    const W = 600, H = 200, pad = 30;
    const expectedWR = meta.wr || 0.25;
    const maxWR = Math.max(0.5, expectedWR + 0.1, ...wrPoints.map(p => p.wr));
    const xs = wrPoints.map((_, i) => pad + (wrPoints.length === 1 ? (W - 2*pad) / 2 : i * (W - 2*pad) / (wrPoints.length - 1)));
    const yScale = v => H - pad - (v / maxWR) * (H - 2*pad);
    let svgHtml = '';
    // Expected WR baseline (dashed)
    svgHtml += '<line class="wr-expected" x1="' + pad + '" y1="' + yScale(expectedWR) + '" x2="' + (W-pad) + '" y2="' + yScale(expectedWR) + '"/>';
    // Rolling WR line
    const wrPath = wrPoints.map((p, i) => (i === 0 ? 'M' : 'L') + xs[i] + ',' + yScale(p.wr)).join(' ');
    svgHtml += '<path class="wr-line" d="' + wrPath + '"/>';
    // Y axis labels
    svgHtml += '<text x="4" y="' + (yScale(maxWR)+4) + '" class="axis-text">' + (maxWR*100).toFixed(0) + '%</text>';
    svgHtml += '<text x="4" y="' + (yScale(expectedWR)+3) + '" class="axis-text">' + (expectedWR*100).toFixed(0) + '%</text>';
    svgHtml += '<text x="4" y="' + (yScale(0)+3) + '" class="axis-text">0%</text>';
    // X axis: bet count
    svgHtml += '<text x="' + xs[0] + '" y="' + (H-8) + '" class="axis-text">Bet 1</text>';
    if (wrPoints.length > 1) svgHtml += '<text x="' + xs[xs.length-1] + '" y="' + (H-8) + '" class="axis-text" text-anchor="end">Bet ' + sortedView.length + '</text>';
    wrSvg.innerHTML = svgHtml;
  }

  // ── Settled bets list (rich expandable cards) ──
  document.getElementById('bh-count').textContent = settled.length;
  const list = document.getElementById('bh-list');
  list.innerHTML = '';

  // Apply "only bets I placed" filter if active
  let displaySettled = settled.slice().reverse();  // most recent first
  if (pnlState.filterOnlyBet) {
    displaySettled = displaySettled.filter(wasBetPlaced);
  }

  if (displaySettled.length === 0) {
    list.innerHTML = '<div class="bh-empty">No settled bets in this view.</div>';
    return;
  }

  displaySettled.forEach((s, idx) => {
    const csvPrice = s.fxprice;
    const sp = s.sp;
    const entry = log[String(s.run_id)] || { placed: false, oddsTaken: null, comments: '', deadHeat: false };
    const placed = !!entry.placed;
    const oddsTaken = entry.oddsTaken;
    const hasOddsTaken = oddsTaken != null && oddsTaken > 1;
    const r = s.runner_full || {};

    // Stake price source of truth: oddsTaken if entered, else live fxprice (muted).
    // For settled bets, this matches Today tab logic exactly.
    const stakePrice = hasOddsTaken ? oddsTaken : csvPrice;
    const usingFallback = !hasOddsTaken;
    const stake = (stakePrice != null && stakePrice > 1)
                    ? calcStake(stakePrice, { capExempt: hasOddsTaken })
                    : null;

    // Settle price: oddsTaken if recorded, else SP, else fxprice. Same as P&L logic.
    const settlePrice = hasOddsTaken ? oddsTaken : (sp || csvPrice);
    const dhMult = entry.deadHeat ? 0.5 : 1;
    // Actual P&L for this settled bet (negative if lost, positive if won)
    const pl = stake ? (s.won ? stake * (settlePrice - 1) * dhMult : -stake) : 0;

    // Card class - use Today tab's existing settled-win / settled-loss visuals
    let cardClass = s.won ? 'settled-win' : 'settled-loss';

    // Date column (replaces time) - "DD MMM" + smaller "weekday"
    let dateMain = s.date || '';
    let dateSub = '';
    if (s.date) {
      const d = new Date(s.date + 'T00:00:00');
      if (!isNaN(d.getTime())) {
        const months = ['Jan','Feb','Mar','Apr','May','Jun','Jul','Aug','Sep','Oct','Nov','Dec'];
        const weekdays = ['Sun','Mon','Tue','Wed','Thu','Fri','Sat'];
        dateMain = String(d.getDate()) + ' ' + months[d.getMonth()];
        dateSub = weekdays[d.getDay()];
      }
    }
    const dateHtml = '<div class="pr-time">' +
      '<div class="ds-main">' + escapeHtml(dateMain) + '</div>' +
      (dateSub ? '<span class="ttj">' + dateSub + '</span>' : '') +
      '</div>';

    // Signal pills - same structure as Today tab
    function sigPill(label, rank) {
      if (rank == null) return '<span class="sig"><span class="lbl">' + label + '</span><span class="v">—</span></span>';
      const cls = rank === 1 ? 'r1' : (rank === 2 ? 'r2' : (rank === 3 ? 'r3' : ''));
      return '<span class="sig ' + cls + '"><span class="lbl">' + label + '</span><span class="v">' + rank + '</span></span>';
    }
    // Score pill on settled rows also gets the confidence dot (same as Today).
    // Displays the raw score (0.00-1.00 as a 2-digit percentage), keeping
    // the within-race rank only as the colour driver. Showing the absolute
    // score lets you eyeball how close a settled pick was to the 0.50
    // threshold retrospectively.
    function scoreSigPill(rank, score, conf) {
      if (score == null && rank == null) return '<span class="sig"><span class="lbl">Score</span><span class="v">—</span></span>';
      const cls = rank === 1 ? 'r1' : (rank === 2 ? 'r2' : (rank === 3 ? 'r3' : ''));
      let confDot = '';
      if (conf != null) {
        const dotCls = conf >= 0.80 ? 'high' : (conf >= 0.50 ? 'mid' : 'low');
        const confTitle = 'Signal confidence ' + Math.round(conf * 100) + '%';
        confDot = '<span class="conf-dot ' + dotCls + '" title="' + confTitle + '"></span>';
      }
      const scoreDisplay = score != null ? Math.round(score * 100) : '—';
      const rankBit = rank != null ? ' (rank #' + rank + ' in this race)' : '';
      const scoreTooltip = 'Score ' + (score != null ? score.toFixed(3) : 'n/a') + rankBit +
        '. Threshold for picks was 0.50.';
      return '<span class="sig ' + cls + '" title="' + scoreTooltip + '">' +
        '<span class="lbl">Score</span><span class="v">' + scoreDisplay + '</span>' + confDot + '</span>';
    }
    // Vote count badge - shows model-rule conformance for the original pick
    // (mobile-friendly summary, replaces the chip row on small screens).
    const pVoteRanks = [s.wpr_rank, s.late_rank, s.wcR, s.l600R, s.pfaiR, s.tr_rank];
    const pVoteTop3 = pVoteRanks.filter(r2 => r2 != null && r2 <= 3).length;
    const pVoteTop1 = pVoteRanks.filter(r2 => r2 != null && r2 === 1).length;
    const pVoteTooltip = pVoteTop3 + ' of 6 signals rank top-3, ' + pVoteTop1 + ' rank #1.';
    const pVoteBadgeHtml = '<span class="sig vote-badge" title="' + pVoteTooltip + '">' +
      '<span class="lbl">Votes</span>' +
      '<span class="v">' + pVoteTop3 + '/6</span>' +
      (pVoteTop1 >= 3 ? '<span class="vote-star">★' + pVoteTop1 + '</span>' : '') +
      '</span>';

    // Desktop signal chips - the 6 voting signals. Matches the Today tab
    // layout. Fields are on the settled bet (`s`), not on the runner_full
    // record (`r`) which contains race-level context but not pre-computed ranks.
    const desktopChipsHtml =
      sigPill('WPR',   s.wpr_rank) +
      sigPill('Late',  s.late_rank) +
      sigPill('Class', s.wcR) +
      sigPill('L600',  s.l600R) +
      sigPill('PFAI',  s.pfaiR) +
      sigPill('TR',    s.tr_rank);
    // Score chip stacks above Votes badge in its own mini-column - same
    // layout as Today tab. Score uses cs (cumulative score), crk (within-race
    // rank for colour tier) + csc (confidence) surfaced on the settled bet.
    const scoreChipHtml = scoreSigPill(s.crk, s.cs, s.csc);

    const sigsTopHtml =
      '<span class="desktop-chips">' + desktopChipsHtml + '</span>' +
      '<span class="score-votes-stack">' + scoreChipHtml + pVoteBadgeHtml + '</span>';
    const formHtml = r.fm ?
      '<div class="pr-form desktop-only" title="Last 4 finishes">' + escapeHtml(r.fm) + '</div>' : '';
    const sigsHtml = '<div class="pr-sigs-top">' + sigsTopHtml + '</div>' + formHtml;

    // Fxd display (read-only, same as Today)
    const fxdValStr = csvPrice != null ? csvPrice.toFixed(2) : '—';
    const fxdValCls = csvPrice != null ? 'v' : 'v empty';
    // Top Fluc - populated post-race, useful to compare vs odds-taken on
    // settled bets. Shows whether the user took close to peak or got beaten
    // by the market drift.
    const tfPrice2 = s.top;
    const tfStr2 = tfPrice2 != null ? '$' + tfPrice2.toFixed(2) : '—';
    const tfTitle2 = tfPrice2 != null
      ? 'Top Fluc $' + tfPrice2.toFixed(2) + ' - highest bookie price during pre-race market'
      : 'Top Fluc - available after results sync';
    const oddsHtml =
      '<div class="pr-odds-display" title="Live fixed odds at last refresh">' +
        '<div class="pr-odds-main">' +
          (csvPrice != null ? '<span class="cur">$</span>' : '') +
          '<span class="' + fxdValCls + '">' + fxdValStr + '</span>' +
        '</div>' +
        '<div class="pr-odds-tf" title="' + tfTitle2 + '">' +
          '<span class="tf-lbl">TF</span>' +
          '<span class="tf-val' + (tfPrice2 == null ? ' empty' : '') + '">' + tfStr2 + '</span>' +
        '</div>' +
      '</div>';

    // Stake display (units + dollars)
    const stakeWrapCls = 'pr-stake' + (usingFallback ? ' muted' : '');
    const returnWrapCls = 'pr-return' + (usingFallback ? ' muted' : '');
    let stakeHtml, returnHtml;
    if (stake) {
      stakeHtml = '<span class="units">' + stake.toFixed(2) + 'u</span>' +
        '<span class="ret">' + fmtDollar(stake) + '</span>';
      // Return: only the actual payout on a win (stake * settlePrice, dead-heat halved).
      // Losing bets show em-dash so the column doesn't imply winnings.
      if (s.won) {
        const returnUnits = stake * settlePrice * dhMult;
        returnHtml = '<span class="units">' + returnUnits.toFixed(2) + 'u</span>' +
          '<span class="ret">' + fmtDollar(returnUnits) + '</span>';
      } else {
        returnHtml = '<span class="skip">&mdash;</span>';
      }
    } else {
      stakeHtml = '<span class="skip">—</span>';
      returnHtml = '<span class="skip">—</span>';
    }

    // Result chip - shows finish position with W/L tag (same as Today's hasOfficial branch)
    // Loss colouring varies by finish position - see lossPosClass helper.
    function lossPosClass(fin) {
      if (fin == null) return '';
      if (fin === 2) return ' fin2';
      if (fin >= 3 && fin <= 5) return ' fin345';
      return ' fin6plus';
    }
    let resultHtml;
    if (s.finish != null) {
      const cls = s.won ? 'win' : ('loss' + lossPosClass(s.finish));
      resultHtml = '<span class="res-tag ' + cls + '">' +
        (s.won ? 'W' : 'L') + ' · ' + s.finish + ord(s.finish) + '</span>';
    } else {
      resultHtml = '<span class="res-tag ' + (s.won ? 'win' : 'loss') + '">' +
        (s.won ? 'W' : 'L') + '</span>';
    }

    // Bet toggle + odds-taken input (same shape as Today)
    let betHtml = '<button class="bet-btn ' + (placed ? 'placed' : '') +
                  '" data-bh-bet-rid="' + s.run_id + '" title="' +
                  (placed ? 'Mark as not bet' : 'Mark this bet as placed') +
                  '" onclick="event.stopPropagation();">' +
                  (placed ? '✓' : '+') + '</button>';
    if (placed) {
      const oddsVal = oddsTaken != null ? oddsTaken.toFixed(2) : '';
      const showWarning = !hasOddsTaken;
      betHtml += '<span class="odds-input-wrap" onclick="event.stopPropagation();">' +
                   '<span class="cur">$</span>' +
                   '<input type="number" step="0.01" min="1" class="odds-input" ' +
                   'data-bh-odds-rid="' + s.run_id + '" placeholder="0.00" ' +
                   'value="' + oddsVal + '" />' +
                 '</span>';
      if (showWarning) {
        betHtml += '<span class="odds-warning" title="No odds-taken entered. P&L uses live fxprice as fallback.">⚠</span>';
      }
      // Timing edge vs SP: shows whether you got better/worse odds than starting
      // price. Positive number = you took an early price that drifted (good).
      // Negative = the horse firmed and SP was shorter than your bet (bad).
      // Only show when both oddsTaken AND SP are known.
      if (hasOddsTaken && s.sp != null && s.sp > 1) {
        const diff = oddsTaken - s.sp;
        const diffStr = (diff >= 0 ? '+' : '') + diff.toFixed(2);
        const edgeCls = diff > 0.05 ? 'pos' : (diff < -0.05 ? 'neg' : 'neutral');
        betHtml += '<span class="vs-sp ' + edgeCls + '" ' +
          'title="Odds taken $' + oddsTaken.toFixed(2) + ' vs SP $' + s.sp.toFixed(2) + '. ' +
          (diff > 0 ? 'You beat SP by $' + diff.toFixed(2) : diff < 0 ? 'SP beat your odds by $' + Math.abs(diff).toFixed(2) : 'You matched SP') +
          '">' + diffStr + '</span>';
      }
    }

    // Meta line: distance · going · jky · trn (matches Today tab)
    const metaParts = [];
    if (s.distance) metaParts.push(s.distance + 'm');
    if (s.going) metaParts.push(escapeHtml(s.going));
    if (r.j || s.jockey) metaParts.push(escapeHtml(r.j || s.jockey));
    if (r.tn || s.trainer) metaParts.push(escapeHtml(r.tn || s.trainer));
    const metaLine = metaParts.join(' · ');

    // Field size chip - same as Today tab. <=7 = warn red, flag skip
    // candidates for the user. Useful retrospectively on P&L too: shows
    // which past picks were small-field (the segment user wants to avoid).
    const fsValueP = s.field_size || (r.fs || null);
    let fsChipHtmlP = '';
    if (fsValueP != null) {
      const fsWarn = fsValueP <= 7;
      const fsTip = fsWarn
        ? 'Small field (' + fsValueP + ' runners). User strategy: skip bets in fields of 7 or fewer.'
        : fsValueP + ' runners in this race';
      fsChipHtmlP = '<span class="fs-chip ' + (fsWarn ? 'warn' : '') + '" title="' + fsTip + '">' +
        'F' + fsValueP + '</span>';
    }

    // Jockey rating chip - absolute rating buckets (matches Today tab).
    // 4 bands: red <75, amber 75-79, grey 80-84, green 85+.
    let jkyChipHtmlP = '';
    if (r.jrt != null) {
      const myRating = Math.round(r.jrt);
      let cls = '';
      let lbl = '';
      if (myRating >= 85) {
        cls = 'good';
        lbl = 'Elite jockey rating (85+).';
      } else if (myRating >= 80) {
        cls = '';
        lbl = 'Decent jockey rating (80-84).';
      } else if (myRating >= 75) {
        cls = 'warn';
        lbl = 'Mediocre jockey rating (75-79).';
      } else {
        cls = 'bad';
        lbl = 'Weak jockey rating (below 75).';
      }
      const tip = 'Jockey rating ' + myRating + '. ' + lbl;
      jkyChipHtmlP = '<span class="jky-chip ' + cls + '" title="' + tip + '">Jky ' + myRating + '</span>';
    }
    const fsAndJkyChipsP = fsChipHtmlP + jkyChipHtmlP;

    const rowHtml =
      '<div class="pick-row is-settled ' + cardClass + (placed ? ' bet-placed' : '') +
        '" data-row-idx="' + idx + '" data-run-id="' + s.run_id + '" data-race-id="' + (s.race_id || '') + '">' +
        dateHtml +
        '<div class="pr-venue clickable" data-nav-rid="' + (s.race_id || '') + '" title="Open race detail">' +
          '<div class="v-name">' + escapeHtml(s.venue || '') + '</div>' +
          '<div class="v-race">R' + s.race + ' ↗</div>' +
        '</div>' +
        '<div class="pr-runner">' +
          '<span class="tab-bdg">' + (s.tab || '?') + '</span>' +
          '<div class="rdetails">' +
            '<div class="rhorse">' + escapeHtml(s.horse || '') + fsAndJkyChipsP + '</div>' +
            '<div class="rmeta">' + metaLine + '</div>' +
          '</div>' +
        '</div>' +
        '<div class="pr-sigs">' + sigsHtml + '</div>' +
        '<div class="pr-odds"><span class="cell-lbl">Fxd</span>' + oddsHtml + '</div>' +
        '<div class="' + stakeWrapCls + '"><span class="cell-lbl">Stake</span>' + stakeHtml + '</div>' +
        '<div class="' + returnWrapCls + '"><span class="cell-lbl">Return</span>' + returnHtml + '</div>' +
        '<div class="pr-result"><span class="cell-lbl">Result</span>' + resultHtml + '</div>' +
        '<div class="pr-bet"><span class="cell-lbl">Bet</span>' + betHtml + '</div>' +
        '<div class="pr-chev">▾</div>' +
      '</div>' +
      '<div class="bh-detail" id="bh-detail-' + idx + '"></div>';

    list.insertAdjacentHTML('beforeend', rowHtml);
  });

  // Wire row clicks for expand
  list.querySelectorAll('.pick-row').forEach(row => {
    row.addEventListener('click', (ev) => {
      // Don't expand if clicking interactive elements
      if (ev.target.closest('.bet-btn, .odds-input, .odds-input-wrap, input, textarea, button')) return;
      // Venue block click - navigate to race detail and stop here, don't expand
      const navTarget = ev.target.closest('.pr-venue.clickable');
      if (navTarget) {
        ev.stopPropagation();
        navigateToRace(navTarget.dataset.navRid);
        return;
      }
      const idx = row.dataset.rowIdx;
      const detail = document.getElementById('bh-detail-' + idx);
      if (!detail) return;
      const isOpen = detail.classList.contains('open');
      if (isOpen) {
        detail.classList.remove('open');
        row.classList.remove('expanded');
      } else {
        // Lazy-render detail content
        if (!detail.innerHTML) {
          const s = displaySettled[Number(idx)];
          detail.innerHTML = renderBhDetail(s);
          // Wire comment textarea
          const ta = detail.querySelector('.bh-comments textarea');
          if (ta) {
            ta.addEventListener('input', (e) => {
              setBetEntry(s.run_id, { comments: e.target.value });
            });
          }
          // Wire odds-taken input in expand panel
          const oddsInput = detail.querySelector('[data-detail-odds-rid]');
          if (oddsInput) {
            oddsInput.addEventListener('input', (e) => {
              const v = parseFloat(e.target.value);
              setBetEntry(s.run_id, { oddsTaken: (isNaN(v) || v <= 0) ? null : v });
            });
            oddsInput.addEventListener('blur', () => renderPnL());
          }
          // Wire dead heat toggle in expand panel
          const dhToggle = detail.querySelector('[data-detail-deadheat-rid]');
          if (dhToggle) {
            dhToggle.addEventListener('change', (e) => {
              setBetEntry(s.run_id, { deadHeat: e.target.checked });
              renderPnL();
              if (typeof renderToday === 'function') { try { renderToday(); } catch(err) {} }
            });
          }
        }
        detail.classList.add('open');
        row.classList.add('expanded');
      }
    });
  });

  // Wire inline odds-taken input on the row itself
  list.querySelectorAll('[data-bh-odds-rid]').forEach(el => {
    el.addEventListener('input', e => {
      const rid = el.dataset.bhOddsRid;
      const v = parseFloat(e.target.value);
      setBetEntry(rid, { oddsTaken: (isNaN(v) || v <= 0) ? null : v });
    });
    el.addEventListener('blur', () => {
      renderPnL();
      if (typeof renderToday === 'function') { try { renderToday(); } catch(err) {} }
    });
    el.addEventListener('click', e => e.stopPropagation());
  });

  // Wire single bet toggle
  list.querySelectorAll('[data-bh-bet-rid]').forEach(btn => {
    btn.addEventListener('click', (ev) => {
      ev.stopPropagation();
      const rid = btn.dataset.bhBetRid;
      const cur = isPlaced(rid);
      setBetEntry(rid, { placed: !cur });
      renderPnL();
      // Also re-render Today tab in case user marked it from there earlier
      if (typeof renderToday === 'function') {
        try { renderToday(); } catch(e) {}
      }
    });
  });
}

// Render the expanded detail panel for a settled bet (using runner_full data)
function renderBhDetail(s) {
  const r = s.runner_full || {};
  const entry = getBetEntry(s.run_id);

  function speedCell(label, value, rank) {
    if (value == null) return '<div class="pd-speed-cell"><span class="sp-lbl">' + label + '</span><span class="sp-val">—</span></div>';
    const rkCls = rank === 1 ? 'r1' : (rank === 2 ? 'r2' : '');
    return '<div class="pd-speed-cell ' + rkCls + '">' +
      '<span class="sp-lbl">' + label + '</span>' +
      '<span class="sp-val">' + value.toFixed(1) + '</span>' +
      (rank ? '<span class="sp-rk">#' + rank + '</span>' : '') +
      '</div>';
  }

  // Find rank within race for speed scores by looking up race
  const race = (RACES || []).find(rc => String(rc.race_id) === String(s.race_id));
  const runnersInRace = race ? (race.runners || []) : [];
  function rankIn(field) {
    const valid = runnersInRace.filter(u => u[field] != null);
    valid.sort((a, b) => b[field] - a[field]);
    const found = valid.findIndex(u => String(u.rid) === String(s.run_id));
    return found >= 0 ? found + 1 : null;
  }

  const speedHtml =
    '<div class="pd-speed">' +
    speedCell('Early', r.es, rankIn('es')) +
    speedCell('Mid', r.ms, rankIn('ms')) +
    speedCell('Late', r.ls, rankIn('ls')) +
    speedCell('Total', r.ts, rankIn('ts')) +
    '</div>';

  // Distance perf
  let distPerf = '—';
  if (r.ds) {
    distPerf = (r.dw || 0) + 'W ' + Math.max(0, (r.dp || 0) - (r.dw || 0)) + 'P / ' + r.ds;
  }
  // Going perf
  let goingPerf = '—';
  if (s.going && r.gb) {
    const gl = s.going.toLowerCase();
    let cat = null;
    if (gl.startsWith('firm')) cat = 'firm';
    else if (gl.startsWith('good')) cat = 'good';
    else if (gl.startsWith('soft')) cat = 'soft';
    else if (gl.startsWith('heavy')) cat = 'heavy';
    if (cat && r.gb[cat] && r.gb[cat].starts) {
      const g = r.gb[cat];
      goingPerf = (g.wins || 0) + 'W ' + Math.max(0, (g.places || 0) - (g.wins || 0)) + 'P / ' + g.starts;
    }
  }

  // Drift
  let driftStr = '—';
  if (typeof PRICE_HIST !== 'undefined' && PRICE_HIST) {
    const ph = PRICE_HIST[String(s.run_id)];
    if (ph && ph.o && ph.r) {
      const pct = ((ph.r - ph.o) / ph.o) * 100;
      if (Math.abs(pct) >= 1) {
        driftStr = '$' + ph.o.toFixed(2) + ' → $' + ph.r.toFixed(2) + ' (' + (pct > 0 ? '+' : '') + pct.toFixed(0) + '%)';
      } else {
        driftStr = '$' + ph.o.toFixed(2) + ' (steady)';
      }
    }
  }

  // Settles
  let settleStr = '—';
  if (r.asp != null) {
    if (r.asp <= 2.5) settleStr = 'Lead (' + r.asp.toFixed(1) + ')';
    else if (r.asp <= 4.5) settleStr = 'On-pace (' + r.asp.toFixed(1) + ')';
    else if (r.asp <= 8.5) settleStr = 'Mid (' + r.asp.toFixed(1) + ')';
    else settleStr = 'Back (' + r.asp.toFixed(1) + ')';
  }

  function field(label, value) {
    if (value == null || value === '' || value === '—') return '';
    return '<div class="pd-field"><span class="fl">' + label + '</span>' +
      '<span class="fv">' + escapeHtml(String(value)) + '</span></div>';
  }

  const tfDetail = s.top != null ? '$' + s.top.toFixed(2) : '— post-race';
  const spDetail = s.sp != null ? '$' + s.sp.toFixed(2) : '— post-race';

  // Jockey + Trainer rating context: rating + rank in race + delta to #1.
  // Same logic as Today tab. The settled bet doesn't carry full race
  // context, so we look up the race via s.race_id and read runners.
  function ratingContext(getter) {
    const myVal = getter(r);
    if (myVal == null) return null;
    const race = (typeof RACES !== 'undefined' && RACES)
      ? RACES.find(rc => String(rc.race_id) === String(s.race_id))
      : null;
    const runners = (race && race.runners) ? race.runners : [];
    const valid = runners.filter(u => getter(u) != null);
    if (valid.length === 0) return Math.round(myVal).toString();
    valid.sort((a, b) => getter(b) - getter(a));
    const myIdx = valid.findIndex(u => String(u.rid) === String(s.run_id));
    const rank = myIdx >= 0 ? (myIdx + 1) : null;
    const top = getter(valid[0]);
    const delta = myVal - top;
    let parts = [Math.round(myVal).toString()];
    if (rank != null) parts.push('#' + rank);
    if (rank != null && rank > 1) {
      const d = Math.round(delta);
      if (d < 0) parts.push(d.toString() + ' from #1');
    }
    return parts.join(' · ');
  }
  const jockeyRatingStr = ratingContext(u => u.jrt);
  const trainerRatingStr = ratingContext(u => u.trt);

  const contextHtml = '<div class="pd-context">' +
    field('Form', r.fm) +
    field('Drift', driftStr) +
    field('Settles', settleStr) +
    field('Distance', s.distance ? s.distance + 'm' : null) +
    field('Going', s.going) +
    field('Top Fluc', tfDetail) +
    field('SP', spDetail) +
    field('Distance perf', distPerf) +
    field('Going perf', goingPerf) +
    field('Jockey', r.j || s.jockey) +
    field('Jockey rating', jockeyRatingStr) +
    field('Trainer', r.tn || s.trainer) +
    field('Trainer rating', trainerRatingStr) +
    field('Barrier', r.b) +
    field('Speed rating', r.spd != null ? r.spd.toFixed(0) : null) +
    field('TR rating', r.trr != null ? r.trr.toFixed(1) : null) +
    field('Finish', s.finish ? ord(s.finish) + ' of ' + (s.field_size || (r.fs || '?')) : null) +
    '</div>';

  // "View race in Today tab" link if it's today's date
  const todayStr = new Date().toISOString().slice(0,10);
  const linkHtml = (s.date === todayStr)
    ? '<a class="bh-detail-link" data-action="goto-today" data-run-id="' + s.run_id + '">→ View this pick in Today tab</a>'
    : '';

  // Bet recording: odds-taken + comments
  const oddsValStr = entry.oddsTaken != null ? entry.oddsTaken.toFixed(2) : '';
  const recordHtml =
    '<div class="bh-record">' +
    '<div class="bh-record-row">' +
      '<label>Bet recording</label>' +
      '<div class="bh-record-fields">' +
        '<span class="bh-record-status ' + (entry.placed ? 'on' : '') + '">' +
          (entry.placed ? '✓ Placed' : 'Not bet') + '</span>' +
        (entry.placed
          ? '<input type="number" step="0.01" min="1" data-detail-odds-rid="' + s.run_id + '" placeholder="Odds taken" value="' + oddsValStr + '" />'
          : '') +
      '</div>' +
    '</div>' +
    '<div class="bh-comments">' +
    '<label>Comments</label>' +
    '<textarea placeholder="Notes about this bet (post-mortem, observations, etc.)">' + escapeHtml(entry.comments || '') + '</textarea>' +
    '</div>' +
    '</div>';

  // Dead heat toggle (only for placed bets, mirrors Today tab pattern)
  let adjustmentsHtml = '';
  if (entry.placed) {
    const dhChecked = entry.deadHeat ? 'checked' : '';
    adjustmentsHtml =
      '<div class="pd-section">' +
        '<div class="pd-section-title">Bet adjustments</div>' +
        '<label class="pd-toggle" onclick="event.stopPropagation();">' +
          '<input type="checkbox" data-detail-deadheat-rid="' + s.run_id + '" ' + dhChecked + '>' +
          '<span class="pd-toggle-lbl">Dead heat</span>' +
          '<span class="pd-toggle-help">Halves the return on a winning bet (joint winner)</span>' +
        '</label>' +
      '</div>';
  }

  // First-starter warning: same wording as Race tab banner
  let fsWarningHtml = '';
  if (s.hfs) {
    fsWarningHtml =
      '<div class="pd-fs-warn">' +
        '<span class="icon">⚠</span>' +
        '<div>' +
          '<div class="text">First starter in this race</div>' +
          '<div class="sub">Model signals do not apply to debut runners. Recommend skipping this race.</div>' +
        '</div>' +
      '</div>';
  }

  return linkHtml +
    fsWarningHtml +
    '<div class="pd-section"><div class="pd-section-title">Context</div>' + contextHtml + '</div>' +
    adjustmentsHtml +
    recordHtml;
}

// Wire P&L tab controls (called once at page load)
function wirePnLControls() {
  // Period buttons
  document.querySelectorAll('.pnl-period-btn').forEach(btn => {
    btn.addEventListener('click', () => {
      pnlState.period = btn.dataset.period;
      document.querySelectorAll('.pnl-period-btn').forEach(b => b.classList.remove('active'));
      btn.classList.add('active');
      const customRange = document.getElementById('pnl-custom-range');
      customRange.style.display = (pnlState.period === 'custom') ? 'flex' : 'none';
      renderPnL();
    });
  });
  // Custom date inputs
  const fromInput = document.getElementById('pnl-date-from');
  const toInput = document.getElementById('pnl-date-to');
  if (fromInput) fromInput.addEventListener('change', e => { pnlState.customFrom = e.target.value; if (pnlState.period === 'custom') renderPnL(); });
  if (toInput) toInput.addEventListener('change', e => { pnlState.customTo = e.target.value; if (pnlState.period === 'custom') renderPnL(); });
  // View toggle
  document.querySelectorAll('.pnl-view-btn').forEach(btn => {
    btn.addEventListener('click', () => {
      pnlState.view = btn.dataset.view;
      document.querySelectorAll('.pnl-view-btn').forEach(b => b.classList.remove('active'));
      btn.classList.add('active');
      renderPnL();
    });
  });
  // Filter checkbox. State is loaded from localStorage on init (see pnlState
  // defaults) and persisted on change so the user's preference sticks across
  // sessions and page reloads.
  const filterChk = document.getElementById('bh-filter-only-bet');
  if (filterChk) {
    filterChk.checked = pnlState.filterOnlyBet;
    filterChk.addEventListener('change', e => {
      pnlState.filterOnlyBet = e.target.checked;
      try { localStorage.setItem('tr_pnl_filter_only_bet_v1', e.target.checked ? '1' : '0'); } catch(err) {}
      renderPnL();
    });
  }
  // Export CSV
  const exportBtn = document.getElementById('bh-export');
  if (exportBtn) exportBtn.addEventListener('click', exportSettledCSV);
  // Goto today link delegation (handled at body since detail rendered later)
  document.body.addEventListener('click', (ev) => {
    if (ev.target.dataset && ev.target.dataset.action === 'goto-today') {
      ev.preventDefault();
      // Switch to Today tab
      document.querySelectorAll('.tab').forEach(t => t.classList.remove('active'));
      document.querySelectorAll('.section').forEach(s => s.classList.remove('active'));
      const todayTab = document.querySelector('.tab[data-tab="today"]');
      const todaySec = document.getElementById('sec-today');
      if (todayTab) todayTab.classList.add('active');
      if (todaySec) todaySec.classList.add('active');
      renderTodayList();
      // Scroll to the runner
      setTimeout(() => {
        const rows = document.querySelectorAll('.pick-row');
        rows.forEach(r => {
          if (r.dataset.runId === ev.target.dataset.runId) {
            r.scrollIntoView({ behavior: 'smooth', block: 'center' });
            r.style.animation = 'highlight 1.5s';
          }
        });
      }, 100);
    }
  });
}

function exportSettledCSV() {
  const settled = SETTLED || [];
  const log = getBetLog();
  const rows = [['date','venue','race','horse','tab','fxd','sp','top','odds_taken','finish','won','placed','pl_units','comments']];
  settled.forEach(s => {
    const e = log[String(s.run_id)] || {};
    const stake = calcStake(s.fxprice);
    const price = effectivePrice(s, e);
    const pl = stake ? (s.won ? stake * (price - 1) : -stake) : 0;
    rows.push([
      s.date || '', s.venue || '', s.race || '', s.horse || '', s.tab || '',
      s.fxprice || '', s.sp || '', s.top || '',
      e.oddsTaken || '',
      s.finish || '',
      s.won ? '1' : '0',
      e.placed ? '1' : '0',
      pl.toFixed(2),
      (e.comments || '').replace(/\n/g, ' ').replace(/"/g, '""'),
    ]);
  });
  const csv = rows.map(r => r.map(v => '"' + String(v) + '"').join(',')).join('\n');
  const blob = new Blob([csv], { type: 'text/csv' });
  const a = document.createElement('a');
  a.href = URL.createObjectURL(blob);
  a.download = 'toprate_settled_' + new Date().toISOString().slice(0,10) + '.csv';
  a.click();
}



// ── TRACKING tab rendering ─────────────────────────────────────────────────
// Three sections:
//   1. Signal heatmap   - WR% per signal at top-1/3/5 across resulted races
//   2. Winners table    - one row per resulted race showing winner's signal ranks
//   3. Placegetters     - 1st/2nd/3rd per race with all signal ranks
//
// All sections respect a single period filter (7/30/90 days). Data source is
// SETTLED (model picks with results) plus RACES (full field data including
// finish positions and per-runner signal values).

let trackingPeriod = '30';   // '7' | '30' | '90'
// trackingMode controls 6 pick-based sections (threshold, dow, venue,
// distance, going, field size). Three modes (matches P&L tab vocab):
//   'actual'      - bets you actually placed (P&L bet toggle = on).
//                   "what I really wagered".
//   'theoretical' - all V3 model picks regardless of placement. Same data
//                   the P&L tab shows under its Theoretical view. Default.
//   'all'         - every horse in every resulted race, no model filter.
//                   Raw predictive power of the cumulative score.
// The other sections (heatmap, correlation, winners, placegetters) operate
// on all resulted races regardless of this toggle.
const TRACKING_MODE_KEY = 'tr_tracking_mode_v2';
let trackingMode = (function() {
  try {
    const v = localStorage.getItem(TRACKING_MODE_KEY);
    if (v === 'actual' || v === 'theoretical' || v === 'all') return v;
  } catch(e) {}
  return 'theoretical';  // default = same as P&L's Theoretical view
})();
// Model selector for the 6 pick-based tracking sections. Filters the
// underlying SETTLED list by the pick's model_id so Main and Loose can
// be analysed separately (mixing them defaults blurs both models' true
// performance since they have different volume profiles: Main ~7/day,
// Loose ~20/day). Default 'main' = production model.
//   'main'  - only picks where model_id == 'main' (production rule).
//   'loose' - only picks where model_id == 'loose' (experimental rule).
//   'both'  - union of both. A horse picked by both models appears twice
//             in the underlying list and contributes to each section's
//             totals separately. This was the implicit behaviour before
//             the toggle existed.
const TRACKING_MODEL_KEY = 'tr_tracking_model_v1';
let trackingModel = (function() {
  try {
    const v = localStorage.getItem(TRACKING_MODEL_KEY);
    if (v === 'main' || v === 'loose' || v === 'both') return v;
  } catch(e) {}
  return 'main';
})();
let trackingSortCol = 'date';
let trackingSortDir = 'desc';
// Winners-table filter state. Show only winners where signal X had rank
// >= rankFilter (i.e. signal MISSED the winner). Useful for spotting which
// signals are dropping known winners.
let winnersFilterSig = '';   // empty = no filter
let winnersFilterMin = 0;    // 0 = no minimum
let winnersFilterMax = 99;   // 99 = no maximum
// Free-text horse/venue filter
let winnersTextFilter = '';

// The 12 signals shown on each row: Score (cumulative rank) first, then
// the 11 individual signals (model rule signals + supporting context).
const TRACKING_SIGNALS = [
  // Score (cumulative score rank) - leads the list since it's the headline
  // metric. Already a rank (lower = better) so rankField is true.
  { key: 'score', label: 'Score', field: 'crk', rankField: true },
  { key: 'wpr',   label: 'WPR',   field: 'w' },        // raw value, sort desc
  { key: 'late',  label: 'Late',  field: 'ls' },
  { key: 'class', label: 'Class', field: 'wcR',  rankField: true }, // rank, sort asc
  { key: 'l600',  label: 'L600',  field: 'l600R', rankField: true },
  { key: 'pfai',  label: 'PFAI',  field: 'pfaiR', rankField: true },
  { key: 'tr',    label: 'TR',    field: 'trr' },
  { key: 'mid',   label: 'Mid',   field: 'ms' },
  { key: 'total', label: 'Total', field: 'ts' },
  { key: 'l400',  label: 'L400',  field: 'l400R', rankField: true },
  { key: 'l200',  label: 'L200',  field: 'l200R', rankField: true },
  { key: 'time',  label: 'Time',  field: 'tR',    rankField: true },
];

// Compute per-race within-field rank for one signal.
// rankField=true means the value already IS a rank (lower = better).
// rankField=false means it's a raw value (higher = better, rank 1 = highest).
function rankInRace(runners, rid, sigDef) {
  const me = runners.find(u => String(u.rid) === String(rid));
  if (!me) return null;
  const v = me[sigDef.field];
  if (v == null) return null;
  if (sigDef.rankField) return Math.round(v);
  // value-based: rank 1 = highest
  const valid = runners.filter(u => u[sigDef.field] != null);
  valid.sort((a, b) => b[sigDef.field] - a[sigDef.field]);
  const idx = valid.findIndex(u => String(u.rid) === String(rid));
  return idx >= 0 ? idx + 1 : null;
}

// Get all resulted races (where finish_position is known for at least one runner)
// filtered to the period. Returns array of races with their original runners array.
function trackingResultedRaces(daysOverride) {
  // daysOverride lets callers (e.g. period comparison) pull a different window
  // than the active trackingPeriod state. Most callers just use the default.
  const days = daysOverride != null ? daysOverride : parseInt(trackingPeriod, 10);
  const cutoff = new Date(Date.now() - days * 86400000);
  const cutoffStr = cutoff.toISOString().slice(0, 10);
  return (RACES || [])
    .filter(r => r.done === 1 || (r.runners || []).some(u => u.f != null))
    .filter(r => (r.date || '') >= cutoffStr);
}

// Compute heatmap buckets for a given race set. Pulled out so we can call it
// for multiple windows (7/30/90 days) for the period comparison footer.
// Mirrors the inline logic in renderSignalHeatmap.
function computeHeatmapBuckets(races) {
  const buckets = {};
  TRACKING_SIGNALS.forEach(sig => {
    buckets[sig.key] = { t1n: 0, t1h: 0, t3n: 0, t3h: 0, t5n: 0, t5h: 0 };
  });
  races.forEach(race => {
    const runners = race.runners || [];
    const winnerRid = (runners.find(u => u.f === 1) || {}).rid;
    if (!winnerRid) return;
    TRACKING_SIGNALS.forEach(sig => {
      runners.forEach(u => {
        const r = rankInRace(runners, u.rid, sig);
        if (r == null) return;
        const isWinner = String(u.rid) === String(winnerRid);
        if (r === 1) { buckets[sig.key].t1n++; if (isWinner) buckets[sig.key].t1h++; }
        if (r <= 3) { buckets[sig.key].t3n++; if (isWinner) buckets[sig.key].t3h++; }
        if (r <= 5) { buckets[sig.key].t5n++; if (isWinner) buckets[sig.key].t5h++; }
      });
    });
  });
  return buckets;
}

function rankPillCls(rank) {
  if (rank == null) return 'r-out';
  if (rank <= 3) return 'r-top';
  if (rank <= 5) return 'r-mid';
  return 'r-out';
}

function rankPill(rank) {
  if (rank == null) return '<span class="rank-pill r-out">—</span>';
  return '<span class="rank-pill ' + rankPillCls(rank) + '">' + rank + '</span>';
}

// Heatmap colour bucket: 0..80%+
function heatmapClass(pct) {
  // Legacy function kept for any other callers - now just returns base class.
  // Use heatmapStyle() for the new continuous gradient inline styling.
  if (pct == null || pct === 0) return 'hm0';
  return 'hm-grad';
}

// Continuous heatmap colour: maps a win-rate percentage to an inline style.
// Anchors:
//   < 10% (below random baseline for top-1 in 10-runner field) = neutral grey
//   = 10% (random)                                              = white
//   > 10% scales linearly to bright emerald at 40%+
// This gives instantly-readable contrast: weak signals fade, strong pop.
// Note: 10% is the rough random baseline for top-1 picks; for top-3/5 the
// random baselines are higher (~30%, ~50%) but using 10% across the board
// keeps the interpretation simple - "above 10% means signal has some edge".
function heatmapStyle(pct) {
  if (pct == null) return 'background: #f3f4f6; color: #9ca3af;';
  // Linear interpolation: 0% white, 40% strong emerald
  // Clamp to range
  const clamped = Math.max(0, Math.min(40, pct));
  // Below 10% = grey (signal noise / dead)
  if (clamped < 10) {
    const greyScale = clamped / 10;  // 0..1
    const lightness = 96 - (greyScale * 4);  // 96 down to 92
    return 'background: hsl(0, 0%, ' + lightness.toFixed(0) + '%); color: #6b7280;';
  }
  // 10-40% = emerald gradient. 10% = pale, 40% = strong
  const emeraldT = (clamped - 10) / 30;  // 0..1
  // Use HSL for smooth colour interpolation. emerald at 158deg.
  const lightness = 95 - (emeraldT * 38);  // 95% down to 57%
  const saturation = 35 + (emeraldT * 35); // 35% up to 70%
  const textColor = emeraldT > 0.5 ? '#064e3b' : '#065f46';
  return 'background: hsl(158, ' + saturation.toFixed(0) + '%, ' + lightness.toFixed(0) + '%); color: ' + textColor + '; font-weight: 600;';
}

// Master tracking renderer - called whenever period changes
function renderInsights() {
  const races = trackingResultedRaces();

  // Summary line
  const summaryEl = document.getElementById('insights-summary');
  if (summaryEl) {
    const totalRaces = races.length;
    const totalRunners = races.reduce((s, r) => s + (r.runners || []).length, 0);
    const periodLbl = 'last ' + trackingPeriod + ' days';
    // Add model-filter context when not in 'all races' mode and not 'both'.
    // Lets the user see at a glance which model's stats they're viewing.
    let modelLbl = '';
    if (trackingMode !== 'all' && trackingModel !== 'both') {
      modelLbl = ' · ' + (trackingModel === 'main' ? 'Main' : 'Loose') + ' model';
    }
    summaryEl.textContent = totalRaces + ' resulted races · ' + totalRunners + ' runners · ' + periodLbl + modelLbl;
  }

  renderSignalHeatmap(races);
  renderTrackingWinners(races);
  renderSignalCorrelation(races);
  renderThresholdCurve(races);
  renderDowBreakdown(races);
  renderVenuePerformance(races);
  renderDistanceBreakdown(races);
  renderGoingBreakdown(races);
  renderFieldSizeBreakdown(races);
  renderTrackingPlacegetters(races);
}

// ── Section 1: Signal Heatmap ────────────────────────────────────────────
// For each signal, compute WR% of horses ranked top-1/3/5 across all resulted races.
function renderSignalHeatmap(races) {
  const el = document.getElementById('signal-heatmap');
  if (!el) return;
  if (races.length === 0) {
    el.innerHTML = '<div class="empty-text">No resulted races in the selected period.</div>';
    return;
  }

  // For each signal, count {top1Hits, top3Hits, top5Hits, top1N, top3N, top5N}
  const buckets = {};
  TRACKING_SIGNALS.forEach(sig => buckets[sig.key] = { t1h: 0, t1n: 0, t3h: 0, t3n: 0, t5h: 0, t5n: 0 });

  races.forEach(race => {
    const runners = race.runners || [];
    // Find the winner (finish_position == 1)
    const winnerRid = (runners.find(u => u.f === 1) || {}).rid;
    if (!winnerRid) return;
    TRACKING_SIGNALS.forEach(sig => {
      runners.forEach(u => {
        const r = rankInRace(runners, u.rid, sig);
        if (r == null) return;
        const isWinner = String(u.rid) === String(winnerRid);
        if (r === 1) { buckets[sig.key].t1n++; if (isWinner) buckets[sig.key].t1h++; }
        if (r <= 3) { buckets[sig.key].t3n++; if (isWinner) buckets[sig.key].t3h++; }
        if (r <= 5) { buckets[sig.key].t5n++; if (isWinner) buckets[sig.key].t5h++; }
      });
    });
  });

  // Random baselines for top-N picks in average 10-runner field. These are
  // the floor each signal needs to clear to demonstrate ANY predictive edge.
  // Top-1: 1/10 = 10%, Top-3: 3/10 = 30%, Top-5: 5/10 = 50%.
  const BASELINE = { 1: 10, 3: 30, 5: 50 };

  let html = '<div class="heatmap-grid">' +
    '<div class="hm-cell hm-head">Signal</div>' +
    '<div class="hm-cell hm-head">Top-1 WR%<div class="hm-baseline">vs 10% random</div></div>' +
    '<div class="hm-cell hm-head">Top-3 WR%<div class="hm-baseline">vs 30% random</div></div>' +
    '<div class="hm-cell hm-head">Top-5 WR%<div class="hm-baseline">vs 50% random</div></div>';
  TRACKING_SIGNALS.forEach(sig => {
    const b = buckets[sig.key];
    const wr1 = b.t1n > 0 ? (b.t1h / b.t1n * 100) : null;
    const wr3 = b.t3n > 0 ? (b.t3h / b.t3n * 100) : null;
    const wr5 = b.t5n > 0 ? (b.t5h / b.t5n * 100) : null;
    function valHtml(wr, n, level) {
      if (wr == null || n === 0) return '<div class="hm-cell hm-val hm0">—</div>';
      const hits = level === 1 ? b.t1h : (level === 3 ? b.t3h : b.t5h);
      const baseline = BASELINE[level];
      const edge = wr - baseline;
      const edgeStr = (edge >= 0 ? '+' : '') + edge.toFixed(1);
      // Edge label: shows how far above/below random this signal is performing.
      // Useful because 13% top-1 looks "low" but is actually +3% over random.
      // The headline number stays as the WR%; edge is a small subscript.
      const edgeCls = edge >= 5 ? 'hm-edge-strong' :
                      edge >= 1 ? 'hm-edge-pos' :
                      edge <= -3 ? 'hm-edge-neg' : 'hm-edge-flat';
      const tooltip = hits + ' winners / ' + n + ' picks. ' +
                      'Random baseline for this level: ' + baseline + '%. ' +
                      'Signal edge: ' + edgeStr + ' percentage points.';
      return '<div class="hm-cell hm-val" style="' + heatmapStyle(wr) + '" title="' + tooltip + '">' +
        wr.toFixed(1) + '%' +
        '<div class="hm-edge ' + edgeCls + '">' + edgeStr + '</div>' +
        '</div>';
    }
    html += '<div class="hm-cell hm-name">' + sig.label + '</div>' +
      valHtml(wr1, b.t1n, 1) + valHtml(wr3, b.t3n, 3) + valHtml(wr5, b.t5n, 5);
  });
  html += '</div>';
  el.innerHTML = html;

  // Period comparison: show top-1 WR for the top-performing signals across
  // 7/30/90 day windows so user can spot decay or improvement. Only shown
  // when current period is not 90d (otherwise the comparison would be against
  // the same window). Renders below the heatmap as a small strip.
  const cmpHost = document.getElementById('heatmap-period-cmp');
  if (cmpHost) {
    const currentDays = parseInt(trackingPeriod, 10);
    const otherWindows = [7, 30, 90].filter(d => d !== currentDays);
    // Pick the 3 strongest signals at the CURRENT window (by top-1 WR) to compare
    const wrAtCurrent = TRACKING_SIGNALS
      .map(sig => ({ sig: sig, wr: buckets[sig.key].t1n > 0 ? (buckets[sig.key].t1h / buckets[sig.key].t1n * 100) : -1 }))
      .filter(o => o.wr > 0)
      .sort((a, b) => b.wr - a.wr)
      .slice(0, 3);
    if (wrAtCurrent.length === 0 || otherWindows.length === 0) {
      cmpHost.innerHTML = '';
    } else {
      // Compute buckets for other windows
      const otherBuckets = {};
      otherWindows.forEach(d => {
        otherBuckets[d] = computeHeatmapBuckets(trackingResultedRaces(d));
      });
      let cmpHtml = '<div class="hm-cmp-title">Top-1 WR across windows</div>' +
                    '<div class="hm-cmp-rows">';
      wrAtCurrent.forEach(o => {
        cmpHtml += '<div class="hm-cmp-row">' +
          '<span class="hm-cmp-sig">' + o.sig.label + '</span>';
        // Show current first, then others, with arrow indicators for trend
        const allDays = [currentDays].concat(otherWindows).sort((a, b) => a - b);
        allDays.forEach(d => {
          let wr;
          if (d === currentDays) {
            wr = o.wr;
          } else {
            const ob = otherBuckets[d][o.sig.key];
            wr = ob.t1n > 0 ? (ob.t1h / ob.t1n * 100) : null;
          }
          const cur = d === currentDays;
          cmpHtml += '<span class="hm-cmp-cell' + (cur ? ' cur' : '') + '">' +
            '<span class="lbl">' + d + 'd</span>' +
            '<span class="val">' + (wr != null ? wr.toFixed(1) + '%' : '—') + '</span>' +
            '</span>';
        });
        cmpHtml += '</div>';
      });
      cmpHtml += '</div>';
      cmpHost.innerHTML = cmpHtml;
    }
  }
}

// ── Section 2: Winners table ─────────────────────────────────────────────
// One row per resulted race. Columns: Date · Meeting (link) · Race · Distance ·
// Winner horse · Win SP · then 12 signal-rank cells (Score + 11 signals).
function renderTrackingWinners(races) {
  const el = document.getElementById('tracking-winners');
  if (!el) return;
  if (races.length === 0) {
    el.innerHTML = '<div class="empty-text">No resulted races.</div>';
    return;
  }

  // Build row data
  let rows = races.map(race => {
    const runners = race.runners || [];
    const winner = runners.find(u => u.f === 1);
    if (!winner) return null;
    const ranks = {};
    TRACKING_SIGNALS.forEach(sig => {
      ranks[sig.key] = rankInRace(runners, winner.rid, sig);
    });
    return {
      race_id: race.race_id,
      date: race.date || '',
      venue: race.venue || '',
      race: race.race || 0,
      distance: race.distance || 0,
      horse: winner.h || '',
      sp: winner.sp,
      ranks: ranks,
    };
  }).filter(r => r != null);

  const totalRows = rows.length;

  // Apply filters BEFORE sort (filter then sort is cheaper since filtered set
  // is usually smaller). The filters are:
  //   - signal-rank: winners where signal X had rank in [min, max]
  //   - text: substring match on horse name or venue (case-insensitive)
  if (winnersFilterSig && winnersFilterSig !== '') {
    rows = rows.filter(r => {
      const v = r.ranks[winnersFilterSig];
      if (v == null) return false;
      return v >= winnersFilterMin && v <= winnersFilterMax;
    });
  }
  if (winnersTextFilter && winnersTextFilter.length > 0) {
    const needle = winnersTextFilter.toLowerCase();
    rows = rows.filter(r =>
      r.horse.toLowerCase().includes(needle) ||
      r.venue.toLowerCase().includes(needle)
    );
  }

  // Sort
  rows.sort((a, b) => {
    let av, bv;
    if (trackingSortCol === 'date')      { av = a.date + a.venue + a.race; bv = b.date + b.venue + b.race; }
    else if (trackingSortCol === 'venue'){ av = a.venue; bv = b.venue; }
    else if (trackingSortCol === 'horse'){ av = a.horse.toLowerCase(); bv = b.horse.toLowerCase(); }
    else if (trackingSortCol === 'sp')   { av = a.sp || 9999; bv = b.sp || 9999; }
    else { // signal rank
      av = a.ranks[trackingSortCol] != null ? a.ranks[trackingSortCol] : 99;
      bv = b.ranks[trackingSortCol] != null ? b.ranks[trackingSortCol] : 99;
    }
    if (typeof av === 'string') return trackingSortDir === 'desc' ? bv.localeCompare(av) : av.localeCompare(bv);
    return trackingSortDir === 'desc' ? bv - av : av - bv;
  });

  function thW(col, label) {
    const isCur = trackingSortCol === col;
    const cls = ['sortable'];
    if (isCur) cls.push('sort-' + trackingSortDir);
    return '<th class="' + cls.join(' ') + '" data-tsort="' + col + '">' + label + '</th>';
  }

  // Filter bar: signal+rank selector and free-text input. Renders above the
  // table so users can narrow the view without losing context. Shows result
  // count "Showing X of Y" so users know if filters are active.
  const sigOpts = '<option value="">— signal —</option>' +
    TRACKING_SIGNALS.map(s =>
      '<option value="' + s.key + '"' + (winnersFilterSig === s.key ? ' selected' : '') + '>' +
      s.label + '</option>').join('');
  const filterBar =
    '<div class="winners-filter-bar">' +
      '<div class="wfb-group">' +
        '<label class="wfb-lbl">Filter by rank:</label>' +
        '<select id="winners-filter-sig" class="wfb-select">' + sigOpts + '</select>' +
        '<span class="wfb-range">' +
          '<input type="number" id="winners-filter-min" class="wfb-num" min="1" max="99" value="' + winnersFilterMin + '" title="Min rank">' +
          '<span class="wfb-dash">to</span>' +
          '<input type="number" id="winners-filter-max" class="wfb-num" min="1" max="99" value="' + winnersFilterMax + '" title="Max rank">' +
        '</span>' +
      '</div>' +
      '<div class="wfb-group">' +
        '<label class="wfb-lbl">Search:</label>' +
        '<input type="text" id="winners-filter-text" class="wfb-text" placeholder="horse or venue" value="' + escapeHtml(winnersTextFilter) + '">' +
      '</div>' +
      '<div class="wfb-group wfb-info">' +
        '<button class="wfb-clear" id="winners-filter-clear" title="Clear all filters">Clear</button>' +
        '<span class="wfb-count">' + rows.length + ' of ' + totalRows + '</span>' +
      '</div>' +
    '</div>';

  let html = filterBar + '<div class="tracking-table-wrap"><table class="tracking-table tracking-winners"><thead><tr>' +
    thW('date', 'Date') +
    thW('venue', 'Meeting') +
    '<th>Race</th>' +
    '<th>Dist</th>' +
    thW('horse', 'Winner') +
    thW('sp', 'SP') ;
  TRACKING_SIGNALS.forEach(sig => { html += thW(sig.key, sig.label); });
  html += '</tr></thead><tbody>';

  rows.forEach(r => {
    html += '<tr>' +
      '<td>' + escapeHtml(r.date) + '</td>' +
      '<td><a class="meeting-link" href="#" data-nav-rid="' + escapeHtml(String(r.race_id)) + '">' + escapeHtml(r.venue) + '</a></td>' +
      '<td>R' + r.race + '</td>' +
      '<td>' + r.distance + 'm</td>' +
      '<td class="horse-cell">' + escapeHtml(r.horse) + '</td>' +
      '<td class="price-cell">' + (r.sp != null ? '$' + r.sp.toFixed(2) : '—') + '</td>';
    TRACKING_SIGNALS.forEach(sig => { html += '<td>' + rankPill(r.ranks[sig.key]) + '</td>'; });
    html += '</tr>';
  });
  html += '</tbody></table></div>';
  el.innerHTML = html;

  // Wire sort headers
  el.querySelectorAll('th.sortable').forEach(th => {
    th.addEventListener('click', () => {
      const col = th.dataset.tsort;
      if (trackingSortCol === col) {
        trackingSortDir = trackingSortDir === 'asc' ? 'desc' : 'asc';
      } else {
        trackingSortCol = col;
        // Most signal/numeric cols default to ASC (1 = best); date/sp default DESC
        const ascDefault = ['horse', 'venue'];
        const descDefault = ['date', 'sp'];
        if (ascDefault.includes(col)) trackingSortDir = 'asc';
        else if (descDefault.includes(col)) trackingSortDir = 'desc';
        else trackingSortDir = 'asc';
      }
      renderTrackingWinners(trackingResultedRaces());
    });
  });
  // Wire meeting links
  el.querySelectorAll('a.meeting-link').forEach(a => {
    a.addEventListener('click', e => {
      e.preventDefault();
      const rid = a.dataset.navRid;
      if (typeof navigateToRace === 'function') navigateToRace(rid);
    });
  });
  // Wire filter controls. Each input/select triggers a re-render but
  // preserves the user's focus state via a debounce on text input.
  let winnersTextDebounce = null;
  const sigSel = document.getElementById('winners-filter-sig');
  const minInp = document.getElementById('winners-filter-min');
  const maxInp = document.getElementById('winners-filter-max');
  const txtInp = document.getElementById('winners-filter-text');
  const clrBtn = document.getElementById('winners-filter-clear');
  if (sigSel) sigSel.addEventListener('change', e => {
    winnersFilterSig = e.target.value;
    renderTrackingWinners(trackingResultedRaces());
  });
  if (minInp) minInp.addEventListener('change', e => {
    winnersFilterMin = Math.max(0, parseInt(e.target.value, 10) || 0);
    renderTrackingWinners(trackingResultedRaces());
  });
  if (maxInp) maxInp.addEventListener('change', e => {
    winnersFilterMax = Math.max(1, parseInt(e.target.value, 10) || 99);
    renderTrackingWinners(trackingResultedRaces());
  });
  if (txtInp) txtInp.addEventListener('input', e => {
    if (winnersTextDebounce) clearTimeout(winnersTextDebounce);
    const val = e.target.value;
    winnersTextDebounce = setTimeout(() => {
      winnersTextFilter = val;
      renderTrackingWinners(trackingResultedRaces());
      // Re-focus and put cursor at end so user can keep typing
      const inp = document.getElementById('winners-filter-text');
      if (inp) {
        inp.focus();
        inp.setSelectionRange(val.length, val.length);
      }
    }, 200);
  });
  if (clrBtn) clrBtn.addEventListener('click', () => {
    winnersFilterSig = '';
    winnersFilterMin = 0;
    winnersFilterMax = 99;
    winnersTextFilter = '';
    renderTrackingWinners(trackingResultedRaces());
  });
}

// ── Section 3: Signal correlation matrix ─────────────────────────────────
// For each pair of signals, what % of races did they agree on which horse
// is ranked #1? Useful for detecting redundancy: if WPR and TR agree 90% of
// the time, you're effectively just using one signal twice in your voting.
// Conversely if PFAI and Late only agree 30% of the time, they're capturing
// genuinely different information.
function renderSignalCorrelation(races) {
  const el = document.getElementById('signal-correlation');
  if (!el) return;
  if (races.length === 0) {
    el.innerHTML = '<div class="empty-text">No resulted races in the selected period.</div>';
    return;
  }

  // Only include signals that are part of the V3 voting model. Including all
  // 11 would make the matrix unreadable on screen and most of the non-voting
  // signals aren't decision-relevant anyway.
  const VOTING_KEYS = ['wpr', 'late', 'class', 'l600', 'pfai', 'tr'];
  const sigs = TRACKING_SIGNALS.filter(s => VOTING_KEYS.includes(s.key));

  // For each pair (i, j) compute agreement: % of races where rank-1 horse
  // for signal i == rank-1 horse for signal j.
  const N = sigs.length;
  const agreement = Array.from({ length: N }, () => Array(N).fill(null));
  const counts = Array.from({ length: N }, () => Array(N).fill(0));

  for (let i = 0; i < N; i++) {
    agreement[i][i] = 100;  // self-agreement is always 100%
    counts[i][i] = races.length;
    for (let j = i + 1; j < N; j++) {
      let agree = 0, total = 0;
      races.forEach(race => {
        const runners = race.runners || [];
        if (runners.length === 0) return;
        // Find rank-1 horse for each signal in this race
        const top_i = topRankedHorse(runners, sigs[i]);
        const top_j = topRankedHorse(runners, sigs[j]);
        if (top_i == null || top_j == null) return;
        total++;
        if (String(top_i) === String(top_j)) agree++;
      });
      const pct = total > 0 ? (agree / total * 100) : null;
      agreement[i][j] = pct;
      agreement[j][i] = pct;
      counts[i][j] = total;
      counts[j][i] = total;
    }
  }

  // Render as a grid: first row = column headers, then one row per signal
  // with values in each column. Colour scale similar to heatmap but inverted:
  // HIGH agreement = redundancy = warm/orange tones; LOW = good = green.
  function corrStyle(pct) {
    if (pct == null) return 'background: #f3f4f6; color: #9ca3af;';
    if (pct === 100) return 'background: #1f2937; color: #f9fafb; font-weight: 700;';  // self
    // 30%..90% maps to green..orange
    const clamped = Math.max(30, Math.min(90, pct));
    const t = (clamped - 30) / 60;  // 0..1 where 1 = high redundancy
    // Hue: 158 (emerald) -> 25 (orange) as t increases
    const hue = 158 - (t * 133);
    const lightness = 92 - (t * 30);
    const saturation = 35 + (t * 35);
    return 'background: hsl(' + hue.toFixed(0) + ', ' + saturation.toFixed(0) + '%, ' + lightness.toFixed(0) + '%); ' +
           'color: ' + (t > 0.6 ? '#7c2d12' : '#064e3b') + '; font-weight: 600;';
  }

  let html = '<div class="corr-grid" style="grid-template-columns: 80px repeat(' + N + ', 1fr);">' +
    '<div class="corr-cell corr-head"></div>';
  sigs.forEach(s => {
    html += '<div class="corr-cell corr-head">' + s.label + '</div>';
  });
  for (let i = 0; i < N; i++) {
    html += '<div class="corr-cell corr-row-head">' + sigs[i].label + '</div>';
    for (let j = 0; j < N; j++) {
      const pct = agreement[i][j];
      const cnt = counts[i][j];
      const cell = pct == null ?
        '<div class="corr-cell corr-val" style="background:#f3f4f6;color:#9ca3af;">—</div>' :
        '<div class="corr-cell corr-val" style="' + corrStyle(pct) + '" ' +
          'title="' + sigs[i].label + ' and ' + sigs[j].label + ' agree on top pick in ' +
          pct.toFixed(0) + '% of ' + cnt + ' races">' + pct.toFixed(0) + '%</div>';
      html += cell;
    }
  }
  html += '</div>';

  // Quick interpretation line: find most redundant pair (highest off-diagonal)
  // and least redundant pair (lowest off-diagonal).
  let maxPair = null, minPair = null;
  for (let i = 0; i < N; i++) {
    for (let j = i + 1; j < N; j++) {
      const p = agreement[i][j];
      if (p == null) continue;
      if (maxPair == null || p > maxPair.pct) maxPair = { i, j, pct: p };
      if (minPair == null || p < minPair.pct) minPair = { i, j, pct: p };
    }
  }
  if (maxPair && minPair) {
    html += '<div class="corr-summary">' +
      '<div><span class="lbl">Most redundant:</span> ' +
        sigs[maxPair.i].label + ' &harr; ' + sigs[maxPair.j].label + ' (' + maxPair.pct.toFixed(0) + '%)</div>' +
      '<div><span class="lbl">Most independent:</span> ' +
        sigs[minPair.i].label + ' &harr; ' + sigs[minPair.j].label + ' (' + minPair.pct.toFixed(0) + '%)</div>' +
      '</div>';
  }

  el.innerHTML = html;
}

// Helper: which horse is ranked #1 in a given race for a given signal?
function topRankedHorse(runners, sigDef) {
  let best = null, bestRank = 99;
  runners.forEach(u => {
    const r = rankInRace(runners, u.rid, sigDef);
    if (r != null && r < bestRank) {
      bestRank = r;
      best = u.rid;
    }
  });
  return best;
}

// ── Period-bound settled bets helper ─────────────────────────────────────
// Tracking analytics operate on settled BETS, not raw races. Pulls from
// SETTLED filtered by the active trackingPeriod window. Each entry has the
// fields populated by toprate_html_v3.py:settled_history (line ~358):
//   date, venue, cs (cumulative score), won, sp, top, fxprice, distance,
//   going, field_size.
function trackingSettledBets() {
  const days = parseInt(trackingPeriod, 10);
  const cutoff = new Date(Date.now() - days * 86400000);
  const cutoffStr = cutoff.toISOString().slice(0, 10);
  const all = (typeof SETTLED !== 'undefined' ? SETTLED : [])
    .filter(s => (s.date || '') >= cutoffStr);
  // Model filter - 'both' is pass-through. 'main'/'loose' filters by tag.
  // Older SETTLED entries without an explicit 'model' field default to
  // 'main' since they pre-date the loose model being added.
  if (trackingModel === 'both') return all;
  return all.filter(s => (s.model || 'main') === trackingModel);
}

// Unified data source for the 6 pick-based tracking sections (threshold,
// dow, venue, distance, going, field size). Three modes:
//   - 'actual': only SETTLED bets where bet log has placed=true.
//                "What I actually wagered".
//   - 'theoretical': all SETTLED bets (V3 picks regardless of placement).
//                Same as P&L tab's Theoretical view.
//   - 'all': every horse in every resulted race (no rule filter).
//                Raw cumulative-score predictive power.
// All three modes return records of the same shape so the downstream
// aggregators don't care which mode is active.
function trackingActiveBets(races) {
  if (trackingMode === 'all') {
    return trackingAllRunnerBets(races || []);
  }
  const settled = trackingSettledBets();
  if (trackingMode === 'actual') {
    // Filter to bets the user actually placed. Uses the same bet log
    // helper as the P&L tab so the "Actual" semantics are identical.
    const log = getBetLog();
    return settled.filter(s => {
      const entry = log[String(s.run_id)];
      return !!(entry && entry.placed);
    });
  }
  // 'theoretical' (default): all settled picks
  return settled;
}

// Mode-aware label for the count column header and empty-state message.
// Centralised so the 6 renderers stay in sync if the mode names change.
function trackingCountLabel() {
  if (trackingMode === 'all') return 'Runners';
  if (trackingMode === 'actual') return 'Bets';
  return 'Picks';  // theoretical (default)
}
function trackingEmptyLabel() {
  if (trackingMode === 'all') return 'No resulted runners';
  if (trackingMode === 'actual') return 'No placed bets';
  return 'No model picks';
}

// Aggregate helper: compute pick count, win count, win-rate, and SP-based
// ROI from a list of settled bets. Returns null if no bets contributed.
// ROI is calculated at SP (1u stake): wins return SP-1 units, losses -1.
function aggregateBets(bets) {
  if (bets.length === 0) return null;
  let wins = 0, places = 0, sumProfit = 0, sumStake = 0, oddsList = [];
  bets.forEach(b => {
    if (!(b.sp != null && b.sp > 1)) return;
    sumStake += 1;
    oddsList.push(b.sp);
    if (b.won) {
      wins++;
      sumProfit += (b.sp - 1);
    } else {
      sumProfit -= 1;
    }
    // Place = finished 1st, 2nd, or 3rd. b.placed is set Python-side from
    // finish_position <= 3. Counted separately from wins so Tracking can
    // show place rate as a softer measure of model accuracy (a horse
    // finishing 2nd or 3rd still validates the prediction even though
    // the bet lost on a win-only stake).
    if (b.placed) places++;
  });
  if (sumStake === 0) return null;
  return {
    n: bets.length,
    wins: wins,
    places: places,
    wr: bets.length > 0 ? wins / bets.length : 0,
    placeRate: bets.length > 0 ? places / bets.length : 0,
    roi: sumStake > 0 ? sumProfit / sumStake : 0,
    avgSp: oddsList.length > 0 ? oddsList.reduce((a, b) => a + b, 0) / oddsList.length : null,
  };
}

// Render helper - 4 column stat row: label / N / WR / ROI / Avg SP
function statRow(label, agg, extras) {
  if (agg == null) {
    return '<tr><td class="lbl">' + label + '</td>' +
      '<td colspan="4" class="empty">No bets</td></tr>';
  }
  const wrStr = (agg.wr * 100).toFixed(1) + '%';
  const roiStr = (agg.roi >= 0 ? '+' : '') + (agg.roi * 100).toFixed(1) + '%';
  const roiCls = agg.roi > 0.05 ? 'pos' : agg.roi < -0.05 ? 'neg' : '';
  const avgSpStr = agg.avgSp != null ? '$' + agg.avgSp.toFixed(2) : '—';
  const sample = agg.n < 10 ? ' <span class="small-sample" title="Small sample - results may be noisy">·</span>' : '';
  return '<tr><td class="lbl">' + label + sample + '</td>' +
    '<td class="num">' + agg.n + '</td>' +
    '<td class="num">' + wrStr + '</td>' +
    '<td class="num ' + roiCls + '">' + roiStr + '</td>' +
    '<td class="num">' + avgSpStr + '</td>' +
    (extras || '') +
    '</tr>';
}

// ── Score threshold performance curve ────────────────────────────────────
// At each threshold step, how would you have performed at that threshold?
// Population source determined by the GLOBAL trackingMode (toggle at the
// top of the Tracking tab): either picks (V3 rule applied) or all horses
// in every resulted race (raw score predictive power).
//
// The two views together tell you:
//   - whether the voting rule adds edge beyond raw Score (compare ROIs
//     between modes)
//   - what threshold to use if you wanted to bet outside the voting rule

// Build a synthetic 'bets' list from resulted races (all horses) for the
// 'all' mode. Mirrors the structure of SETTLED entries so aggregateBets()
// works without modification. Only includes runners with both cs and sp,
// since we need a score (for threshold) AND price (for ROI calculation).
function trackingAllRunnerBets(races) {
  const out = [];
  races.forEach(race => {
    (race.runners || []).forEach(u => {
      if (u.cs == null) return;
      if (u.sp == null || u.sp <= 1) return;
      out.push({
        date:    race.date,
        venue:   race.venue,
        distance: race.distance,
        going:    race.going,
        field_size: (race.runners || []).length,
        cs:      u.cs,
        won:     u.won === 1,
        sp:      u.sp,
        top:     u.top,
        fxprice: u.fx,
      });
    });
  });
  return out;
}

function renderThresholdCurve(races) {
  const el = document.getElementById('threshold-curve');
  if (!el) return;
  const source = trackingActiveBets(races);
  if (source.length === 0) {
    el.innerHTML = '<div class="empty-text">No data for the selected mode and period.</div>';
    return;
  }
  // Threshold steps from 0.30 to 0.90 in 0.10 increments
  const steps = [0.30, 0.40, 0.50, 0.60, 0.70, 0.80, 0.90];
  // Column label changes by mode: "Picks" when in picks mode, "Runners"
  // when in all-theoretical mode, since the meaning of the row count differs.
  const countCol = trackingCountLabel();
  // Custom row renderer for this table since it includes Place Rate.
  // Other tracking tables stick with the 4-column statRow shape.
  function thresholdRow(label, agg) {
    if (agg == null) {
      return '<tr><td class="lbl">' + label + '</td>' +
        '<td colspan="5" class="empty">No bets</td></tr>';
    }
    const wrStr  = (agg.wr        * 100).toFixed(1) + '%';
    const prStr  = (agg.placeRate * 100).toFixed(1) + '%';
    const roiStr = (agg.roi >= 0 ? '+' : '') + (agg.roi * 100).toFixed(1) + '%';
    const roiCls = agg.roi > 0.05 ? 'pos' : agg.roi < -0.05 ? 'neg' : '';
    const avgSpStr = agg.avgSp != null ? '$' + agg.avgSp.toFixed(2) : '—';
    const sample = agg.n < 10 ? ' <span class="small-sample" title="Small sample - results may be noisy">·</span>' : '';
    return '<tr><td class="lbl">' + label + sample + '</td>' +
      '<td class="num">' + agg.n + '</td>' +
      '<td class="num">' + wrStr + '</td>' +
      '<td class="num">' + prStr + '</td>' +
      '<td class="num ' + roiCls + '">' + roiStr + '</td>' +
      '<td class="num">' + avgSpStr + '</td>' +
      '</tr>';
  }
  let html = '<table class="tracking-mini-table"><thead><tr>' +
    '<th>Threshold</th><th>' + countCol + '</th><th>WR%</th><th>PR%</th><th>ROI%</th><th>Avg SP</th>' +
    '</tr></thead><tbody>';
  steps.forEach(t => {
    const subset = source.filter(b => b.cs != null && b.cs >= t);
    const agg = aggregateBets(subset);
    html += thresholdRow('>= ' + t.toFixed(2), agg);
  });
  html += '</tbody></table>';
  // Note copy depends on mode - frame the analysis correctly for each view
  let note;
  if (trackingMode === 'actual') {
    note = 'Performance of bets you actually placed (P&L bet toggle = on) at each Score threshold. ' +
      'This is your real wagering record. ROI is at SP, 1u flat stake. ' +
      'PR (place rate) = % finishing top 3.';
  } else if (trackingMode === 'theoretical') {
    note = 'Performance of all V3 model picks (regardless of placement) at each Score threshold. ' +
      'Use this to pick a stake threshold for your live bets. ROI is at SP, 1u flat stake. ' +
      'PR (place rate) = % finishing top 3 - a softer accuracy measure than WR.';
  } else {
    note = 'Performance of EVERY horse in resulted races (no model filtering), grouped by Score. ' +
      'Shows the raw predictive power of the cumulative score independent of the voting rule. ' +
      'Compare ROI here vs Theoretical mode to see how much edge the voting rule adds. ' +
      'PR = place rate (top 3 finish).';
  }
  html += '<div class="tracking-note">' + note +
    '<br>Dot (·) flags small samples (under 10).</div>';
  el.innerHTML = html;
}

// ── Day of week breakdown ────────────────────────────────────────────────
function renderDowBreakdown(races) {
  const el = document.getElementById('dow-breakdown');
  if (!el) return;
  const bets = trackingActiveBets(races);
  if (bets.length === 0) {
    el.innerHTML = '<div class="empty-text">' + trackingEmptyLabel() + ' in the selected period.</div>';
    return;
  }
  const days = ['Sun', 'Mon', 'Tue', 'Wed', 'Thu', 'Fri', 'Sat'];
  // Group by weekday
  const byDay = {};
  days.forEach(d => byDay[d] = []);
  bets.forEach(b => {
    if (!b.date) return;
    const d = new Date(b.date + 'T00:00:00');
    if (isNaN(d.getTime())) return;
    byDay[days[d.getDay()]].push(b);
  });
  let html = '<table class="tracking-mini-table"><thead><tr>' +
    '<th>Day</th><th>' + trackingCountLabel() + '</th><th>WR%</th><th>ROI%</th><th>Avg SP</th>' +
    '</tr></thead><tbody>';
  days.forEach(d => {
    const agg = aggregateBets(byDay[d]);
    html += statRow(d, agg);
  });
  html += '</tbody></table>';
  el.innerHTML = html;
}

// ── Venue performance ────────────────────────────────────────────────────
function renderVenuePerformance(races) {
  const el = document.getElementById('venue-performance');
  if (!el) return;
  const bets = trackingActiveBets(races);
  if (bets.length === 0) {
    el.innerHTML = '<div class="empty-text">' + trackingEmptyLabel() + ' in the selected period.</div>';
    return;
  }
  // Group by venue
  const byVenue = {};
  bets.forEach(b => {
    const v = b.venue || 'Unknown';
    if (!byVenue[v]) byVenue[v] = [];
    byVenue[v].push(b);
  });
  // Sort by pick count desc, then take top 15
  const venues = Object.entries(byVenue)
    .map(([v, bs]) => ({ venue: v, bets: bs, agg: aggregateBets(bs) }))
    .filter(o => o.agg != null)
    .sort((a, b) => b.bets.length - a.bets.length)
    .slice(0, 15);
  if (venues.length === 0) {
    el.innerHTML = '<div class="empty-text">No venue data.</div>';
    return;
  }
  let html = '<table class="tracking-mini-table"><thead><tr>' +
    '<th>Venue</th><th>' + trackingCountLabel() + '</th><th>WR%</th><th>ROI%</th><th>Avg SP</th>' +
    '</tr></thead><tbody>';
  venues.forEach(v => {
    const rowOpacity = v.bets.length < 5 ? ' style="opacity:0.55"' : '';
    html += '<tr' + rowOpacity + '>' +
      '<td class="lbl">' + escapeHtml(v.venue) + '</td>' +
      '<td class="num">' + v.agg.n + '</td>' +
      '<td class="num">' + (v.agg.wr * 100).toFixed(1) + '%</td>' +
      '<td class="num ' + (v.agg.roi > 0.05 ? 'pos' : v.agg.roi < -0.05 ? 'neg' : '') + '">' +
        (v.agg.roi >= 0 ? '+' : '') + (v.agg.roi * 100).toFixed(1) + '%</td>' +
      '<td class="num">' + (v.agg.avgSp != null ? '$' + v.agg.avgSp.toFixed(2) : '—') + '</td>' +
      '</tr>';
  });
  html += '</tbody></table>';
  if (Object.keys(byVenue).length > 15) {
    html += '<div class="tracking-note">Showing top 15 by pick count. ' +
      'Total venues: ' + Object.keys(byVenue).length + '. Faded rows have under 5 picks (small sample).</div>';
  } else {
    html += '<div class="tracking-note">Faded rows have under 5 picks - small sample, results are noisy.</div>';
  }
  el.innerHTML = html;
}

// ── Distance bracket breakdown ───────────────────────────────────────────
function renderDistanceBreakdown(races) {
  const el = document.getElementById('distance-breakdown');
  if (!el) return;
  const bets = trackingActiveBets(races);
  if (bets.length === 0) {
    el.innerHTML = '<div class="empty-text">' + trackingEmptyLabel() + ' in the selected period.</div>';
    return;
  }
  // Buckets: sprint, mile, middle, staying
  const buckets = [
    { lbl: 'Sprint (≤1100m)',    test: d => d != null && d <= 1100,                bets: [] },
    { lbl: 'Short (1200-1400m)', test: d => d != null && d >= 1200 && d <= 1400,   bets: [] },
    { lbl: 'Middle (1500-1800m)', test: d => d != null && d >= 1500 && d <= 1800,  bets: [] },
    { lbl: 'Long (1900-2200m)',  test: d => d != null && d >= 1900 && d <= 2200,   bets: [] },
    { lbl: 'Staying (≥2300m)',   test: d => d != null && d >= 2300,                bets: [] },
  ];
  bets.forEach(b => {
    for (const bk of buckets) {
      if (bk.test(b.distance)) { bk.bets.push(b); break; }
    }
  });
  let html = '<table class="tracking-mini-table"><thead><tr>' +
    '<th>Distance</th><th>' + trackingCountLabel() + '</th><th>WR%</th><th>ROI%</th><th>Avg SP</th>' +
    '</tr></thead><tbody>';
  buckets.forEach(bk => {
    html += statRow(bk.lbl, aggregateBets(bk.bets));
  });
  html += '</tbody></table>';
  el.innerHTML = html;
}

// ── Going (track condition) breakdown ────────────────────────────────────
function renderGoingBreakdown(races) {
  const el = document.getElementById('going-breakdown');
  if (!el) return;
  const bets = trackingActiveBets(races);
  if (bets.length === 0) {
    el.innerHTML = '<div class="empty-text">' + trackingEmptyLabel() + ' in the selected period.</div>';
    return;
  }
  // Group by going category. AU going strings are like "Good 4", "Soft 5",
  // "Heavy 8", "Firm 1". Strip the numeric suffix to group by category.
  function goingCat(g) {
    if (!g) return 'Unknown';
    const s = String(g).trim().toLowerCase();
    if (s.startsWith('firm')) return 'Firm';
    if (s.startsWith('good')) return 'Good';
    if (s.startsWith('soft')) return 'Soft';
    if (s.startsWith('heavy')) return 'Heavy';
    if (s.startsWith('synth') || s === 'awt') return 'Synthetic';
    return 'Other';
  }
  const categories = ['Firm', 'Good', 'Soft', 'Heavy', 'Synthetic', 'Other'];
  const byGoing = {};
  categories.forEach(c => byGoing[c] = []);
  bets.forEach(b => {
    const cat = goingCat(b.going);
    if (byGoing[cat]) byGoing[cat].push(b);
  });
  let html = '<table class="tracking-mini-table"><thead><tr>' +
    '<th>Going</th><th>' + trackingCountLabel() + '</th><th>WR%</th><th>ROI%</th><th>Avg SP</th>' +
    '</tr></thead><tbody>';
  categories.forEach(c => {
    if (byGoing[c].length === 0 && c !== 'Good') return;  // skip empty categories (except Good which is the default)
    html += statRow(c, aggregateBets(byGoing[c]));
  });
  html += '</tbody></table>';
  el.innerHTML = html;
}

// ── Field size breakdown ─────────────────────────────────────────────────
function renderFieldSizeBreakdown(races) {
  const el = document.getElementById('fieldsize-breakdown');
  if (!el) return;
  const bets = trackingActiveBets(races);
  if (bets.length === 0) {
    el.innerHTML = '<div class="empty-text">' + trackingEmptyLabel() + ' in the selected period.</div>';
    return;
  }
  const buckets = [
    { lbl: 'Small (≤7 runners)',  test: n => n != null && n <= 7,                bets: [] },
    { lbl: 'Medium (8-11)',       test: n => n != null && n >= 8 && n <= 11,     bets: [] },
    { lbl: 'Large (12-15)',       test: n => n != null && n >= 12 && n <= 15,    bets: [] },
    { lbl: 'Huge (≥16)',          test: n => n != null && n >= 16,               bets: [] },
  ];
  bets.forEach(b => {
    for (const bk of buckets) {
      if (bk.test(b.field_size)) { bk.bets.push(b); break; }
    }
  });
  let html = '<table class="tracking-mini-table"><thead><tr>' +
    '<th>Field</th><th>' + trackingCountLabel() + '</th><th>WR%</th><th>ROI%</th><th>Avg SP</th>' +
    '</tr></thead><tbody>';
  buckets.forEach(bk => {
    html += statRow(bk.lbl, aggregateBets(bk.bets));
  });
  html += '</tbody></table>';
  el.innerHTML = html;
}

// ── Section 4: Placegetters detail ───────────────────────────────────────
// 1st / 2nd / 3rd per race with all signal ranks. Useful for spotting where
// the model picked a runner that lost a photo finish to a similar-profile horse.
function renderTrackingPlacegetters(races) {
  const el = document.getElementById('tracking-placegetters');
  if (!el) return;
  if (races.length === 0) {
    el.innerHTML = '<div class="empty-text">No resulted races.</div>';
    return;
  }

  // Build rows: for each race, up to 3 rows (1st, 2nd, 3rd)
  const rows = [];
  races.sort((a, b) => (b.date || '').localeCompare(a.date || '')).forEach(race => {
    const runners = race.runners || [];
    [1, 2, 3].forEach(pos => {
      const runner = runners.find(u => u.f === pos);
      if (!runner) return;
      const ranks = {};
      TRACKING_SIGNALS.forEach(sig => {
        ranks[sig.key] = rankInRace(runners, runner.rid, sig);
      });
      rows.push({
        race_id: race.race_id,
        date: race.date || '',
        venue: race.venue || '',
        race: race.race || 0,
        pos: pos,
        horse: runner.h || '',
        sp: runner.sp,
        ranks: ranks,
        // First-place row marks a meeting boundary (we'll show divider)
        isFirstOfRace: pos === 1,
      });
    });
  });

  let html = '<div class="tracking-table-wrap"><table class="tracking-table tracking-places"><thead><tr>' +
    '<th>Date</th>' +
    '<th>Meeting</th>' +
    '<th>Race</th>' +
    '<th>Pos</th>' +
    '<th>Horse</th>' +
    '<th>SP</th>';
  TRACKING_SIGNALS.forEach(sig => { html += '<th>' + sig.label + '</th>'; });
  html += '</tr></thead><tbody>';

  rows.forEach(r => {
    const trClass = r.isFirstOfRace ? 'race-row' : '';
    const posClass = 'pos-' + r.pos;
    html += '<tr class="' + trClass + '">' +
      '<td>' + (r.isFirstOfRace ? escapeHtml(r.date) : '') + '</td>' +
      '<td>' + (r.isFirstOfRace ?
        '<a class="meeting-link" href="#" data-nav-rid="' + escapeHtml(String(r.race_id)) + '">' + escapeHtml(r.venue) + '</a>' : '') + '</td>' +
      '<td>' + (r.isFirstOfRace ? 'R' + r.race : '') + '</td>' +
      '<td><span class="' + posClass + '">' + r.pos + (r.pos === 1 ? 'st' : (r.pos === 2 ? 'nd' : 'rd')) + '</span></td>' +
      '<td class="horse-cell">' + escapeHtml(r.horse) + '</td>' +
      '<td class="price-cell">' + (r.sp != null ? '$' + r.sp.toFixed(2) : '—') + '</td>';
    TRACKING_SIGNALS.forEach(sig => { html += '<td>' + rankPill(r.ranks[sig.key]) + '</td>'; });
    html += '</tr>';
  });
  html += '</tbody></table></div>';
  el.innerHTML = html;

  // Wire meeting links
  el.querySelectorAll('a.meeting-link').forEach(a => {
    a.addEventListener('click', e => {
      e.preventDefault();
      const rid = a.dataset.navRid;
      if (typeof navigateToRace === 'function') navigateToRace(rid);
    });
  });
}

// Wire the period toggle buttons
document.querySelectorAll('.ic-period-btn').forEach(btn => {
  btn.addEventListener('click', () => {
    trackingPeriod = btn.dataset.iperiod;
    document.querySelectorAll('.ic-period-btn').forEach(b => b.classList.remove('active'));
    btn.classList.add('active');
    renderInsights();
  });
});

// Wire the mode toggle buttons (picks vs all theoretical). On click,
// flip trackingMode, persist to localStorage, re-render. Also sync the
// active class on initial load to reflect the persisted state.
document.querySelectorAll('.ic-mode-btn').forEach(btn => {
  btn.classList.toggle('active', btn.dataset.imode === trackingMode);
  btn.addEventListener('click', () => {
    trackingMode = btn.dataset.imode;
    try { localStorage.setItem(TRACKING_MODE_KEY, trackingMode); } catch(e) {}
    document.querySelectorAll('.ic-mode-btn').forEach(b => b.classList.remove('active'));
    btn.classList.add('active');
    _updateTrackingModelToggleVisibility();
    renderInsights();
  });
});

// Wire the model toggle buttons (main / loose / both). On click, flip
// trackingModel, persist, re-render. Active class synced on initial load.
document.querySelectorAll('.ic-model-btn').forEach(btn => {
  btn.classList.toggle('active', btn.dataset.imodel === trackingModel);
  btn.addEventListener('click', () => {
    trackingModel = btn.dataset.imodel;
    try { localStorage.setItem(TRACKING_MODEL_KEY, trackingModel); } catch(e) {}
    document.querySelectorAll('.ic-model-btn').forEach(b => b.classList.remove('active'));
    btn.classList.add('active');
    renderInsights();
  });
});

// Show/hide the model toggle based on mode. In 'all' mode, the model
// filter is meaningless since we're analysing every runner regardless
// of pick. Hide the toggle in that case so the UI doesn't suggest it
// has an effect.
function _updateTrackingModelToggleVisibility() {
  const tog = document.getElementById('ic-model-toggle');
  if (!tog) return;
  tog.classList.toggle('hidden', trackingMode === 'all');
}
_updateTrackingModelToggleVisibility();


// ── Database tab ────────────────────────────────────────────────────────────
// Flat queryable view over every runner in every resulted-or-not race in
// the last ~30 days (uses RACES as source - 90 days was the original ask
// but inlining 90 days would balloon the HTML to >25MB; 30 days from RACES
// is what we have in-context already). Filter bar at top, stats strip with
// computed metrics over visible rows including the user's preferred
// "bet to return 4u" hypothetical, sortable table at the bottom.
const DB_FILTERS_KEY = 'tr_database_filters_v1';

// Filter state (persisted)
let dbFilters = {
  dateFrom: '', dateTo: '',
  venue: '', horse: '',
  minFs: 0, minPrize: 0, going: '',
  minDist: null, maxDist: null,
  minScore: null, maxScore: null,
  minSp: null,
  minJky: 0,
  model: 'any',     // any | main | loose | any-pick | none
  result: 'any',    // any | won | placed | lost | resulted | unresulted
  // Per-signal rank filters - each value is 'any', '1', or '3'
  sigWpr: 'any', sigLate: 'any', sigWcR: 'any',
  sigL600R: 'any', sigPfaiR: 'any', sigTr: 'any',
};
try {
  const raw = localStorage.getItem(DB_FILTERS_KEY);
  if (raw) {
    const parsed = JSON.parse(raw);
    if (parsed && typeof parsed === 'object') dbFilters = Object.assign(dbFilters, parsed);
  }
} catch(e) {}
function saveDbFilters() {
  try { localStorage.setItem(DB_FILTERS_KEY, JSON.stringify(dbFilters)); } catch(e) {}
}

let dbSort = { col: 'date', dir: 'desc' };
let dbCollapsed = false;
try {
  const c = localStorage.getItem('tr_database_collapsed_v1');
  if (c === '1') dbCollapsed = true;
} catch(e) {}

// Build flat row list from RACES. Each row = one runner + race context.
// Heavy operation; only run once per tab open (or after dataset reload).
// Per-race ranks for wpr, late, tr are computed inline since some races
// don't have them pre-ranked on the runner object.
let _databaseRows = null;
function getDatabaseRows() {
  if (_databaseRows !== null) return _databaseRows;
  const rows = [];
  (RACES || []).forEach(race => {
    const runners = race.runners || [];
    // Compute per-race ranks for the three TR-side signals (the PF ranks
    // are already on the runner via u.wcR / u.l600R / u.pfaiR).
    function rankByField(field, ascending) {
      const ranks = {};
      const valid = runners.filter(u => u[field] != null);
      valid.sort((a, b) => ascending ? a[field] - b[field] : b[field] - a[field]);
      valid.forEach((u, i) => { ranks[u.rid] = i + 1; });
      return ranks;
    }
    const wprRanks  = rankByField('w', false);
    const lateRanks = rankByField('ls', false);
    const trRanks   = rankByField('trr', false);

    // Pick membership for this race
    const racePicks = MODEL_PICKS[race.race_id] || {};
    const mainPickIds  = new Set((racePicks[PRIMARY_KEY] || []).map(p => String(p.run_id)));
    const loosePickIds = new Set((racePicks['loose']     || []).map(p => String(p.run_id)));

    runners.forEach(u => {
      const ridStr = String(u.rid);
      rows.push({
        // Race context
        date: race.date,
        venue: race.venue,
        race: race.race,
        race_id: race.race_id,
        fs: race.fs || runners.length,
        prize: race.prize,
        going: race.going,
        distance: race.distance,
        // Runner identity
        rid: u.rid,
        tab: u.tab,
        horse: u.h,
        jockey: u.j,
        trainer: u.tn,
        barrier: u.b,
        // Signals + ranks
        score: u.cs,
        crk: u.crk,
        wpr: u.w,
        wprRank: wprRanks[ridStr],
        late: u.ls,
        lateRank: lateRanks[ridStr],
        wcR: u.wcR,
        l600R: u.l600R,
        pfaiR: u.pfaiR,
        tr: u.trr,
        trRank: trRanks[ridStr],
        jrt: u.jrt,
        trt: u.trt,
        runStyle: u.rs,
        // Price + result
        fxd: u.fx,
        sp: u.sp,
        finish: u.f,
        // Pick membership
        isMain:  mainPickIds.has(ridStr),
        isLoose: loosePickIds.has(ridStr),
      });
    });
  });
  _databaseRows = rows;
  return rows;
}

// Apply current filter state to the row list. Returns filtered array.
function filterDatabaseRows(rows) {
  return rows.filter(r => {
    if (dbFilters.dateFrom && (r.date || '') < dbFilters.dateFrom) return false;
    if (dbFilters.dateTo   && (r.date || '') > dbFilters.dateTo)   return false;
    if (dbFilters.venue) {
      const v = (r.venue || '').toLowerCase();
      if (!v.includes(dbFilters.venue.toLowerCase())) return false;
    }
    if (dbFilters.horse) {
      const h = (r.horse || '').toLowerCase();
      if (!h.includes(dbFilters.horse.toLowerCase())) return false;
    }
    if (dbFilters.minFs > 0 && (r.fs || 0) < dbFilters.minFs) return false;
    if (dbFilters.minPrize > 0 && (r.prize || 0) < dbFilters.minPrize) return false;
    if (dbFilters.going) {
      const g = (r.going || '').toLowerCase();
      if (!g.startsWith(dbFilters.going.toLowerCase())) return false;
    }
    if (dbFilters.minDist != null && (r.distance || 0) < dbFilters.minDist) return false;
    if (dbFilters.maxDist != null && (r.distance || 0) > dbFilters.maxDist) return false;
    if (dbFilters.minScore != null && (r.score == null || r.score < dbFilters.minScore)) return false;
    if (dbFilters.maxScore != null && (r.score == null || r.score > dbFilters.maxScore)) return false;
    // Min SP filter - SP only exists on resulted rows, so this filter
    // implicitly hides unresulted ones (no way to compare). That's the
    // intended behaviour: filtering by SP means you're looking at
    // completed races.
    if (dbFilters.minSp != null && (r.sp == null || r.sp < dbFilters.minSp)) return false;
    if (dbFilters.minJky > 0 && (r.jrt == null || r.jrt < dbFilters.minJky)) return false;
    // Model pick filter
    if (dbFilters.model === 'main'     && !r.isMain) return false;
    if (dbFilters.model === 'loose'    && !r.isLoose) return false;
    if (dbFilters.model === 'any-pick' && !(r.isMain || r.isLoose)) return false;
    if (dbFilters.model === 'none'     && (r.isMain || r.isLoose)) return false;
    // Result filter
    const resulted = r.finish != null;
    const won = r.finish === 1;
    const placed = r.finish != null && r.finish <= 3;
    if (dbFilters.result === 'won'         && !won) return false;
    if (dbFilters.result === 'placed'      && !placed) return false;
    if (dbFilters.result === 'lost'        && (!resulted || placed)) return false;
    if (dbFilters.result === 'resulted'    && !resulted) return false;
    if (dbFilters.result === 'unresulted' && resulted) return false;
    // Signal rank filters - each "n" means rank must be <= n
    function sigPass(filterVal, rank) {
      if (filterVal === 'any') return true;
      const n = parseInt(filterVal, 10);
      if (isNaN(n)) return true;
      return rank != null && rank <= n;
    }
    if (!sigPass(dbFilters.sigWpr,    r.wprRank))  return false;
    if (!sigPass(dbFilters.sigLate,   r.lateRank)) return false;
    if (!sigPass(dbFilters.sigWcR,    r.wcR))      return false;
    if (!sigPass(dbFilters.sigL600R,  r.l600R))    return false;
    if (!sigPass(dbFilters.sigPfaiR,  r.pfaiR))    return false;
    if (!sigPass(dbFilters.sigTr,     r.trRank))   return false;
    return true;
  });
}

// Sort rows by the active sort column/direction.
function sortDatabaseRows(rows) {
  const col = dbSort.col;
  const dirMul = dbSort.dir === 'asc' ? 1 : -1;
  // Default getters for each sortable column. Null sorts to end.
  const getters = {
    date:    r => r.date || '',
    venue:   r => r.venue || '',
    race:    r => r.race || 0,
    horse:   r => r.horse || '',
    tab:     r => r.tab || 99,
    fxd:     r => r.fxd != null ? r.fxd : 9999,
    sp:      r => r.sp != null ? r.sp : 9999,
    score:   r => r.score != null ? r.score : -1,
    crk:     r => r.crk != null ? r.crk : 99,
    wpr:     r => r.wpr != null ? r.wpr : -9999,
    late:    r => r.late != null ? r.late : -9999,
    wcR:     r => r.wcR != null ? r.wcR : 99,
    l600R:   r => r.l600R != null ? r.l600R : 99,
    pfaiR:   r => r.pfaiR != null ? r.pfaiR : 99,
    tr:      r => r.tr != null ? r.tr : -9999,
    fs:      r => r.fs || 0,
    prize:   r => r.prize || 0,
    distance: r => r.distance || 0,
    jky:     r => r.jrt != null ? r.jrt : -1,
    finish:  r => r.finish != null ? r.finish : 99,
    barrier: r => r.barrier != null ? r.barrier : 99,
  };
  const getter = getters[col] || getters.date;
  return rows.slice().sort((a, b) => {
    const av = getter(a), bv = getter(b);
    let cmp;
    if (typeof av === 'string') cmp = av.localeCompare(bv);
    else cmp = av - bv;
    return cmp * dirMul;
  });
}

// Compute stats over visible (already-filtered) rows. Includes the
// hypothetical "bet to return 4u" calculation requested by the user:
//   For each resulted row, stake = TARGET / (price - 1). On win, return
//   = TARGET = 4. On loss, return = 0. ROI = (total_return - total_stake)
//   / total_stake. Uses SP as the price (falls back to Fxd if SP missing).
// Skipped: rows without a usable price, rows that haven't resulted.
function computeDatabaseStats(rows) {
  const TARGET = 4;
  let total = rows.length;
  let resulted = 0, wins = 0, places = 0;
  let bettable = 0, stakeSum = 0, returnSum = 0;
  rows.forEach(r => {
    if (r.finish == null) return;
    resulted++;
    if (r.finish === 1) wins++;
    if (r.finish != null && r.finish <= 3) places++;
    const price = r.sp != null ? r.sp : r.fxd;
    if (price == null || price <= 1) return;
    bettable++;
    const stake = TARGET / (price - 1);
    stakeSum += stake;
    if (r.finish === 1) returnSum += TARGET;
  });
  const wr        = resulted > 0 ? wins / resulted : null;
  const placeRate = resulted > 0 ? places / resulted : null;
  const profit    = returnSum - stakeSum;
  const roi       = stakeSum > 0 ? profit / stakeSum : null;
  return {
    total, resulted, wins, places, bettable,
    wr, placeRate,
    stakeSum, returnSum, profit, roi,
  };
}

// Render the stats strip
function renderDatabaseStats(stats) {
  const el = document.getElementById('db-stats-strip');
  if (!el) return;
  function fmt(n, dp) { return n == null ? '—' : Number(n).toFixed(dp == null ? 2 : dp); }
  function pct(n) { return n == null ? '—' : (n * 100).toFixed(1) + '%'; }
  function dollar(n) { return n == null ? '—' : '$' + Number(n).toFixed(2); }
  const roiClass = stats.roi != null ? (stats.roi > 0.01 ? 'pos' : stats.roi < -0.01 ? 'neg' : '') : '';
  el.innerHTML =
    '<div class="db-stat">' +
      '<div class="lbl">Visible rows</div>' +
      '<div class="val">' + stats.total + '</div>' +
      '<div class="sub">' + stats.resulted + ' resulted · ' + (stats.total - stats.resulted) + ' pending</div>' +
    '</div>' +
    '<div class="db-stat">' +
      '<div class="lbl">Win rate</div>' +
      '<div class="val">' + pct(stats.wr) + '</div>' +
      '<div class="sub">' + stats.wins + ' of ' + stats.resulted + '</div>' +
    '</div>' +
    '<div class="db-stat">' +
      '<div class="lbl">Place rate</div>' +
      '<div class="val">' + pct(stats.placeRate) + '</div>' +
      '<div class="sub">' + stats.places + ' of ' + stats.resulted + '</div>' +
    '</div>' +
    '<div class="db-stat" title="Hypothetical stake sized to return 4u on each winning bet. Stake = 4 / (price - 1). Total stake summed across all bettable rows.">' +
      '<div class="lbl">Total stake (4u target)</div>' +
      '<div class="val">' + fmt(stats.stakeSum) + 'u</div>' +
      '<div class="sub">' + stats.bettable + ' bettable rows</div>' +
    '</div>' +
    '<div class="db-stat" title="Total returned if you had bet every resulted row at 4u-target stake. Each winner returns 4u.">' +
      '<div class="lbl">Total return</div>' +
      '<div class="val">' + fmt(stats.returnSum) + 'u</div>' +
      '<div class="sub">' + stats.wins + ' wins × 4u</div>' +
    '</div>' +
    '<div class="db-stat" title="(Return - Stake) / Stake at the 4u-target staking strategy.">' +
      '<div class="lbl">ROI</div>' +
      '<div class="val ' + roiClass + '">' + (stats.roi != null ? (stats.roi >= 0 ? '+' : '') + (stats.roi * 100).toFixed(1) + '%' : '—') + '</div>' +
      '<div class="sub">' + (stats.profit >= 0 ? '+' : '') + fmt(stats.profit) + 'u net</div>' +
    '</div>';
}

// Render the table
function renderDatabaseTable(rows) {
  const wrap = document.getElementById('db-table-wrap');
  if (!wrap) return;
  if (rows.length === 0) {
    wrap.innerHTML = '<div class="db-table-empty">No runners match current filters. Try Reset.</div>';
    return;
  }
  // Limit display rows. Show all if under 2000; warn and slice if more.
  const HARD_CAP = 2000;
  const truncated = rows.length > HARD_CAP;
  const display = truncated ? rows.slice(0, HARD_CAP) : rows;
  function th(col, label) {
    let cls = '';
    if (dbSort.col === col) cls = 'sort-' + dbSort.dir;
    return '<th class="' + cls + '" data-sort="' + col + '">' + label + '</th>';
  }
  function rankCls(r) {
    if (r == null) return '';
    if (r === 1) return 'rk-1';
    if (r === 2) return 'rk-2';
    if (r === 3) return 'rk-3';
    return '';
  }
  function cell(v, extra) {
    if (v == null) return '<td' + (extra || '') + '>—</td>';
    return '<td' + (extra || '') + '>' + v + '</td>';
  }
  function rankCell(rank) {
    if (rank == null) return '<td class="num">—</td>';
    return '<td class="num ' + rankCls(rank) + '">' + rank + '</td>';
  }
  let html = '<table class="db-table"><thead><tr>' +
    th('date', 'Date') + th('venue', 'Venue') + th('race', 'R#') +
    th('tab', 'Tab') + th('horse', 'Horse') +
    th('fs', 'Field') + th('prize', '$') + th('distance', 'Dist') +
    th('barrier', 'Bar') + th('fxd', 'Fxd') + th('sp', 'SP') +
    th('score', 'Score') + th('crk', 'Score#') +
    th('wpr', 'WPR') + th('late', 'Late') +
    th('wcR', 'Cls') + th('l600R', 'L600') + th('pfaiR', 'PFAI') +
    th('tr', 'TR') + th('jky', 'Jky rt') +
    th('finish', 'Fin') +
    '</tr></thead><tbody>';
  display.forEach(r => {
    let cls = '';
    if (r.isMain && r.isLoose) cls = 'is-pick';
    else if (r.isMain) cls = 'is-pick';
    else if (r.isLoose) cls = 'is-loose-pick';
    // Horse cell with pick pills
    let horseHtml = '<span class="horse-link" data-rid="' + r.race_id + '">' +
      escapeHtml(r.horse || '') + '</span>';
    if (r.isMain)  horseHtml += '<span class="db-pick-pill main">M</span>';
    if (r.isLoose) horseHtml += '<span class="db-pick-pill loose">L</span>';
    // Finish badge
    let finishHtml;
    if (r.finish == null) finishHtml = '<td class="num">—</td>';
    else {
      const f = r.finish;
      const fcls = f === 1 ? 'f1' : f === 2 ? 'f2' : f === 3 ? 'f3' : 'fo';
      finishHtml = '<td class="num"><span class="db-finish ' + fcls + '">' + f + '</span></td>';
    }
    html += '<tr class="' + cls + '">' +
      cell(r.date) +
      cell(escapeHtml(r.venue || '')) +
      cell('R' + (r.race || '—')) +
      cell(r.tab != null ? r.tab : '?', ' class="num"') +
      '<td>' + horseHtml + '</td>' +
      cell(r.fs, ' class="num"') +
      cell(r.prize != null ? '$' + (r.prize/1000).toFixed(0) + 'k' : null, ' class="num"') +
      cell(r.distance != null ? r.distance + 'm' : null, ' class="num"') +
      cell(r.barrier != null ? r.barrier : null, ' class="num"') +
      cell(r.fxd != null ? '$' + r.fxd.toFixed(2) : null, ' class="num"') +
      cell(r.sp != null ? '$' + r.sp.toFixed(2) : null, ' class="num"') +
      cell(r.score != null ? r.score.toFixed(2) : null, ' class="num"') +
      rankCell(r.crk) +
      rankCell(r.wprRank) +
      rankCell(r.lateRank) +
      rankCell(r.wcR) +
      rankCell(r.l600R) +
      rankCell(r.pfaiR) +
      rankCell(r.trRank) +
      cell(r.jrt != null ? Math.round(r.jrt) : null, ' class="num"') +
      finishHtml +
      '</tr>';
  });
  html += '</tbody></table>';
  if (truncated) {
    html = '<div class="db-table-empty" style="padding:12px;">Showing first ' + HARD_CAP +
      ' of ' + rows.length + ' rows. Tighten filters to see more.</div>' + html;
  }
  wrap.innerHTML = html;

  // Wire header sort
  wrap.querySelectorAll('th[data-sort]').forEach(h => {
    h.addEventListener('click', () => {
      const col = h.dataset.sort;
      if (dbSort.col === col) dbSort.dir = dbSort.dir === 'asc' ? 'desc' : 'asc';
      else { dbSort.col = col; dbSort.dir = (col === 'score' || col === 'wpr' || col === 'late' || col === 'tr' || col === 'fxd' || col === 'sp' || col === 'jky' || col === 'prize') ? 'desc' : 'asc'; }
      renderDatabase();
    });
  });
  // Wire horse-link clicks to navigate to race detail
  wrap.querySelectorAll('.horse-link[data-rid]').forEach(a => {
    a.addEventListener('click', e => {
      e.preventDefault();
      const rid = a.dataset.rid;
      if (typeof navigateToRace === 'function') navigateToRace(rid);
    });
  });
}

// Top-level render: filter + sort + render stats + render table
function renderDatabase() {
  const all = getDatabaseRows();
  const filtered = filterDatabaseRows(all);
  const sorted = sortDatabaseRows(filtered);
  const stats = computeDatabaseStats(filtered);
  renderDatabaseStats(stats);
  renderDatabaseTable(sorted);
  // Filter summary
  const summary = document.getElementById('db-filter-summary');
  if (summary) {
    summary.textContent = filtered.length + ' of ' + all.length + ' runners shown';
  }
}

// Wire all filter inputs. Each change saves state, re-renders.
function _wireDatabaseFilters() {
  function bind(id, key, parseFn) {
    const el = document.getElementById(id);
    if (!el) return;
    // Restore from state
    if (dbFilters[key] != null && dbFilters[key] !== '' && dbFilters[key] !== 0) {
      el.value = dbFilters[key];
    }
    el.addEventListener('input', () => {
      const raw = el.value;
      dbFilters[key] = parseFn ? parseFn(raw) : raw;
      saveDbFilters();
      renderDatabase();
    });
    el.addEventListener('change', () => {
      const raw = el.value;
      dbFilters[key] = parseFn ? parseFn(raw) : raw;
      saveDbFilters();
      renderDatabase();
    });
  }
  const toInt   = v => v === '' ? 0 : parseInt(v, 10);
  const toIntOrNull = v => v === '' ? null : parseInt(v, 10);
  const toFloatOrNull = v => v === '' ? null : parseFloat(v);
  bind('db-date-from', 'dateFrom');
  bind('db-date-to',   'dateTo');
  bind('db-venue',     'venue');
  bind('db-horse',     'horse');
  bind('db-min-fs',    'minFs',    toInt);
  bind('db-min-prize', 'minPrize', toInt);
  bind('db-going',     'going');
  bind('db-min-dist',  'minDist',  toIntOrNull);
  bind('db-max-dist',  'maxDist',  toIntOrNull);
  bind('db-min-score', 'minScore', toFloatOrNull);
  bind('db-max-score', 'maxScore', toFloatOrNull);
  bind('db-min-sp',    'minSp',    toFloatOrNull);
  bind('db-min-jky',   'minJky',   toInt);
  bind('db-model',     'model');
  bind('db-result',    'result');
  // Signal filters - wire each select, key derived from data-sigfilter
  document.querySelectorAll('[data-sigfilter]').forEach(sel => {
    const sigKey = sel.dataset.sigfilter;
    const stateKey = 'sig' + sigKey.charAt(0).toUpperCase() + sigKey.slice(1);
    if (dbFilters[stateKey] && dbFilters[stateKey] !== 'any') sel.value = dbFilters[stateKey];
    sel.addEventListener('change', () => {
      dbFilters[stateKey] = sel.value;
      saveDbFilters();
      renderDatabase();
    });
  });
  // Quick filters: All #1 and All top-3
  const allRank1 = document.getElementById('db-all-rank-1');
  if (allRank1) {
    allRank1.addEventListener('click', () => {
      ['sigWpr','sigLate','sigWcR','sigL600R','sigPfaiR','sigTr'].forEach(k => dbFilters[k] = '1');
      saveDbFilters();
      // Update UI
      document.querySelectorAll('[data-sigfilter]').forEach(s => s.value = '1');
      renderDatabase();
    });
  }
  const allTop3 = document.getElementById('db-all-top3');
  if (allTop3) {
    allTop3.addEventListener('click', () => {
      ['sigWpr','sigLate','sigWcR','sigL600R','sigPfaiR','sigTr'].forEach(k => dbFilters[k] = '3');
      saveDbFilters();
      document.querySelectorAll('[data-sigfilter]').forEach(s => s.value = '3');
      renderDatabase();
    });
  }
  // Reset
  const reset = document.getElementById('db-reset');
  if (reset) {
    reset.addEventListener('click', () => {
      dbFilters = {
        dateFrom: '', dateTo: '', venue: '', horse: '',
        minFs: 0, minPrize: 0, going: '',
        minDist: null, maxDist: null,
        minScore: null, maxScore: null,
        minSp: null,
        minJky: 0, model: 'any', result: 'any',
        sigWpr: 'any', sigLate: 'any', sigWcR: 'any',
        sigL600R: 'any', sigPfaiR: 'any', sigTr: 'any',
      };
      saveDbFilters();
      // Clear all input UI
      ['db-date-from','db-date-to','db-venue','db-horse','db-min-dist','db-max-dist','db-min-score','db-max-score','db-min-sp']
        .forEach(id => { const el = document.getElementById(id); if (el) el.value = ''; });
      ['db-min-fs','db-min-prize','db-going','db-min-jky','db-model','db-result']
        .forEach(id => { const el = document.getElementById(id); if (el) el.value = (id === 'db-going') ? '' : (id === 'db-model' || id === 'db-result') ? 'any' : '0'; });
      document.querySelectorAll('[data-sigfilter]').forEach(s => s.value = 'any');
      renderDatabase();
    });
  }
  // Collapse toggle
  const toggle = document.getElementById('db-controls-toggle');
  if (toggle) {
    const controls = toggle.closest('.db-controls');
    if (dbCollapsed) controls.classList.add('collapsed');
    toggle.addEventListener('click', () => {
      const collapsed = controls.classList.toggle('collapsed');
      dbCollapsed = collapsed;
      try { localStorage.setItem('tr_database_collapsed_v1', collapsed ? '1' : '0'); } catch(e) {}
    });
  }
}
_wireDatabaseFilters();
renderDatabase();


// ── Quaddie tab ─────────────────────────────────────────────────────────────
// State persisted in localStorage so user doesn't lose their selections on refresh
const QUADDIE_STORAGE_KEY = 'tr_quaddie_state_v1';
let quaddieState = {
  date: null,            // YYYY-MM-DD currently being browsed
  meetingKey: null,      // venue|date key
  legRaceIds: [],        // up to 4 race_ids selected
  threshOverride: null,  // null = use settings.scoreThreshold
};
try {
  const raw = localStorage.getItem(QUADDIE_STORAGE_KEY);
  if (raw) quaddieState = Object.assign(quaddieState, JSON.parse(raw));
} catch(e) {}
function saveQuaddieState() {
  try { localStorage.setItem(QUADDIE_STORAGE_KEY, JSON.stringify(quaddieState)); } catch(e) {}
}

// Per-leg winner coverage curves from backtest (1,608 races). Indexed by N picks.
// E.g. if a leg has 3 qualifying horses, those 3 are by definition the top 3 by score,
// so coverage = QUADDIE_COVERAGE_CURVE_B[3] = 0.687 (winner appears in our 3 picks 68.7% of races).
//
// Two curves because the score formula has two paths:
//   Path B (default when jt_combo missing): TR + wpr3 + late_speed proxy. 33% rk-1 WR.
//   Path A (jt_combo with Bayesian shrinkage): jt_combo_shrunk + tr. 40% rk-1 WR.
// Each race has a 'cs_path' field telling us which formula was used. We pick
// the matching curve so the projected hit rates are accurate.
//
// IMPORTANT: Path A numbers use Bayesian-shrunk jt_combo_win_pct. The naive
// version (no shrinkage) shows inflated 44% rk-1 WR but that's largely small-
// sample noise (5-ride pairs with 60% strike rates). Shrinkage pulls noisy
// pairs toward the population mean of 9% so only well-sampled pairs influence.
const QUADDIE_COVERAGE_CURVE_B = {
  // Proxy formula numbers (TR + wpr3 + late)
  0: 0.0,   1: 0.326, 2: 0.540, 3: 0.687, 4: 0.783,
  5: 0.860, 6: 0.912, 7: 0.953, 8: 0.973, 9: 0.985,
  10: 0.992, 11: 0.996, 12: 1.0,
};
const QUADDIE_COVERAGE_CURVE_A = {
  // jt_combo (shrunk) + tr formula numbers - the honest, non-inflated version
  0: 0.0,   1: 0.399, 2: 0.628, 3: 0.778, 4: 0.866,
  5: 0.922, 6: 0.947, 7: 0.969, 8: 0.981, 9: 0.990,
  10: 0.995, 11: 0.997, 12: 0.998,
};
function legCoverage(nPicks, path) {
  if (nPicks == null || nPicks <= 0) return 0;
  const curve = (path === 'A') ? QUADDIE_COVERAGE_CURVE_A : QUADDIE_COVERAGE_CURVE_B;
  if (curve[nPicks] != null) return curve[nPicks];
  return 1.0;  // 12+ picks ≈ whole field
}

function getQuaddieThreshold() {
  if (quaddieState.threshOverride != null) return quaddieState.threshOverride;
  return (settings && settings.scoreThreshold != null) ? settings.scoreThreshold : 0.55;
}

function quaddieRacesForDate(dateStr) {
  // Exclude races/meetings the user has marked abandoned. Quaddies can't be
  // formed across abandoned races so filtering here is the cleanest spot -
  // the meetings grid, legs picker, qualifier counts all flow from this.
  return RACES.filter(r => r.date === dateStr && !isRaceAbandoned(r));
}

function quaddieMeetingsForDate(dateStr) {
  // Group races by venue, return [{venue, state, races: [...sorted by start_time]}]
  const races = quaddieRacesForDate(dateStr);
  const groups = {};
  races.forEach(r => {
    const key = r.venue + '|' + (r.state || '');
    if (!groups[key]) groups[key] = { venue: r.venue, state: r.state || '', races: [] };
    groups[key].races.push(r);
  });
  Object.values(groups).forEach(g => {
    g.races.sort((a, b) => (a.start_time || '').localeCompare(b.start_time || '') || (a.race - b.race));
  });
  return Object.values(groups).sort((a, b) => a.venue.localeCompare(b.venue));
}

function renderQuaddieMeetingsGrid(meetings) {
  const host = document.getElementById('quaddie-meetings-list');
  if (!host) return;
  if (meetings.length === 0) {
    host.innerHTML = '<div class="empty-state">' +
      '<div class="head">No meetings for ' + quaddieState.date + '</div>' +
      '<div class="sub">Try Yesterday or Tomorrow, or pick another date.</div>' +
      '</div>';
    return;
  }
  // Strategy filter constants - same as the per-meeting renderer below.
  const QUADDIE_MIN_PRIZE = 50000;
  const QUADDIE_MIN_FIELD = 8;
  function raceStratPass(r) {
    const prize = r.prize || 0;
    const fs = r.fs || (r.runners || []).length || 0;
    return prize >= QUADDIE_MIN_PRIZE && fs >= QUADDIE_MIN_FIELD;
  }

  const thresh = getQuaddieThreshold();
  const legSet = new Set(quaddieState.legRaceIds);
  // Find the max race number to align all venues against the same column grid
  const maxR = Math.max(...meetings.map(m =>
    Math.max(...m.races.map(r => r.race || 0))));

  let html = '<div class="quaddie-meetings-table">';
  // Header row
  html += '<div class="qmt-row qmt-head">';
  html += '<div class="qmt-venue-col">Venue</div>';
  for (let i = 1; i <= maxR; i++) {
    html += '<div class="qmt-race-head">R' + i + '</div>';
  }
  html += '</div>';

  // Sort meetings: passing-strategy meetings first (most useful), then by name
  const meetingsAnnotated = meetings.map(m => {
    const passingCount = m.races.filter(raceStratPass).length;
    return { m, passingCount };
  });
  meetingsAnnotated.sort((a, b) => {
    if (a.passingCount !== b.passingCount) return b.passingCount - a.passingCount;
    return a.m.venue.localeCompare(b.m.venue);
  });

  meetingsAnnotated.forEach(({ m, passingCount }) => {
    const meetingKey = m.venue + '|' + m.state;
    const isActive = meetingKey === quaddieState.meetingKey;
    const rowCls = ['qmt-row', 'qmt-venue-row'];
    if (isActive) rowCls.push('active');
    if (passingCount === 0) rowCls.push('no-strat-races');
    html += '<div class="' + rowCls.join(' ') + '" data-meeting-key="' + escapeHtml(meetingKey) + '">';
    // Venue cell with strategy summary inline (X of Y races meet criteria)
    const stratSummaryCls = passingCount === 0 ? 'qmt-strat-none' :
                            passingCount >= 4 ? 'qmt-strat-good' : 'qmt-strat-some';
    html += '<div class="qmt-venue-col">' +
      '<div class="qmt-venue-name">' + escapeHtml(m.venue) + '</div>' +
      (m.state ? '<div class="qmt-venue-state">' + escapeHtml(m.state) + '</div>' : '') +
      '<div class="qmt-strat-summary ' + stratSummaryCls + '" title="Races at this meeting meeting your bet criteria (prize $50k+ AND 8+ runners)">' +
      passingCount + '/' + m.races.length + ' ✓' +
      '</div>' +
      '</div>';

    for (let i = 1; i <= maxR; i++) {
      const race = m.races.find(r => r.race === i);
      if (!race) {
        html += '<div class="qmt-race-cell qmt-empty">—</div>';
        continue;
      }
      const stratPass = raceStratPass(race);
      const quals = race.runners.filter(u => u.cs != null && u.cs >= thresh).length;
      const isSelected = legSet.has(race.race_id) && isActive;
      const legPos = isSelected ? (quaddieState.legRaceIds.indexOf(race.race_id) + 1) : null;
      const cellCls = ['qmt-race-cell'];
      if (stratPass) cellCls.push('strat-pass');
      else cellCls.push('strat-fail');
      if (isSelected) cellCls.push('selected');
      if (race.done === 1) cellCls.push('resulted');
      // Cell click target: data attrs for both meeting select + race toggle
      html += '<div class="' + cellCls.join(' ') + '" ' +
        'data-meeting-key="' + escapeHtml(meetingKey) + '" ' +
        'data-rid="' + race.race_id + '" ' +
        'title="' + (stratPass ? '✓' : '✗') + ' R' + race.race +
        ' · prize $' + ((race.prize || 0) / 1000).toFixed(0) + 'k' +
        ' · field ' + (race.fs || (race.runners || []).length || 0) + '">' +
        (legPos ? '<span class="qmt-leg-tag">' + legPos + '</span>' : '') +
        '<div class="qmt-quals">' + quals + '</div>' +
        '<div class="qmt-strat-icon">' + (stratPass ? '✓' : '✗') + '</div>' +
        '</div>';
    }
    html += '</div>';
  });
  html += '</div>';

  // Help line under the grid - explains the cell layout
  html += '<div class="qmt-key">' +
    '<span><span class="qmt-key-tick">✓</span> meets bet strategy (prize $50k+, field 8+)</span>' +
    '<span><span class="qmt-key-num">3</span> = horses meeting score threshold</span>' +
    '<span><span class="qmt-key-leg">1</span> = selected as leg 1 of your quaddie</span>' +
    '</div>';

  host.innerHTML = html;

  // Wire venue-row clicks - select meeting (but don't toggle a race)
  host.querySelectorAll('.qmt-venue-row .qmt-venue-col').forEach(cell => {
    cell.addEventListener('click', (ev) => {
      ev.stopPropagation();
      const row = ev.currentTarget.closest('.qmt-venue-row');
      const key = row.dataset.meetingKey;
      if (quaddieState.meetingKey !== key) {
        quaddieState.meetingKey = key;
        quaddieState.legRaceIds = [];  // reset legs when switching meetings
        saveQuaddieState();
        renderQuaddie();
      }
    });
  });

  // Wire race-cell clicks - select meeting if not already, then toggle leg
  host.querySelectorAll('.qmt-race-cell[data-rid]').forEach(cell => {
    cell.addEventListener('click', (ev) => {
      ev.stopPropagation();
      const key = cell.dataset.meetingKey;
      const rid = cell.dataset.rid;
      // If clicking a race at a different meeting, switch meetings first
      if (quaddieState.meetingKey !== key) {
        quaddieState.meetingKey = key;
        quaddieState.legRaceIds = [rid];  // start fresh with this race as leg 1
      } else {
        // Same meeting - toggle leg membership
        const idx = quaddieState.legRaceIds.indexOf(rid);
        if (idx >= 0) {
          quaddieState.legRaceIds.splice(idx, 1);
        } else {
          if (quaddieState.legRaceIds.length >= 4) {
            quaddieState.legRaceIds.shift();
          }
          quaddieState.legRaceIds.push(rid);
        }
      }
      saveQuaddieState();
      renderQuaddie();
    });
  });
}

function renderQuaddie() {
  // Initialise date if missing
  if (!quaddieState.date) quaddieState.date = isoDate(0);
  const dateInp = document.getElementById('quaddie-date-input');
  if (dateInp && !dateInp.value) dateInp.value = quaddieState.date;
  // Update active state on date quick buttons
  document.querySelectorAll('.quaddie-date-quick').forEach(btn => btn.classList.remove('active'));
  const todayIso = isoDate(0), yIso = isoDate(-1), tIso = isoDate(1);
  if (quaddieState.date === todayIso)      document.querySelector('.quaddie-date-quick[data-qdate="today"]')?.classList.add('active');
  else if (quaddieState.date === yIso)     document.querySelector('.quaddie-date-quick[data-qdate="yesterday"]')?.classList.add('active');
  else if (quaddieState.date === tIso)     document.querySelector('.quaddie-date-quick[data-qdate="tomorrow"]')?.classList.add('active');

  // Threshold input
  const threshInp = document.getElementById('quaddie-thresh');
  if (threshInp && document.activeElement !== threshInp) {
    threshInp.value = getQuaddieThreshold().toFixed(2);
  }

  const meetings = quaddieMeetingsForDate(quaddieState.date);
  const currentMeetingKey = quaddieState.meetingKey;

  // Render meetings grid (rows = venues, columns = race numbers across)
  // matching the Race tab's meetings-table layout. Each race cell shows
  // qualifier count + strategy ✓/✗ + leg position if selected. Clicking
  // a venue row selects it as the active meeting; clicking a race cell
  // toggles that race in/out of the legs. This replaces the old dropdown
  // which required a 2-step "pick meeting > then click races" flow.
  renderQuaddieMeetingsGrid(meetings);

  // Determine what to render based on current meeting
  const grid = document.getElementById('quaddie-race-grid');
  const legsWrap = document.getElementById('quaddie-legs-wrap');
  const empty = document.getElementById('quaddie-empty');

  // Validate meetingKey still exists for this date
  let activeMeeting = meetings.find(m => (m.venue + '|' + m.state) === currentMeetingKey);
  if (!activeMeeting) {
    // Reset
    quaddieState.meetingKey = null;
    quaddieState.legRaceIds = [];
    grid.innerHTML = '';
    legsWrap.style.display = 'none';
    const stratBannerHide = document.getElementById('quaddie-strategy-banner');
    if (stratBannerHide) stratBannerHide.style.display = 'none';
    empty.style.display = 'block';
    empty.textContent = meetings.length === 0
      ? 'No races available for ' + quaddieState.date + '. Pick another date.'
      : 'Pick a meeting above to get started. Then click race cards to add them as legs.';
    saveQuaddieState();
    return;
  }

  empty.style.display = 'none';

  // Validate legRaceIds belong to current meeting
  const meetingRaceIds = new Set(activeMeeting.races.map(r => r.race_id));
  quaddieState.legRaceIds = quaddieState.legRaceIds.filter(rid => meetingRaceIds.has(rid));

  // Strategy filter constants - user's manual play criteria. Quaddie strategy
  // backtest showed clear edge ONLY on meetings where all 4 legs have prize
  // money >= $50k AND field size >= 8. Below either threshold the strategy
  // is unprofitable, so flag races that fail either filter to make manual
  // selection effortless.
  const QUADDIE_MIN_PRIZE = 50000;
  const QUADDIE_MIN_FIELD = 8;
  function raceStratPass(r) {
    const prize = (r.prize || 0);
    const fs = (r.fs || (r.runners || []).length || 0);
    return prize >= QUADDIE_MIN_PRIZE && fs >= QUADDIE_MIN_FIELD;
  }

  // Render race grid
  const thresh = getQuaddieThreshold();
  const legSet = new Set(quaddieState.legRaceIds);
  grid.innerHTML = activeMeeting.races.map(r => {
    const quals = r.runners.filter(u => u.cs != null && u.cs >= thresh).length;
    const isSelected = legSet.has(r.race_id);
    const legPos = isSelected ? (quaddieState.legRaceIds.indexOf(r.race_id) + 1) : null;
    const time = fmtTime(r.start_time) || '—';
    const fsTag = r.hfs ? '<span class="qr-firststarter" title="First-starter race: at least one horse has no past WPR data. The model rule excludes these races since signals don\'t apply to debut runners. You can still use this leg manually but model picks won\'t fire.">⚠</span>' : '';
    const legTag = legPos ? '<span class="qr-leg-tag">Leg ' + legPos + '</span>' : '';
    const qualsCls = quals === 0 ? ' zero' : '';
    // Strategy flag - small tick or cross indicating whether THIS race meets
    // the user's bet criteria (prize >= $50k AND field >= 8 runners).
    // Tooltip explains why a race fails. Cards are still clickable either
    // way - this is a guide, not a hard restriction.
    const stratPass = raceStratPass(r);
    const stratPrize = (r.prize || 0);
    const stratFs = (r.fs || (r.runners || []).length || 0);
    const stratReasons = [];
    if (stratPrize < QUADDIE_MIN_PRIZE) {
      stratReasons.push('prize $' + (stratPrize / 1000).toFixed(0) + 'k < $50k');
    }
    if (stratFs < QUADDIE_MIN_FIELD) {
      stratReasons.push('field ' + stratFs + ' < 8 runners');
    }
    const stratTip = stratPass
      ? 'Meets strategy: prize $' + (stratPrize / 1000).toFixed(0) + 'k, ' + stratFs + ' runners'
      : 'Below strategy: ' + stratReasons.join(', ');
    const stratTag = '<span class="qr-strat ' + (stratPass ? 'pass' : 'fail') +
      '" title="' + stratTip + '">' + (stratPass ? '✓' : '✗') + '</span>';
    return '<div class="quaddie-race-card' + (isSelected ? ' selected' : '') +
      (stratPass ? '' : ' strat-fail') + '" data-rid="' + r.race_id + '">' +
      legTag +
      stratTag +
      '<div class="qr-num">R' + r.race + '</div>' +
      '<div class="qr-time">' + time + '</div>' +
      '<div class="qr-quals' + qualsCls + '">' + quals + ' above ' + thresh.toFixed(2) + '</div>' +
      fsTag +
      '</div>';
  }).join('');

  // Strategy banner above grid - tells user at a glance how many races at
  // this meeting meet their bet criteria. If selected legs are already
  // picked, also reports whether the chosen quaddie passes (all 4 legs
  // meeting strategy). Hidden when no meeting active.
  const stratBanner = document.getElementById('quaddie-strategy-banner');
  if (stratBanner) {
    const allRaces = activeMeeting.races;
    const passingRaces = allRaces.filter(raceStratPass);
    const selectedLegRaces = quaddieState.legRaceIds
      .map(rid => allRaces.find(r => r.race_id === rid))
      .filter(Boolean);
    const selectedPassing = selectedLegRaces.filter(raceStratPass).length;
    const allSelectedPass = selectedLegRaces.length === 4 && selectedPassing === 4;
    let html = '';
    if (selectedLegRaces.length === 4) {
      // Quaddie is fully built - emphasise pass/fail status for the whole quaddie
      if (allSelectedPass) {
        html = '<div class="stratb pass-quaddie">' +
          '<span class="ico">✓</span>' +
          '<span class="lbl">All 4 selected legs meet strategy</span>' +
          '<span class="meta">prize $50k+ and 8+ runners per leg</span>' +
          '</div>';
      } else {
        const failing = selectedLegRaces.length - selectedPassing;
        html = '<div class="stratb fail-quaddie">' +
          '<span class="ico">✗</span>' +
          '<span class="lbl">' + failing + ' of 4 selected legs fail strategy</span>' +
          '<span class="meta">strategy needs prize $50k+ and 8+ runners per leg</span>' +
          '</div>';
      }
    } else {
      // No full quaddie yet - just show meeting-level summary
      html = '<div class="stratb info">' +
        '<span class="lbl">Strategy:</span>' +
        '<span class="meta">' + passingRaces.length + ' of ' + allRaces.length +
        ' races meet bet criteria (prize $50k+, field 8+)</span>' +
        '</div>';
    }
    stratBanner.innerHTML = html;
    stratBanner.style.display = 'block';
  }

  // Wire race-card click handlers
  grid.querySelectorAll('.quaddie-race-card').forEach(card => {
    card.addEventListener('click', () => {
      const rid = card.dataset.rid;
      const idx = quaddieState.legRaceIds.indexOf(rid);
      if (idx >= 0) {
        // Already selected, remove
        quaddieState.legRaceIds.splice(idx, 1);
      } else {
        if (quaddieState.legRaceIds.length >= 4) {
          // Replace the oldest pick (first leg) so user can keep adding
          quaddieState.legRaceIds.shift();
        }
        quaddieState.legRaceIds.push(rid);
      }
      saveQuaddieState();
      renderQuaddie();
    });
  });

  // Render legs and summary
  if (quaddieState.legRaceIds.length === 0) {
    legsWrap.style.display = 'none';
    return;
  }

  legsWrap.style.display = 'block';
  renderQuaddieLegs(activeMeeting, thresh);
}

function renderQuaddieLegs(meeting, thresh) {
  // Sort selected legs by start_time so leg 1 is first to jump
  const legRaces = quaddieState.legRaceIds
    .map(rid => meeting.races.find(r => r.race_id === rid))
    .filter(r => r != null);
  legRaces.sort((a, b) => (a.start_time || '').localeCompare(b.start_time || '') || (a.race - b.race));

  // Compute per-leg picks + coverage
  const perLeg = legRaces.map(r => {
    const quals = r.runners
      .filter(u => u.cs != null && u.cs >= thresh)
      .sort((a, b) => (a.crk || 99) - (b.crk || 99));
    return {
      race: r,
      quals: quals,
      // Pick the matching coverage curve - Path A is more accurate when jt_combo
      // data is in the API response, Path B is the proxy fallback
      coverage: legCoverage(quals.length, r.cs_path || 'B'),
    };
  });

  // Combos = product of qualifying counts (treat 0 as 1 with a flag, since user
  // can't bet a leg with no horses; we'll flag it but compute "what if you took rank 1")
  let combos = 1;
  let allLegsHaveQuals = true;
  perLeg.forEach(leg => {
    const n = leg.quals.length || 1;
    combos *= n;
    if (leg.quals.length === 0) allLegsHaveQuals = false;
  });

  // Hit rate = product of per-leg coverage. If a leg is empty, fall back to top-1 coverage.
  let hitRate = 1.0;
  perLeg.forEach(leg => {
    const n = leg.quals.length || 1;
    hitRate *= legCoverage(n, leg.race.cs_path || 'B');
  });
  // If only 1-3 legs selected, the hit rate is for that subset
  const isComplete = perLeg.length === 4;

  // Render summary
  const unitDollars = settings.unitDollar || 1;
  const targetReturn = settings.targetReturn || 4;
  // Cost: assume $1 unit per combo by default (user can scale)
  const costPerUnit = combos;  // in units
  const costInDollars = combos * 1;  // $1 per combo as a baseline reference
  const costInUserUnits = combos;  // user enters their own outlay

  const fsAnyLeg = perLeg.some(l => l.race.hfs);

  document.getElementById('quaddie-summary').innerHTML =
    '<div class="qs-stat"><span class="lbl">Legs selected</span>' +
      '<span class="val">' + perLeg.length + ' / 4</span>' +
      '<span class="sub">' + meeting.venue + '</span>' +
    '</div>' +
    '<div class="qs-stat"><span class="lbl">Combos</span>' +
      '<span class="val">' + combos + '</span>' +
      '<span class="sub">' + perLeg.map(l => l.quals.length || 0).join(' × ') +
        (isComplete ? '' : ' (need 4 legs)') + '</span>' +
    '</div>' +
    '<div class="qs-stat"><span class="lbl">' + (isComplete ? 'Hit rate' : 'Coverage so far') + '</span>' +
      '<span class="val ' + (hitRate > 0.15 ? 'pos' : (hitRate < 0.05 ? 'neg' : '')) + '">' +
        (hitRate * 100).toFixed(1) + '%</span>' +
      '<span class="sub">' + (isComplete
        ? 'all 4 winners covered'
        : 'partial - ' + perLeg.length + ' of 4 legs') + '</span>' +
    '</div>' +
    '<div class="qs-stat"><span class="lbl">Cost @ $1 unit</span>' +
      '<span class="val">$' + combos + '</span>' +
      '<span class="sub">$' + (combos * unitDollars).toFixed(0) + ' @ ' + unitDollars + 'u/combo</span>' +
    '</div>' +
    '<div class="qs-actions">' +
      '<button class="btn-tiny" id="quaddie-clear">Clear legs</button>' +
      '<button class="btn-tiny" id="quaddie-export">Copy picks</button>' +
    '</div>';

  // Render leg cards
  document.getElementById('quaddie-legs').innerHTML = perLeg.map((leg, idx) => {
    const r = leg.race;
    const time = fmtTime(r.start_time) || '—';
    const cov = leg.coverage;
    const covCls = cov < 0.5 ? ' warn' : '';
    const covText = leg.quals.length > 0
      ? leg.quals.length + ' picks · ' + (cov * 100).toFixed(0) + '% winner cov'
      : 'No picks at this threshold';
    const fsHtml = r.hfs
      ? '<div class="ql-fs-warn"><span>⚠</span><span>First starter in this race - skip recommended</span></div>'
      : '';

    // Show qualifiers, plus rank 1 and 2 fallback if no qualifiers
    let runnersHtml;
    if (leg.quals.length === 0) {
      // Show top 3 by score so user can lower threshold or accept the empty leg
      const top3 = r.runners
        .filter(u => u.cs != null)
        .sort((a, b) => (a.crk || 99) - (b.crk || 99))
        .slice(0, 3);
      runnersHtml = top3.length === 0
        ? '<div class="ql-empty">No runners with score data.</div>'
        : '<div class="ql-empty">Top 3 by score (none qualify):</div>' +
          top3.map(u => '<div class="ql-runner">' +
            '<span class="qr-tab">' + (u.tab || '?') + '</span>' +
            '<span class="qr-horse">' + escapeHtml(u.h || '') + '</span>' +
            '<span class="qr-score">' + (u.cs != null ? u.cs.toFixed(2) : '—') + '</span>' +
            '</div>').join('');
    } else {
      runnersHtml = leg.quals.map(u => '<div class="ql-runner qualifies">' +
        '<span class="qr-tab">' + (u.tab || '?') + '</span>' +
        '<span class="qr-horse">' + escapeHtml(u.h || '') + '</span>' +
        '<span class="qr-score">' + u.cs.toFixed(2) + '</span>' +
        '</div>').join('');
    }

    return '<div class="quaddie-leg-card" data-rid="' + r.race_id + '">' +
      '<div class="ql-head">' +
        '<div class="ql-title">Leg ' + (idx + 1) + ' · R' + r.race + '</div>' +
        '<button class="ql-remove" data-leg-rid="' + r.race_id + '">remove</button>' +
      '</div>' +
      '<div class="ql-meta">' + time + ' · ' + r.distance + 'm · ' + escapeHtml(r.going || '—') +
        ' · ' + r.fs + ' runners</div>' +
      fsHtml +
      '<div class="ql-coverage' + covCls + '">' + covText + '</div>' +
      '<div class="ql-runners">' + runnersHtml + '</div>' +
      '</div>';
  }).join('');

  // Wire remove buttons
  document.querySelectorAll('.ql-remove').forEach(btn => {
    btn.addEventListener('click', e => {
      e.stopPropagation();
      const rid = btn.dataset.legRid;
      quaddieState.legRaceIds = quaddieState.legRaceIds.filter(x => x !== rid);
      saveQuaddieState();
      renderQuaddie();
    });
  });

  // Wire clear legs
  const clearBtn = document.getElementById('quaddie-clear');
  if (clearBtn) clearBtn.addEventListener('click', () => {
    if (confirm('Clear all selected legs?')) {
      quaddieState.legRaceIds = [];
      saveQuaddieState();
      renderQuaddie();
    }
  });

  // Wire copy picks
  const copyBtn = document.getElementById('quaddie-export');
  if (copyBtn) copyBtn.addEventListener('click', () => {
    const lines = [];
    lines.push(meeting.venue + ' Quaddie - ' + quaddieState.date);
    lines.push('Threshold: ' + thresh.toFixed(2) + '  Combos: ' + combos +
               '  Projected hit: ' + (hitRate * 100).toFixed(1) + '%');
    lines.push('');
    perLeg.forEach((leg, idx) => {
      lines.push('Leg ' + (idx + 1) + ' (R' + leg.race.race + ' ' + fmtTime(leg.race.start_time) + ')');
      if (leg.quals.length === 0) {
        lines.push('  (no qualifying picks)');
      } else {
        leg.quals.forEach(u => {
          lines.push('  #' + (u.tab || '?') + ' ' + (u.h || '') + ' (' + u.cs.toFixed(2) + ')');
        });
      }
      lines.push('');
    });
    const text = lines.join('\n');
    if (navigator.clipboard && navigator.clipboard.writeText) {
      navigator.clipboard.writeText(text).then(() => {
        copyBtn.textContent = 'Copied!';
        setTimeout(() => copyBtn.textContent = 'Copy picks', 1500);
      });
    } else {
      // Fallback
      const ta = document.createElement('textarea');
      ta.value = text;
      document.body.appendChild(ta);
      ta.select();
      try { document.execCommand('copy'); } catch(e) {}
      document.body.removeChild(ta);
      copyBtn.textContent = 'Copied!';
      setTimeout(() => copyBtn.textContent = 'Copy picks', 1500);
    }
  });
}

// Wire Quaddie controls (date buttons, meeting selector, threshold input)
document.querySelectorAll('.quaddie-date-quick').forEach(btn => {
  btn.addEventListener('click', () => {
    const k = btn.dataset.qdate;
    if (k === 'yesterday') quaddieState.date = isoDate(-1);
    else if (k === 'tomorrow') quaddieState.date = isoDate(1);
    else quaddieState.date = isoDate(0);
    quaddieState.meetingKey = null;  // reset on date change
    quaddieState.legRaceIds = [];
    const inp = document.getElementById('quaddie-date-input');
    if (inp) inp.value = quaddieState.date;
    saveQuaddieState();
    renderQuaddie();
  });
});
const qDateInp = document.getElementById('quaddie-date-input');
if (qDateInp) {
  qDateInp.addEventListener('change', e => {
    if (e.target.value) {
      quaddieState.date = e.target.value;
      quaddieState.meetingKey = null;
      quaddieState.legRaceIds = [];
      saveQuaddieState();
      renderQuaddie();
    }
  });
}
const qMeetingSel = document.getElementById('quaddie-meeting');
if (qMeetingSel) {
  qMeetingSel.addEventListener('change', e => {
    quaddieState.meetingKey = e.target.value || null;
    quaddieState.legRaceIds = [];
    saveQuaddieState();
    renderQuaddie();
  });
}
const qThreshInp = document.getElementById('quaddie-thresh');
if (qThreshInp) {
  // Live preview: re-render on every keystroke (debounced ~150ms) so user
  // sees combo count / hit rate / cost update as they tweak the threshold.
  // The previous 'change' listener (which only fires on blur) is now redundant
  // but we keep it for safety in case 'input' doesn't fire in some browser
  // (extremely unlikely but the cost is one extra render on blur).
  let qThreshDebounceTimer = null;
  function applyQThreshChange(rawVal) {
    const v = parseFloat(rawVal);
    if (isNaN(v)) return;
    quaddieState.threshOverride = Math.max(0, Math.min(1, v));
    saveQuaddieState();
    renderQuaddie();
  }
  qThreshInp.addEventListener('input', e => {
    if (qThreshDebounceTimer) clearTimeout(qThreshDebounceTimer);
    const val = e.target.value;
    qThreshDebounceTimer = setTimeout(() => applyQThreshChange(val), 150);
  });
  qThreshInp.addEventListener('change', e => applyQThreshChange(e.target.value));
}
const qThreshReset = document.getElementById('quaddie-thresh-reset');
if (qThreshReset) {
  qThreshReset.addEventListener('click', () => {
    quaddieState.threshOverride = null;
    saveQuaddieState();
    renderQuaddie();
  });
}

// ── Init ────────────────────────────────────────────────────────────────────
currentBrowseDate = isoDate(0);
renderToday();
renderMeetingsGrid();
wirePnLControls();
renderPnL();
renderInsights();
renderNtjTicker();
setInterval(renderNtjTicker, 1000);

// ── Relative time + stale banner ────────────────────────────────────────────
function relativeTime(iso) {
  if (!iso) return '';
  const now = Date.now();
  const t = new Date(iso).getTime();
  if (isNaN(t)) return '';
  const diff = Math.max(0, now - t);
  const sec = Math.floor(diff / 1000);
  if (sec < 60) return 'just now';
  const min = Math.floor(sec / 60);
  if (min < 60) return min + ' min ago';
  const hr = Math.floor(min / 60);
  if (hr < 24) return hr + 'h ' + (min % 60) + 'm ago';
  const d = Math.floor(hr / 24);
  return d + 'd ago';
}

function updateRelativeTimes() {
  const rel = relativeTime(RUN_ISO);
  const headerRel = document.getElementById('header-run-rel');
  if (headerRel) headerRel.textContent = rel;
  const settingsRel = document.getElementById('last-fetched-rel');
  if (settingsRel) settingsRel.textContent = rel;
}
updateRelativeTimes();
setInterval(updateRelativeTimes, 60000);

// Wire up Settings: Open Actions link
const REPO_KEY = 'toprate_v3_repo';
let activeRepo = GITHUB_REPO;
try {
  const stored = localStorage.getItem(REPO_KEY);
  if (stored) activeRepo = stored.trim();
} catch(e) {}
const repoInput = document.getElementById('setting-repo');
if (repoInput) {
  repoInput.value = activeRepo;
  repoInput.addEventListener('change', e => {
    activeRepo = e.target.value.trim();
    try { localStorage.setItem(REPO_KEY, activeRepo); } catch(e) {}
    const link = document.getElementById('open-actions-link');
    if (link) link.href = 'https://github.com/' + activeRepo + '/actions/workflows/daily.yml';
  });
}
const openActionsLink = document.getElementById('open-actions-link');
if (openActionsLink) {
  openActionsLink.href = 'https://github.com/' + activeRepo + '/actions/workflows/daily.yml';
}
// Default fetch-date input to today
const fetchDateInput = document.getElementById('fetch-date-input');
if (fetchDateInput) fetchDateInput.value = isoDate(0);

// ── GitHub Actions workflow dispatch ───────────────────────────────────────
// Triggers toprate_daily.py via the workflow_dispatch event. Uses the same PAT
// configured for Gist sync, but the PAT must also have the 'workflow' scope to
// dispatch (gist scope alone is not enough).
async function dispatchWorkflow(date) {
  const statusEl = document.getElementById('fetch-status');
  function setStatus(msg, cls) {
    if (!statusEl) return;
    statusEl.textContent = msg;
    statusEl.className = 'fetch-status ' + (cls || '');
  }
  if (!syncCfg.pat) {
    setStatus('No GitHub PAT — set one up in Sync section below', 'err');
    return;
  }
  setStatus('Looking up workflow…');
  try {
    // Find the workflow ID by name/path
    const listR = await fetch('https://api.github.com/repos/' + activeRepo + '/actions/workflows', {
      headers: {
        'Authorization': 'Bearer ' + syncCfg.pat,
        'Accept': 'application/vnd.github+json',
        'X-GitHub-Api-Version': '2022-11-28',
      },
    });
    if (!listR.ok) {
      const t = await listR.text();
      setStatus('Repo error ' + listR.status + ' — token may need workflow scope', 'err');
      console.error('Workflow list error:', t);
      return;
    }
    const listData = await listR.json();
    const workflows = listData.workflows || [];
    const wf = workflows.find(w => w.name === 'TopRate Daily' || w.path.includes('daily.yml')) || workflows[0];
    if (!wf) {
      setStatus('No workflows in repo. Push .github/workflows/daily.yml first.', 'err');
      return;
    }
    setStatus('Dispatching ' + wf.name + (date ? ' for ' + date : ' for today') + '…');
    const inputs = date ? { date: date } : {};
    const dispR = await fetch('https://api.github.com/repos/' + activeRepo + '/actions/workflows/' + wf.id + '/dispatches', {
      method: 'POST',
      headers: {
        'Authorization': 'Bearer ' + syncCfg.pat,
        'Accept': 'application/vnd.github+json',
        'X-GitHub-Api-Version': '2022-11-28',
        'Content-Type': 'application/json',
      },
      body: JSON.stringify({ ref: 'main', inputs: inputs }),
    });
    if (dispR.status === 204) {
      setStatus('Triggered ' + (date || 'today') + '. Refresh page in ~2 min.', 'ok');
    } else {
      let msg = '';
      try { msg = (await dispR.json()).message || ''; } catch(e) {}
      setStatus('Dispatch error ' + dispR.status + ': ' + msg.slice(0, 120), 'err');
    }
  } catch (e) {
    setStatus('Failed: ' + e.message, 'err');
  }
}

// Wire fetch buttons
const btnRefetchToday = document.getElementById('btn-refetch-today');
if (btnRefetchToday) {
  btnRefetchToday.addEventListener('click', () => dispatchWorkflow(isoDate(0)));
}
const btnFetchDate = document.getElementById('btn-fetch-date');
if (btnFetchDate) {
  btnFetchDate.addEventListener('click', () => {
    const d = document.getElementById('fetch-date-input').value;
    if (!d) { alert('Pick a date first.'); return; }
    dispatchWorkflow(d);
  });
}

// ── Cross-device sync via private GitHub Gist ──────────────────────────────
// What syncs: manualOdds (user-entered prices) and a settings snapshot.
// How: POST/GET to https://api.github.com/gists/{id} using a PAT.
// Storage: token + gist ID stored in localStorage on each device.

const SYNC_KEY = 'toprate_v3_sync';
let syncCfg = { pat: '', gistId: '' };
try {
  const raw = localStorage.getItem(SYNC_KEY);
  if (raw) syncCfg = Object.assign({ pat: '', gistId: '' }, JSON.parse(raw));
} catch(e) {}

function saveSyncCfg() {
  try { localStorage.setItem(SYNC_KEY, JSON.stringify(syncCfg)); } catch(e) {}
  updateSyncUI();
}
function updateSyncUI() {
  const ok = !!(syncCfg.pat && syncCfg.gistId);
  const pill = document.getElementById('sync-state-pill');
  const status = document.getElementById('sync-status');
  if (!pill || !status) return;
  if (ok) {
    pill.textContent = 'on';
    pill.className = 'state-pill state-on';
    status.textContent = 'Synced via Gist ' + syncCfg.gistId.slice(0, 8) + '… Manual odds and settings will pull/push.';
  } else {
    pill.textContent = 'off';
    pill.className = 'state-pill state-off';
    status.textContent = 'Not configured. Add a GitHub token and Gist ID below to sync between iPhone and computer.';
  }
}
function syncLog(msg) {
  const el = document.getElementById('sync-log');
  if (!el) return;
  const t = new Date().toLocaleTimeString();
  el.textContent = '[' + t + '] ' + msg + '\\n' + el.textContent;
  // Trim
  if (el.textContent.length > 5000) el.textContent = el.textContent.slice(0, 5000);
}

// Hydrate inputs
const patInput = document.getElementById('setting-pat');
const gistInput = document.getElementById('setting-gist');
if (patInput) patInput.value = syncCfg.pat || '';
if (gistInput) gistInput.value = syncCfg.gistId || '';
if (patInput) patInput.addEventListener('change', e => { syncCfg.pat = e.target.value.trim(); saveSyncCfg(); });
if (gistInput) gistInput.addEventListener('change', e => { syncCfg.gistId = e.target.value.trim(); saveSyncCfg(); });

async function gistFetch(method, path, body) {
  if (!syncCfg.pat) throw new Error('No PAT configured');
  const url = 'https://api.github.com' + path;
  const opts = {
    method,
    headers: {
      'Accept': 'application/vnd.github+json',
      'Authorization': 'Bearer ' + syncCfg.pat,
      'X-GitHub-Api-Version': '2022-11-28',
    },
  };
  if (body) {
    opts.headers['Content-Type'] = 'application/json';
    opts.body = JSON.stringify(body);
  }
  const r = await fetch(url, opts);
  if (!r.ok) {
    // On rate-limit responses, GitHub sends X-RateLimit-Reset (unix seconds)
    // indicating when the limit resets. Capture it so the sync layer can
    // back off until then instead of hammering the API and worsening the
    // problem. 403 is GitHub's rate-limit status; 429 is the standard one
    // that GitHub uses for secondary (per-minute) limits.
    if (r.status === 403 || r.status === 429) {
      const resetHeader = r.headers.get('X-RateLimit-Reset');
      if (resetHeader) {
        const resetMs = parseInt(resetHeader, 10) * 1000;
        if (!isNaN(resetMs) && resetMs > Date.now()) {
          try {
            localStorage.setItem(SYNC_BLOCKED_UNTIL_KEY, String(resetMs));
          } catch(e) {}
        }
      } else {
        // No reset header - fall back to a 5-minute pause as a safety
        try {
          localStorage.setItem(SYNC_BLOCKED_UNTIL_KEY, String(Date.now() + 5 * 60 * 1000));
        } catch(e) {}
      }
    }
    const txt = await r.text();
    throw new Error('GitHub API ' + r.status + ': ' + txt.slice(0, 200));
  }
  return r.json();
}

async function syncCreateGist() {
  if (!syncCfg.pat) { syncLog('Need a GitHub PAT first.'); return; }
  const payload = buildSyncPayload();
  syncLog('Creating new private Gist…');
  try {
    const data = await gistFetch('POST', '/gists', {
      description: 'TopRate dashboard sync',
      public: false,
      files: { 'toprate_sync.json': { content: JSON.stringify(payload, null, 2) } },
    });
    syncCfg.gistId = data.id;
    if (gistInput) gistInput.value = syncCfg.gistId;
    saveSyncCfg();
    syncLog('Created Gist ' + data.id + '. Use the same ID on your other devices.');
  } catch (e) {
    syncLog('Failed: ' + e.message);
  }
}

async function syncTest() {
  if (!syncCfg.pat || !syncCfg.gistId) { syncLog('Need both PAT and Gist ID.'); return; }
  syncLog('Testing connection…');
  try {
    const data = await gistFetch('GET', '/gists/' + syncCfg.gistId);
    const file = (data.files && data.files['toprate_sync.json']);
    syncLog('OK. Gist accessible. ' + (file ? ('File present, ' + (file.size || '?') + ' bytes.') : 'No sync file yet — run Push to populate.'));
  } catch (e) {
    syncLog('Failed: ' + e.message);
  }
}

function buildSyncPayload() {
  return {
    version: 2,
    deviceTs: new Date().toISOString(),
    manualOdds: manualOdds,         // legacy, kept for old gists
    manualResults: manualResults,
    settings: settings,
    // Unified bet log: placed flag, odds taken, dead heat, comments per run_id
    // This is the source of truth for bet state - syncing it is what makes
    // bets visible across devices.
    betLog: getBetLog(),
    // Manual track-rating overrides keyed by venue|date - syncs your "track is
    // playing softer than official" judgments to mobile
    trackRatings: trackRatings,
    // Abandoned meetings/races - hides picks once user marks abandonment.
    // Crucial for sync because PF/TR don't surface abandonment until results,
    // and a user might mark Lismore on phone but want it hidden on desktop too.
    abandonedMeetings: abandonedMeetings,
    abandonedRaces: abandonedRaces,
  };
}

// ── Sync rate limiting ──────────────────────────────────────────────────
// Prevent runaway push frequency, which can blow through GitHub's 5,000
// requests/hour PAT limit and cause hours-long sync outages. Three guards:
//
//   1. SYNC_MIN_PUSH_INTERVAL_MS: hard floor on push frequency.  Even when
//      callers ask for an immediate flush, refuse if we pushed too recently.
//      Set to 15 seconds = max 240 pushes/hr, comfortably under the 5,000
//      cap with room for pulls too.
//
//   2. Last-pushed content hash. Many code paths bump the dirty flag without
//      actually changing payload contents (e.g. clicking the same checkbox
//      twice). Hash the serialised payload before pushing; if it matches the
//      last successful push, skip. The local dirty flag still clears, since
//      "remote already has this state" is the relevant invariant.
//
//   3. 403/429 backoff. When GitHub returns a rate-limit error, gistFetch
//      stashes X-RateLimit-Reset in SYNC_BLOCKED_UNTIL_KEY. Push refuses
//      until that time passes. Stops the cascade of failed retries that
//      makes the rate limit problem worse than it needs to be.
const SYNC_MIN_PUSH_INTERVAL_MS = 15 * 1000;
const SYNC_LAST_PUSH_KEY        = 'tr_sync_last_push_v1';
const SYNC_LAST_HASH_KEY        = 'tr_sync_last_hash_v1';
const SYNC_BLOCKED_UNTIL_KEY    = 'tr_sync_blocked_until_v1';

function _getSyncBlockedUntil() {
  try { return parseInt(localStorage.getItem(SYNC_BLOCKED_UNTIL_KEY), 10) || 0; }
  catch(e) { return 0; }
}
function _getLastPushTime() {
  try { return parseInt(localStorage.getItem(SYNC_LAST_PUSH_KEY), 10) || 0; }
  catch(e) { return 0; }
}
// Cheap deterministic string hash (djb2 variant). Doesn't need to be
// cryptographic - just needs to differ when payloads differ.
function _hashString(s) {
  let h = 5381;
  for (let i = 0; i < s.length; i++) h = ((h << 5) + h + s.charCodeAt(i)) | 0;
  return h.toString(36);
}

async function syncPush() {
  if (!syncCfg.pat || !syncCfg.gistId) { syncLog('Need both PAT and Gist ID.'); return; }

  // Guard 1: are we still blocked by a previous rate-limit response?
  const blockedUntil = _getSyncBlockedUntil();
  if (blockedUntil > Date.now()) {
    const minsLeft = Math.ceil((blockedUntil - Date.now()) / 60000);
    syncLog('Push skipped: GitHub rate limit active (' + minsLeft + 'min remaining)');
    return;
  }

  // Guard 2: minimum interval since last push. Anything inside the window
  // gets deferred - the dirty flag stays set so the next scheduled push
  // will retry. This protects against runaway flushSyncPush callers.
  const sinceLast = Date.now() - _getLastPushTime();
  if (sinceLast < SYNC_MIN_PUSH_INTERVAL_MS) {
    const waitS = Math.ceil((SYNC_MIN_PUSH_INTERVAL_MS - sinceLast) / 1000);
    syncLog('Push throttled: too soon since last push (' + waitS + 's wait)');
    return;
  }

  // Guard 3: content-hash skip. If the payload is identical to what's
  // already on the gist, no point re-uploading. Clear dirty flag since
  // remote already has the latest state.
  const payload = buildSyncPayload();
  const payloadStr = JSON.stringify(payload);
  const payloadHash = _hashString(payloadStr);
  let lastHash = null;
  try { lastHash = localStorage.getItem(SYNC_LAST_HASH_KEY); } catch(e) {}
  if (lastHash && lastHash === payloadHash) {
    syncLog('Push skipped: no changes since last push');
    clearSyncDirty();
    return;
  }

  syncLog('Pushing to Gist…');
  try {
    await gistFetch('PATCH', '/gists/' + syncCfg.gistId, {
      files: { 'toprate_sync.json': { content: JSON.stringify(payload, null, 2) } },
    });
    syncLog('Pushed ' + Object.keys(payload.betLog || {}).length + ' bet log entries + ' +
            Object.keys(payload.manualOdds || {}).length + ' odds entries + settings.');
    // Record success: timestamp + content hash, so next push can short-circuit.
    try {
      localStorage.setItem(SYNC_LAST_PUSH_KEY, String(Date.now()));
      localStorage.setItem(SYNC_LAST_HASH_KEY, payloadHash);
      localStorage.setItem('tr_sync_last_pull_v1', String(Date.now()));
    } catch(e) {}
    if (typeof updateSyncIndicator === 'function') updateSyncIndicator();
  } catch (e) {
    syncLog('Push failed: ' + e.message);
    // Re-throw so callers (debounced push, flushSyncPush) can detect failure
    // and avoid clearing the dirty flag. Without re-throwing, a failed push
    // looks identical to a successful one and the dirty work would be lost.
    throw e;
  }
}

async function syncPull() {
  if (!syncCfg.pat || !syncCfg.gistId) { syncLog('Need both PAT and Gist ID.'); return; }
  syncLog('Pulling from Gist…');
  try {
    const data = await gistFetch('GET', '/gists/' + syncCfg.gistId);
    const file = data.files && data.files['toprate_sync.json'];
    if (!file || !file.content) { syncLog('No sync file in Gist yet. Push first.'); return; }
    const payload = JSON.parse(file.content);
    if (payload.manualOdds) {
      manualOdds = payload.manualOdds;
      try { localStorage.setItem(ODDS_STORAGE_KEY, JSON.stringify(manualOdds)); } catch(e) {}
    }
    if (payload.manualResults) {
      manualResults = payload.manualResults;
      try { localStorage.setItem(RESULTS_STORAGE_KEY, JSON.stringify(manualResults)); } catch(e) {}
    }
    // Bet log: merge remote into local, with remote winning on per-run_id conflict.
    // This is the right policy because the gist holds the most-recently-pushed state
    // from any device; if the local device had unpushed work it should push first.
    if (payload.betLog && typeof payload.betLog === 'object') {
      const localLog = getBetLog();
      const merged = Object.assign({}, localLog, payload.betLog);
      saveBetLog(merged);
    }
    if (payload.settings) {
      settings = Object.assign({}, defaultSettings, payload.settings);
      try { localStorage.setItem(STORAGE_KEY, JSON.stringify(settings)); } catch(e) {}
      // Re-hydrate UI
      document.getElementById('setting-unit').value = settings.unitDollar;
      document.getElementById('setting-target').value = settings.targetReturn;
      document.getElementById('setting-min').value = settings.minStake;
      document.getElementById('setting-max').value = settings.maxStake;
      const sst = document.getElementById('setting-score-thresh');
      if (sst) sst.value = settings.scoreThreshold;
      document.getElementById('unit-display').textContent = '1u = $' + settings.unitDollar;
    }
    // Track rating overrides - same merge pattern as betLog
    if (payload.trackRatings && typeof payload.trackRatings === 'object') {
      trackRatings = Object.assign({}, trackRatings, payload.trackRatings);
      try { localStorage.setItem(TRACK_RATINGS_KEY, JSON.stringify(trackRatings)); } catch(e) {}
    }
    // Abandoned meetings/races - last-write-wins merge. Same shape as
    // trackRatings: dict keyed by (venue|date) or race_id, value is metadata.
    if (payload.abandonedMeetings && typeof payload.abandonedMeetings === 'object') {
      abandonedMeetings = Object.assign({}, abandonedMeetings, payload.abandonedMeetings);
      try { localStorage.setItem(ABANDONED_MEETINGS_KEY, JSON.stringify(abandonedMeetings)); } catch(e) {}
    }
    if (payload.abandonedRaces && typeof payload.abandonedRaces === 'object') {
      abandonedRaces = Object.assign({}, abandonedRaces, payload.abandonedRaces);
      try { localStorage.setItem(ABANDONED_RACES_KEY, JSON.stringify(abandonedRaces)); } catch(e) {}
    }
    renderToday(); renderPnL(); renderInsights();
    syncLog('Pulled ' + Object.keys(payload.betLog || {}).length + ' bet log entries + ' +
            Object.keys(payload.manualOdds || {}).length + ' odds entries + settings from ' +
            (payload.deviceTs ? new Date(payload.deviceTs).toLocaleString() : 'unknown time'));
    // Track last-pull time for the visible sync indicator
    try { localStorage.setItem('tr_sync_last_pull_v1', String(Date.now())); } catch(e) {}
    updateSyncIndicator();
  } catch (e) {
    syncLog('Pull failed: ' + e.message);
  }
}

// Wire sync buttons
const btnCreate = document.getElementById('btn-sync-create');
const btnTest = document.getElementById('btn-sync-test');
const btnPush = document.getElementById('btn-sync-push');
const btnPull = document.getElementById('btn-sync-pull');
if (btnCreate) btnCreate.addEventListener('click', syncCreateGist);
if (btnTest) btnTest.addEventListener('click', syncTest);
if (btnPush) btnPush.addEventListener('click', syncPush);
if (btnPull) btnPull.addEventListener('click', syncPull);

// Auto-push debounced when bet log or settings change
let _syncPushTimer = null;
let _syncPushPending = false;  // true while a debounced push is queued
// Dirty flag: incremented on EVERY local change, decremented after push success.
// Tracked separately from _syncPushPending so that a pull can detect "we have
// unpushed local work" and refuse to clobber it. Persisted to localStorage so
// it survives a page refresh that happens before the push completes (iOS bug
// where the tab gets backgrounded/killed mid-push).
const SYNC_DIRTY_KEY = 'tr_sync_dirty_v1';
function getSyncDirty() {
  try { return parseInt(localStorage.getItem(SYNC_DIRTY_KEY), 10) || 0; } catch(e) { return 0; }
}
function setSyncDirty(v) {
  try { localStorage.setItem(SYNC_DIRTY_KEY, String(Math.max(0, v))); } catch(e) {}
}
function bumpSyncDirty() { setSyncDirty(getSyncDirty() + 1); }
function clearSyncDirty() { setSyncDirty(0); }

function scheduleSyncPush(delayMs) {
  if (!syncCfg.pat || !syncCfg.gistId) return;  // not configured
  bumpSyncDirty();  // record that we have unpushed local work
  clearTimeout(_syncPushTimer);
  _syncPushPending = true;
  if (typeof updateSyncIndicator === 'function') updateSyncIndicator();
  // Default delay (debounce window). Combines with the rate-limit guard
  // below - if we pushed less than SYNC_MIN_PUSH_INTERVAL_MS ago, defer
  // to just after the cooldown ends so the push will actually fire when
  // its timer expires (otherwise syncPush would refuse and the dirty flag
  // would never clear until the user makes another change).
  let actualDelay = delayMs != null ? delayMs : 500;
  const sinceLast = Date.now() - _getLastPushTime();
  if (sinceLast < SYNC_MIN_PUSH_INTERVAL_MS) {
    const cooldownLeft = SYNC_MIN_PUSH_INTERVAL_MS - sinceLast;
    if (cooldownLeft > actualDelay) actualDelay = cooldownLeft + 100;
  }
  // Also respect any active 403/429 backoff
  const blockedUntil = _getSyncBlockedUntil();
  if (blockedUntil > Date.now()) {
    const blockedLeft = blockedUntil - Date.now();
    if (blockedLeft > actualDelay) actualDelay = blockedLeft + 1000;
  }
  _syncPushTimer = setTimeout(() => {
    _syncPushPending = false;
    const dirtyAtPushStart = getSyncDirty();
    syncPush()
      .then(() => {
        // If no NEW changes happened between scheduling and completion, clear
        // the dirty flag. If there were new changes, a fresh schedule will
        // have bumped the count - leave it for the next push.
        if (getSyncDirty() === dirtyAtPushStart) clearSyncDirty();
      })
      .finally(() => {
        if (typeof updateSyncIndicator === 'function') updateSyncIndicator();
      });
  }, actualDelay);
}

// Force-push immediately, cancelling any pending debounced push.
// Used as a safety net before the page goes away (visibilitychange to hidden,
// pagehide, beforeunload) so we don't lose the user's most recent change.
function flushSyncPush() {
  if (!syncCfg.pat || !syncCfg.gistId) return;
  if (!_syncPushPending && getSyncDirty() === 0) return;  // nothing to flush
  clearTimeout(_syncPushTimer);
  _syncPushPending = false;
  const dirtyAtPushStart = getSyncDirty();
  // Fire-and-forget; if it fails the dirty flag stays set so we can recover
  // on next page load (auto-pull will detect dirty and push instead of pull)
  syncPush()
    .then(() => {
      if (getSyncDirty() === dirtyAtPushStart) clearSyncDirty();
    })
    .catch(() => {})
    .finally(() => {
      if (typeof updateSyncIndicator === 'function') updateSyncIndicator();
    });
}

// Visible sync indicator: shows in the header strip so user can see when last pulled.
// Updates the existing top-right pill (between "{relative time}" and "1u = $X").
function updateSyncIndicator() {
  const el = document.getElementById('sync-pill');
  if (!el) return;
  if (!syncCfg.pat || !syncCfg.gistId) {
    el.textContent = 'sync off';
    el.className = 'sync-pill off';
    return;
  }
  // Pending push state - either currently waiting for debounce, or has unpushed
  // local work from a prior session (e.g. iOS killed the tab mid-push).
  if (_syncPushPending || getSyncDirty() > 0) {
    el.textContent = _syncPushPending ? 'pushing…' : 'unsaved';
    el.className = 'sync-pill pending';
    return;
  }
  let lastPull = null;
  try { lastPull = parseInt(localStorage.getItem('tr_sync_last_pull_v1'), 10); } catch(e) {}
  if (!lastPull || isNaN(lastPull)) {
    el.textContent = 'syncing…';
    el.className = 'sync-pill pending';
    return;
  }
  const ageMs = Date.now() - lastPull;
  const ageMin = Math.floor(ageMs / 60000);
  let label;
  if (ageMs < 30000) label = 'synced';
  else if (ageMin < 1) label = 'synced';
  else if (ageMin < 60) label = 'sync ' + ageMin + 'm';
  else label = 'sync ' + Math.floor(ageMin / 60) + 'h';
  el.textContent = label;
  el.className = ageMin > 30 ? 'sync-pill stale' : 'sync-pill ok';
}

updateSyncUI();
updateSyncIndicator();
// Refresh indicator every 30 seconds so the relative-time updates
setInterval(updateSyncIndicator, 30000);

// Auto-pull on page load if sync is configured
// (so opening the dashboard on iPhone after entering odds on computer just works)
//
// CRITICAL: if there are unpushed local changes (dirty flag set), DO NOT pull.
// Pulling would clobber the local changes with stale Gist data. This is the
// scenario where on iOS the tab gets backgrounded mid-push, the push never
// completes, and on next page load the auto-pull would erase the user's edits.
// In that case, push first (recover the local changes) then a future pull
// will get fresh data including those changes.
if (syncCfg.pat && syncCfg.gistId) {
  if (getSyncDirty() > 0) {
    // Local changes are unpushed - flush them first instead of pulling
    flushSyncPush();
  } else {
    syncPull().catch(() => {/* silent on auto-pull */});
  }
}

// Auto-pull when the tab becomes visible again (mobile users often switch
// apps between making changes on desktop and viewing on mobile)
document.addEventListener('visibilitychange', () => {
  if (document.visibilityState === 'visible' && syncCfg.pat && syncCfg.gistId) {
    // If we have unpushed local changes, push them rather than pulling.
    // This preserves changes that were queued before the tab was backgrounded.
    if (getSyncDirty() > 0) {
      flushSyncPush();
      return;
    }
    // Only re-pull if it's been more than 30 seconds since last pull
    let lastPull = 0;
    try { lastPull = parseInt(localStorage.getItem('tr_sync_last_pull_v1'), 10) || 0; } catch(e) {}
    if (Date.now() - lastPull > 30000) {
      syncPull().catch(() => {});
    }
  } else if (document.visibilityState === 'hidden') {
    // Page going to background - flush any pending bet-log push so we don't
    // lose changes when the user closes the browser/switches apps. iOS Safari
    // is particularly unreliable about firing beforeunload, so visibilitychange
    // to hidden is our primary safety net here.
    flushSyncPush();
  }
});

// Final-chance push on page unload (desktop primarily; iOS often skips this)
window.addEventListener('pagehide', flushSyncPush);
window.addEventListener('beforeunload', flushSyncPush);

// Tap the sync indicator: if there's a pending local change OR unpushed dirty
// state from a prior session (iOS killed the tab mid-push), push it now;
// otherwise pull the latest from the gist
const syncPill = document.getElementById('sync-pill');
if (syncPill) {
  syncPill.addEventListener('click', () => {
    if (!syncCfg.pat || !syncCfg.gistId) return;
    if (_syncPushPending || getSyncDirty() > 0) flushSyncPush();
    else syncPull().catch(() => {});
  });
}

// ── Bet log management ────────────────────────────────────────────────────
function updateStorageUsage() {
  const usageEl = document.getElementById('storage-usage');
  const pillEl = document.getElementById('storage-pill');
  if (!usageEl || !pillEl) return;
  try {
    const log = getBetLog();
    const entries = Object.keys(log).length;
    const placed = Object.values(log).filter(e => e.placed).length;
    const withOdds = Object.values(log).filter(e => e.placed && e.oddsTaken).length;
    const withComments = Object.values(log).filter(e => (e.comments || '').trim().length > 0).length;
    const bytes = JSON.stringify(log).length;
    const kb = (bytes / 1024).toFixed(1);
    usageEl.textContent = entries + ' entries · ' + placed + ' placed · ' +
      withOdds + ' with odds · ' + withComments + ' with notes · ' + kb + ' KB';
    pillEl.textContent = kb + ' KB';
    pillEl.className = 'state-pill state-on';
  } catch (e) {
    usageEl.textContent = 'Unable to read bet log.';
    pillEl.textContent = 'error';
    pillEl.className = 'state-pill state-err';
  }
}

function setBetlogStatus(msg, cls) {
  const el = document.getElementById('betlog-status');
  if (!el) return;
  el.textContent = msg;
  el.className = 'fetch-status ' + (cls || '');
  if (msg) setTimeout(() => { el.textContent = ''; el.className = 'fetch-status'; }, 4000);
}

// Export bet log as JSON download
const btnExportBetlog = document.getElementById('btn-export-betlog');
if (btnExportBetlog) {
  btnExportBetlog.addEventListener('click', () => {
    try {
      const log = getBetLog();
      const blob = new Blob([JSON.stringify(log, null, 2)], { type: 'application/json' });
      const a = document.createElement('a');
      a.href = URL.createObjectURL(blob);
      a.download = 'toprate_betlog_' + new Date().toISOString().slice(0,10) + '.json';
      a.click();
      setBetlogStatus('Downloaded ' + Object.keys(log).length + ' entries.', 'ok');
    } catch (e) {
      setBetlogStatus('Export failed: ' + e.message, 'err');
    }
  });
}

// Import bet log from JSON file
const btnImportBetlog = document.getElementById('btn-import-betlog');
const importFileInput = document.getElementById('import-betlog-input');
if (btnImportBetlog && importFileInput) {
  btnImportBetlog.addEventListener('click', () => importFileInput.click());
  importFileInput.addEventListener('change', e => {
    const file = e.target.files[0];
    if (!file) return;
    const reader = new FileReader();
    reader.onload = ev => {
      try {
        const incoming = JSON.parse(ev.target.result);
        if (typeof incoming !== 'object' || Array.isArray(incoming)) {
          throw new Error('Invalid format - expected an object');
        }
        const existing = getBetLog();
        let added = 0, updated = 0;
        Object.keys(incoming).forEach(rid => {
          if (existing[rid]) updated++;
          else added++;
          existing[rid] = incoming[rid];
        });
        saveBetLog(existing);
        setBetlogStatus(added + ' added, ' + updated + ' updated.', 'ok');
        updateStorageUsage();
        if (typeof renderToday === 'function') { try { renderToday(); } catch(e) {} }
        if (typeof renderPnL === 'function') { try { renderPnL(); } catch(e) {} }
      } catch (err) {
        setBetlogStatus('Import failed: ' + err.message, 'err');
      }
      importFileInput.value = '';
    };
    reader.readAsText(file);
  });
}

// Reset bet log with confirmation
const btnResetBetlog = document.getElementById('btn-reset-betlog');
if (btnResetBetlog) {
  btnResetBetlog.addEventListener('click', () => {
    const log = getBetLog();
    const count = Object.keys(log).length;
    if (count === 0) {
      setBetlogStatus('Bet log is already empty.', 'ok');
      return;
    }
    const ok = confirm('This will permanently delete ' + count + ' bet log entries. Are you sure?');
    if (!ok) return;
    try {
      localStorage.removeItem(BETLOG_KEY);
      setBetlogStatus('Cleared ' + count + ' entries.', 'ok');
      updateStorageUsage();
      if (typeof renderToday === 'function') { try { renderToday(); } catch(e) {} }
      if (typeof renderPnL === 'function') { try { renderPnL(); } catch(e) {} }
    } catch (e) {
      setBetlogStatus('Reset failed: ' + e.message, 'err');
    }
  });
}

updateStorageUsage();
"""
