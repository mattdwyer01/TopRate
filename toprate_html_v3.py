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
from datetime import datetime


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
    all_picks_list = []
    for race_id, models in model_picks_by_race.items():
        for pick in models.get(primary_model_key, []):
            # Find the parent race row for context
            race = next((r for r in races if str(r.get('race_id')) == str(race_id)), None)
            if not race:
                continue
            all_picks_list.append({
                'race_id': race_id,
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
                'rse': race.get('rse'),  # race shape early
                'rsm': race.get('rsm'),  # race shape mid
                'rsl': race.get('rsl'),  # race shape late
                'run_id': pick.get('run_id'),
                'horse': pick.get('horse'),
                'tab': pick.get('tab'),
                'fxprice': pick.get('fxprice'),
                'tr_rank': pick.get('tr_rank'),
                'early_rank': pick.get('early_rank'),
                'mid_rank': pick.get('mid_rank'),
                'late_rank': pick.get('late_rank'),
                'total_rank': pick.get('total_rank'),
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
            tp['done'] = race.get('done')

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

    # Build settled bet history for the primary model from the flat picks list
    settled_history = []
    for r in (model_pick_rows or []):
        if r.get('model') != primary_model_key:
            continue
        if not r.get('resulted'):
            continue
        race_id = r.get('race_id')
        run_id = r.get('run_id')
        # Find race context and runner full data
        race = next((rc for rc in races if str(rc.get('race_id')) == str(race_id)), None)
        runner_full = None
        if race:
            runner_full = next((u for u in race.get('runners', []) if str(u.get('rid')) == str(run_id)), None)
        settled_history.append({
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
            'runner_full': runner_full,
        })
    settled_history.sort(key=lambda r: (r.get('date') or ''))

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
.picks-list {
  display: flex; flex-direction: column;
  background: var(--panel);
  border: 1px solid var(--line);
  border-radius: var(--radius-md);
  overflow: hidden;
}
.pick-row {
  display: grid;
  grid-template-columns:
    52px              /* time */
    110px             /* venue + race # */
    minmax(220px, 1fr)  /* horse + meta */
    220px             /* signals strip - 5 pills (Score TR Mid Late Tot) */
    80px              /* odds (Fxd) */
    80px              /* stake */
    80px              /* return */
    110px             /* result */
    120px             /* bet toggle + odds-taken */
    24px;             /* expand chevron */
  gap: 10px;
  padding: 10px 14px;
  align-items: center;
  border-bottom: 1px solid var(--line-soft);
  cursor: pointer;
  transition: background 0.12s;
  position: relative;
  min-height: 48px;
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
  white-space: nowrap; overflow: hidden; text-overflow: ellipsis;
}
.pr-runner .rmeta {
  font-family: var(--font-body); font-weight: 500; font-size: 11px;
  color: var(--ink-mute); margin-top: 1px;
  white-space: nowrap; overflow: hidden; text-overflow: ellipsis;
  max-width: 100%;
}

.pr-sigs {
  display: flex; flex-direction: column; align-items: flex-start; gap: 3px;
}
.pr-sigs-top {
  display: flex; gap: 4px; align-items: center;
}
.pr-form {
  font-family: var(--font-body); font-size: 10px; color: var(--ink-mute);
  letter-spacing: 0.05em; font-weight: 600;
  font-variant-numeric: tabular-nums;
}
.pr-sigs .sig {
  display: inline-flex; align-items: baseline; gap: 3px;
  font-family: var(--font-body); font-size: 11px;
  background: var(--line-soft); border-radius: 3px;
  padding: 3px 7px; font-weight: 600; color: var(--ink-mute);
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

.pr-odds {
  display: flex; align-items: center; gap: 4px; justify-content: flex-end;
}
/* Live fixed odds display (read-only) - no border/box, looks like static text */
.pr-odds-display {
  display: inline-flex; align-items: baseline; gap: 1px;
  font-variant-numeric: tabular-nums;
  padding: 0;
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

/* Picks list column header */
.picks-header {
  display: grid;
  grid-template-columns:
    52px 110px minmax(220px, 1fr) 220px 80px 80px 80px 110px 120px 24px;
  gap: 10px;
  padding: 8px 14px;
  align-items: center;
  background: var(--panel);
  border: 1px solid var(--line);
  border-bottom: none;
  border-radius: var(--radius-md) var(--radius-md) 0 0;
}
.picks-header > div {
  font-family: var(--font-body); font-size: 10px; font-weight: 600;
  text-transform: uppercase; letter-spacing: 0.06em; color: var(--ink-mute);
}
.picks-header .th-right { text-align: right; }
.picks-list {
  border-top-left-radius: 0; border-top-right-radius: 0;
}
@media (max-width: 720px) {
  .picks-header { display: none; }
  .picks-list { border-top-left-radius: var(--radius-md); border-top-right-radius: var(--radius-md); }
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
  display: flex; gap: 4px; justify-content: flex-end; align-items: center;
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
.pr-result .res-tag.manual {
  border: 1px dashed currentColor;
}
.pr-result .res-clear {
  cursor: pointer; color: var(--ink-faint); font-size: 13px;
  padding: 0 3px; line-height: 1;
}
.pr-result .res-clear:hover { color: var(--rose); }

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

/* Mobile: pick rows stack into card-like layout */
@media (max-width: 720px) {
  .pick-row {
    grid-template-columns: 1fr 1fr 1fr;
    grid-template-areas:
      'time   time   chev'
      'venue  venue  venue'
      'runner runner runner'
      'sigs   sigs   sigs'
      'odds   stake  return'
      'result result result'
      'bet    bet    bet';
    gap: 8px 12px;
    padding: 12px;
  }
  .pr-time { grid-area: time; }
  .pr-venue { grid-area: venue; flex-direction: row; gap: 8px; align-items: baseline; }
  .pr-venue .v-race { margin-top: 0; }
  .pr-runner { grid-area: runner; }
  .pr-sigs { grid-area: sigs; }
  .pr-odds { grid-area: odds; justify-content: flex-start; }
  .pr-stake { grid-area: stake; text-align: center; }
  .pr-return { grid-area: return; text-align: right; }
  .pr-result { grid-area: result; justify-content: flex-start; flex-wrap: wrap; }
  .pr-bet { grid-area: bet; justify-content: flex-start; }
  .pr-chev { grid-area: chev; }
  .pd-speed { grid-template-columns: repeat(2, 1fr); }
  .pd-context { grid-template-columns: 1fr 1fr; }
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

/* Pace map - settling positions */
.race-pace-map {
  background: var(--panel); border-left: 1px solid var(--line);
  border-right: 1px solid var(--line); border-bottom: 1px solid var(--line);
  padding: 14px 20px;
}
.pace-map-grid {
  display: grid; grid-template-columns: repeat(auto-fit, minmax(150px, 1fr));
  gap: 12px;
}
.pace-zone {
  background: var(--line-soft); border-radius: var(--radius-sm);
  padding: 10px 12px;
}
.pace-zone .zone-lbl {
  font-family: var(--font-body); font-size: 10px; font-weight: 600;
  text-transform: uppercase; letter-spacing: 0.06em;
  color: var(--ink-mute); margin-bottom: 6px;
  display: flex; justify-content: space-between;
}
.pace-zone .zone-tabs {
  display: flex; flex-wrap: wrap; gap: 4px;
}
.pace-zone .zone-tab {
  display: inline-block; min-width: 22px; height: 22px; line-height: 22px;
  text-align: center; background: var(--panel); color: var(--ink);
  font-family: var(--font-body); font-size: 11px; font-weight: 700;
  border: 1px solid var(--line); border-radius: 4px; padding: 0 6px;
}
.pace-zone.zone-leaders  { background: #fef3c7; }
.pace-zone.zone-onpace   { background: var(--emerald-bg); }
.pace-zone.zone-midfield { background: #eff6ff; }
.pace-zone.zone-back     { background: #fdf2f8; }

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
}
.race-header-stats .item { color: #a8a29e; }
.race-header-stats .item .v { color: #fafaf9; font-weight: 700; }

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
}
.race-table thead th:hover { background: #ede9e1; }
.race-table tbody td {
  padding: 9px 12px; border-bottom: 1px solid var(--line-soft);
  white-space: nowrap; font-weight: 500;
}
.race-table tbody tr:hover { background: var(--line-soft); }
.race-table tbody tr.is-pick {
  background: var(--emerald-bg);
}
.race-table tbody tr.is-pick:hover { background: #d1fae5; }
.race-table tbody tr.muted { color: var(--ink-mute); }
.tn-cell {
  display: inline-block; min-width: 22px; height: 22px; line-height: 22px;
  text-align: center; background: var(--ink); color: var(--panel);
  font-weight: 700; border-radius: 4px; padding: 0 6px;
  font-size: 11px;
}
.horse-cell { font-weight: 700; color: var(--ink); }
.is-pick .horse-cell { color: var(--emerald-deep); }

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

/* ── Insights tab ──────────────────────────────────────────────────────── */
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
  .hero-stat .val { font-size: 18px; }

  /* Race tab */
  .race-table { font-size: 11px; }
  .race-table thead th, .race-table tbody td { padding: 8px 8px; }
  .race-table-wrap { overflow-x: auto; }
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
    grid-template-columns: repeat(2, 1fr);
  }
  .pnl-stat { padding: 10px 12px; }
  .pnl-stat .val { font-size: 18px; }
  .pnl-chart-card { padding: 14px 16px; }

  /* Insights */
  .insight-card { padding: 14px 16px; }
  .insight-card h3 { font-size: 13px; }
  .insight-card .desc { font-size: 11px; }
  .perf-bar { grid-template-columns: 80px 1fr auto auto; gap: 8px; }
  .perf-bar .label { font-size: 11px; }
  .perf-bar .label .sub { display: block; margin-left: 0; }
  .dist-bar { grid-template-columns: 70px 1fr auto; gap: 8px; }
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
    <div class="tab" data-tab="pnl">P&amp;L</div>
    <div class="tab" data-tab="insights">Insights</div>
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

    <div class="race-date-bar" id="today-date-bar">
      <div class="race-date-controls">
        <button class="today-date-quick race-date-quick" data-tdate="yesterday">Yesterday</button>
        <button class="today-date-quick race-date-quick active" data-tdate="today">Today</button>
        <button class="today-date-quick race-date-quick" data-tdate="tomorrow">Tomorrow</button>
        <input type="date" id="today-date-input" class="race-date-input">
      </div>
      <div class="race-date-info" id="today-date-info">&mdash;</div>
    </div>
    <div class="picks-header" id="picks-header">
      <div>Time</div>
      <div>Meeting</div>
      <div>Runner</div>
      <div>Signals</div>
      <div class="th-right">Fxd</div>
      <div class="th-right">Stake</div>
      <div class="th-right">Return</div>
      <div class="th-right">Result</div>
      <div class="th-right">Odds taken</div>
      <div></div>
    </div>
    <div class="picks-list" id="picks-list">
      <!-- populated by JS -->
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
        <div class="race-pace-map" id="rd-pace-map"></div>
        <div class="race-table-wrap" id="rd-runners-table"></div>
      </div>
    </div>
  </section>

  <!-- PNL -->
  <section class="section" id="sec-pnl">
    <!-- Top control bar: period selector + view mode toggle -->
    <div class="pnl-controls">
      <div class="pnl-period-group" role="group" aria-label="Time period">
        <button class="pnl-period-btn active" data-period="7d">7d</button>
        <button class="pnl-period-btn" data-period="30d">30d</button>
        <button class="pnl-period-btn" data-period="all">All time</button>
        <button class="pnl-period-btn" data-period="custom">Custom</button>
      </div>
      <div class="pnl-period-custom" id="pnl-custom-range" style="display:none;">
        <input type="date" id="pnl-date-from" />
        <span style="color:var(--ink-mute);">→</span>
        <input type="date" id="pnl-date-to" />
      </div>
      <div class="pnl-view-toggle" role="group" aria-label="View mode">
        <span class="pnl-view-label">View:</span>
        <button class="pnl-view-btn active" data-view="actual">Actual</button>
        <button class="pnl-view-btn" data-view="theoretical">Theoretical</button>
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
      <div class="picks-header" id="bh-picks-header">
        <div>Date</div>
        <div>Meeting</div>
        <div>Runner</div>
        <div>Signals</div>
        <div class="th-right">Fxd</div>
        <div class="th-right">Stake</div>
        <div class="th-right">Return</div>
        <div class="th-right">Result</div>
        <div class="th-right">Odds taken</div>
        <div></div>
      </div>
      <div class="bh-list picks-list" id="bh-list">
        <!-- populated by JS - rich cards like Today tab -->
      </div>
    </div>
  </section>

  <!-- INSIGHTS -->
  <section class="section" id="sec-insights">
    <div class="insights-grid">
      <div class="insight-card">
        <h3>Bets by price band</h3>
        <div class="desc">Distribution of primary model picks by fixed-win price. Higher bands carry more variance but also more upside.</div>
        <div class="dist-bars" id="dist-price"></div>
      </div>

      <div class="insight-card">
        <h3>Bets by venue</h3>
        <div class="desc">Where the model finds qualifying bets most often. Click to drill into venue-specific performance.</div>
        <div class="dist-bars" id="dist-venue"></div>
      </div>

      <div class="insight-card">
        <h3>Performance by going</h3>
        <div class="desc">Win rate and ROI by track surface. Helps identify whether the model is biased toward Good vs Heavy tracks.</div>
        <div class="dist-bars" id="perf-going"></div>
      </div>

      <div class="insight-card">
        <h3>Performance by signal strength</h3>
        <div class="desc">Picks broken down by TR rank. Tighter filters (TR=1) typically have stronger edges than looser ones (TR=2 or 3).</div>
        <div class="dist-bars" id="perf-signal"></div>
      </div>

      <div class="insight-card">
        <h3>Performance by day of week</h3>
        <div class="desc">Helps spot whether weekends or midweek meetings produce better edges. Saturday metropolitan racing is typically more competitive than midweek country.</div>
        <div class="dist-bars" id="perf-dow"></div>
      </div>
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

function saveSettings() {
  try { localStorage.setItem(STORAGE_KEY, JSON.stringify(settings)); } catch(e) {}
  document.getElementById('unit-display').textContent = '1u = $' + settings.unitDollar;
  // Re-render anything that uses settings
  renderToday();
  renderPnL();
  renderInsights();
}

['setting-unit','setting-target','setting-min','setting-max'].forEach(id => {
  const el = document.getElementById(id);
  if (!el) return;
  el.addEventListener('change', () => {
    const v = parseFloat(el.value);
    if (isNaN(v)) return;
    if (id === 'setting-unit') settings.unitDollar = v;
    if (id === 'setting-target') settings.targetReturn = v;
    if (id === 'setting-min') settings.minStake = v;
    if (id === 'setting-max') settings.maxStake = v;
    saveSettings();
  });
});
// Apply initial values
document.getElementById('setting-unit').value = settings.unitDollar;
document.getElementById('setting-target').value = settings.targetReturn;
document.getElementById('setting-min').value = settings.minStake;
document.getElementById('setting-max').value = settings.maxStake;
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

// ── TODAY tab rendering ────────────────────────────────────────────────────
// State: which date is being browsed in the Today tab. Null until first render,
// then defaults to local today. Persisted across re-renders within the session.
let currentTodayDate = null;

function renderToday() {
  const list = document.getElementById('picks-list');
  list.innerHTML = '';

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
  const todaysPicks = (PICKS_TODAY || []).filter(p => p.date === browseDate);

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
    const dates = [...new Set((PICKS_TODAY || []).map(p => p.date).filter(Boolean))];
    let hint = '';
    if (dates.length > 0) {
      hint = '<div class="sub" style="margin-top:12px;">Picks available for: ' +
        dates.slice(-3).join(', ') + '. Pick a different date above or use the Race tab to browse.</div>';
    }
    list.innerHTML = '<div class="empty-state"><div class="head">No picks for ' + browseDate + '</div>' +
      '<div class="sub">The model did not find any qualifying runners on this date, or the data has not been refreshed yet.</div>' + hint + '</div>';
    const hdrEmpty = document.getElementById('picks-header');
    if (hdrEmpty) hdrEmpty.style.display = 'none';
    return;
  }
  // Show header (in case it was hidden previously)
  const hdrShow = document.getElementById('picks-header');
  if (hdrShow && window.matchMedia('(min-width: 721px)').matches) {
    hdrShow.style.display = 'grid';
  }

  const minOdds = (MODEL_META[PRIMARY_KEY] && MODEL_META[PRIMARY_KEY].min_odds) || 3.0;

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
    const sigsTopHtml =
      sigPill('Score', p.crk) +
      sigPill('TR', p.tr_rank) +
      sigPill('Mid', p.mid_rank) +
      sigPill('Late', p.late_rank) +
      sigPill('Tot', p.total_rank);
    // Form string row underneath: "3-1-7-2"
    const formHtml = r.fm ?
      '<div class="pr-form" title="Last 4 finishes">' + escapeHtml(r.fm) + '</div>' : '';
    const sigsHtml = '<div class="pr-sigs-top">' + sigsTopHtml + '</div>' + formHtml;

    // Live fixed odds display (read-only)
    const oddsCls = meetsThreshold ? 'qualifies' : 'below';
    const oddsValStr = csvPrice != null ? csvPrice.toFixed(2) : '—';
    const oddsValCls = csvPrice != null ? 'v' : 'v empty';
    const oddsHtml =
      '<div class="pr-odds-display ' + oddsCls + '" title="Live fixed odds at last refresh">' +
        (csvPrice != null ? '<span class="cur">$</span>' : '') +
        '<span class="' + oddsValCls + '">' + oddsValStr + '</span>' +
      '</div>';

    // Stake display - units (large) + dollar value (small) below
    // Return display - same shape: units returned + dollar return below
    // Both muted when calculated from fallback fxprice (no odds-taken yet).
    const stakeWrapCls = 'pr-stake' + (usingFallback ? ' muted' : '');
    const returnWrapCls = 'pr-return' + (usingFallback ? ' muted' : '');
    let stakeHtml, returnHtml;
    if (isActiveBet && stake) {
      // Stake: how much I'm putting down
      stakeHtml = '<span class="units">' + stake.toFixed(2) + 'u</span>' +
        '<span class="ret">' + fmtDollar(stake) + '</span>';

      // Return: gross payout if bet wins.
      // Dead heat halves the return (joint winner).
      const dhMult = betEntry.deadHeat ? 0.5 : 1;
      const returnUnits = stake * stakePrice * dhMult;
      returnHtml = '<span class="units">' + returnUnits.toFixed(2) + 'u</span>' +
        '<span class="ret">' + fmtDollar(returnUnits) + '</span>';
    } else if (!isActiveBet) {
      stakeHtml = '<span class="skip">no bet</span>';
      returnHtml = '<span class="skip">&mdash;</span>';
    } else {
      stakeHtml = '<span class="skip">enter odds</span>';
      returnHtml = '<span class="skip">&mdash;</span>';
    }

    // Result column
    let resultHtml;
    if (hasOfficial) {
      resultHtml = '<span class="res-tag ' + (displayWon ? 'win' : 'loss') + '">' +
        (displayWon ? 'W' : 'L') + ' · ' + officialFinish + ord(officialFinish) + '</span>';
    } else if (manRes) {
      resultHtml = '<span class="res-tag manual ' + (displayWon ? 'win' : 'loss') + '" onclick="event.stopPropagation();">' +
        (displayWon ? 'W' : 'L') + ' · ' + manRes.finish + ord(manRes.finish) +
        '<span class="res-clear" data-clear-rid="' + p.run_id + '" title="Clear">×</span>' +
        '</span>';
    } else {
      resultHtml = '<button data-set-rid="' + p.run_id + '" data-pos="1" onclick="event.stopPropagation();">1st</button>' +
        '<button data-set-rid="' + p.run_id + '" data-pos="2" onclick="event.stopPropagation();">2nd</button>' +
        '<button data-set-rid="' + p.run_id + '" data-pos="3" onclick="event.stopPropagation();">3rd</button>' +
        '<button class="lost-btn" data-set-rid="' + p.run_id + '" data-pos="0" onclick="event.stopPropagation();">L</button>';
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

    row.innerHTML =
      '<div class="pr-time">' + fmtTime(p.start_time) + ttjHtml + '</div>' +
      '<div class="pr-venue">' +
        '<div class="v-name">' + escapeHtml(p.venue || '') + '</div>' +
        '<div class="v-race">R' + p.race + '</div>' +
      '</div>' +
      '<div class="pr-runner">' +
        '<span class="tab-bdg">' + (p.tab || '?') + '</span>' +
        '<div class="rdetails">' +
          '<div class="rhorse">' + escapeHtml(p.horse || '') + '</div>' +
          '<div class="rmeta">' + metaLine + '</div>' +
        '</div>' +
      '</div>' +
      '<div class="pr-sigs">' + sigsHtml + '</div>' +
      '<div class="pr-odds">' + oddsHtml + '</div>' +
      '<div class="' + stakeWrapCls + '">' + stakeHtml + '</div>' +
      '<div class="' + returnWrapCls + '">' + returnHtml + '</div>' +
      '<div class="pr-result">' + resultHtml + '</div>' +
      '<div class="pr-bet">' + betHtml + '</div>' +
      '<div class="pr-chev">▾</div>';

    list.appendChild(row);

    // Detail panel (initially hidden)
    const detail = document.createElement('div');
    detail.className = 'pick-detail';
    detail.dataset.idx = idx;
    detail.innerHTML = buildDetailHTML(p, r);
    list.appendChild(detail);

    // Click row to expand/collapse (but not when clicking inputs/buttons)
    row.addEventListener('click', e => {
      if (e.target.closest('.odds-input, .odds-input-wrap, .pr-result button, .res-clear, .bet-btn')) return;
      const isExpanded = row.classList.toggle('expanded');
      detail.classList.toggle('show', isExpanded);
    });
  });

  // Result chip handlers
  list.querySelectorAll('[data-set-rid]').forEach(el => {
    el.addEventListener('click', e => {
      e.stopPropagation();
      const rid = el.dataset.setRid;
      const pos = parseInt(el.dataset.pos);
      manualResults[String(rid)] = { finish: pos, ts: new Date().toISOString() };
      saveResults();
      renderToday();
    });
  });
  list.querySelectorAll('[data-clear-rid]').forEach(el => {
    el.addEventListener('click', e => {
      e.stopPropagation();
      const rid = el.dataset.clearRid;
      delete manualResults[String(rid)];
      saveResults();
      renderToday();
    });
  });
  // Bet toggle button
  list.querySelectorAll('[data-bet-rid]').forEach(el => {
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
  list.querySelectorAll('[data-odds-rid]').forEach(el => {
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
  list.querySelectorAll('[data-deadheat-rid]').forEach(el => {
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

  const contextHtml = '<div class="pd-context">' +
    field('Form',          r.fm) +
    field('Drift',         driftStr, driftCls) +
    field('Settles',       settleStr) +
    field('Speed rating',  r.spd != null ? r.spd.toFixed(0) : null) +
    field('TR price',      r.trp != null ? '$' + r.trp.toFixed(2) : null) +
    field('Distance',      p.distance ? p.distance + 'm' : null) +
    field('Going',         p.going) +
    field('Field size',    p.field_size || r.fs) +
    field('Distance perf', distPerf) +
    field('Going perf',    goingPerf) +
    field('Wt today',      r.wt != null ? r.wt + 'kg' : null) +
    field('Wt trend',      r.wtr != null ? (r.wtr > 0 ? '+' : '') + r.wtr.toFixed(1) + 'kg' : null) +
    field('Jockey',        r.j) +
    field('Jky 90d',       r.jw != null ? r.jw.toFixed(1) + '% wins' : null) +
    field('Trainer',       r.tn) +
    field('Trn 365d',      r.tw != null ? r.tw.toFixed(1) + '% wins' : null) +
    field('Barrier',       r.b) +
    field('Recent WPR',    wprStr) +
  '</div>';

  // Bet adjustments - dead heat toggle (only shown when bet is placed)
  const bEntry = getBetEntry(p.run_id);
  let adjustmentsHtml = '';
  if (bEntry.placed) {
    const dhChecked = bEntry.deadHeat ? 'checked' : '';
    adjustmentsHtml =
      '<div class="pd-section">' +
        '<div class="pd-section-title">Bet adjustments</div>' +
        '<label class="pd-toggle" onclick="event.stopPropagation();">' +
          '<input type="checkbox" data-deadheat-rid="' + p.run_id + '" ' + dhChecked + '>' +
          '<span class="pd-toggle-lbl">Dead heat</span>' +
          '<span class="pd-toggle-help">Halves the return on a winning bet (joint winner)</span>' +
        '</label>' +
      '</div>';
  }

  return '<div class="pd-section"><div class="pd-section-title">Context</div>' + contextHtml + '</div>' +
         '<div class="pd-section"><div class="pd-section-title">Speed scores</div>' + speedHtml + '</div>' +
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
    html += '<div class="mt-row">';
    html += '<div class="mt-venue-col">' +
      '<div class="mt-venue-name">' + escapeHtml(m.venue) + '</div>' +
      (m.state ? '<div class="mt-venue-state">' + escapeHtml(m.state) + '</div>' : '') +
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
      const hasPick = !!((MODEL_PICKS[race.race_id] || {})[PRIMARY_KEY] || []).length;

      let cellCls = 'mt-race-cell';
      if (hasPick) cellCls += ' has-pick';
      let badge = '';
      let lbl = tm || ('R' + i);
      if (isResulted) { cellCls += ' mt-resulted'; lbl = 'Result'; }
      else if (isImminent) {
        cellCls += ' mt-imminent';
        badge = '<span class="mt-cd">' + (mins <= 0 ? 'NOW' : mins + 'm') + '</span>';
      }
      else if (isSoon) { cellCls += ' mt-soon'; badge = '<span class="mt-cd-soon">' + mins + 'm</span>'; }
      else if (isPast && !isResulted) cellCls += ' mt-pending-late';

      html += '<div class="' + cellCls + '" data-rid="' + race.race_id + '">' +
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
  // Reset sort to TR$ rank ascending whenever a new race is opened
  raceSortState = { col: 'tr', dir: 'asc' };
  renderRaceDetail(raceId);
}

function exitRaceDetail() {
  document.getElementById('race-browser').style.display = 'block';
  document.getElementById('race-detail').style.display = 'none';
  currentRaceId = null;
}

// Race detail sort state - {column: name, dir: 'asc'|'desc'}
let raceSortState = { col: 'tr', dir: 'asc' };

function renderRaceDetail(raceId) {
  const race = RACES.find(r => String(r.race_id) === String(raceId));
  if (!race) {
    document.getElementById('rd-title').textContent = 'Race not found';
    return;
  }
  const picks = (MODEL_PICKS[raceId] || {})[PRIMARY_KEY] || [];
  const pickIds = new Set(picks.map(p => String(p.run_id)));
  const runners = race.runners || [];

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
      const rPicks = (MODEL_PICKS[r.race_id] || {})[PRIMARY_KEY] || [];
      const hasPick = rPicks.length > 0;
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

  // Top 3 by cumulative score (predictive composite for exotics)
  const topByScore = runners.filter(u => u.crk != null)
    .sort((a, b) => a.crk - b.crk).slice(0, 3);
  const top3ScoreHtml = topByScore.length === 3
    ? '<div class="score-top3" title="Top 3 by predictive composite score (TR + form + late-speed)">' +
        '<span class="lbl">Top 3 by score</span>' +
        '<span class="tabs">' +
          topByScore.map(u => '<span class="tab-num">#' + (u.tab || '?') + '</span>').join('') +
        '</span>' +
      '</div>'
    : '';

  document.getElementById('rd-header-stats').innerHTML =
    '<div class="item">' + fmtTime(race.start_time) + '</div>' +
    '<div class="item">' + race.distance + 'm</div>' +
    '<div class="item">' + escapeHtml(race.going || '') + '</div>' +
    '<div class="item">$' + (race.prize/1000).toFixed(0) + 'k</div>' +
    '<div class="item">' + runners.length + ' runners</div>' +
    '<div class="item"><span class="v">' + picks.length + '</span> model pick' + (picks.length !== 1 ? 's' : '') + '</div>' +
    top3ScoreHtml +
    '<div class="race-pace-est ' + paceClass + '"><span class="lbl">Pace</span>' + paceDisplay + '</div>';

  // Context bar
  const ctx = [];
  ctx.push({ lbl: 'Distance', v: race.distance + 'm' });
  ctx.push({ lbl: 'Going', v: race.going || '—' });
  ctx.push({ lbl: 'Prize', v: '$' + (race.prize / 1000).toFixed(0) + 'k' });
  ctx.push({ lbl: 'Field', v: runners.length });
  document.getElementById('rd-context-bar').innerHTML =
    ctx.map(c =>
      '<div class="ctx-item">' + c.lbl + '<span class="ctx-v">' + escapeHtml(String(c.v)) + '</span></div>'
    ).join('');

  // ── Pace map ──
  const settled = { leaders: [], onpace: [], midfield: [], back: [] };
  runners.forEach(u => {
    const pos = u.asp;
    let zone = 'midfield';
    if (pos == null) zone = 'midfield';
    else if (pos <= 2) zone = 'leaders';
    else if (pos <= 4) zone = 'onpace';
    else if (pos <= 8) zone = 'midfield';
    else zone = 'back';
    settled[zone].push(u);
  });
  const paceHtml =
    '<div class="pace-map-grid">' +
    paceZoneHtml('zone-leaders',  'Leaders',  '(1-2)', settled.leaders) +
    paceZoneHtml('zone-onpace',   'On-pace',  '(3-4)', settled.onpace) +
    paceZoneHtml('zone-midfield', 'Midfield', '(5-8)', settled.midfield) +
    paceZoneHtml('zone-back',     'Back',     '(9+)',  settled.back) +
    '</div>';
  document.getElementById('rd-pace-map').innerHTML = paceHtml;

  // ── Compute ranks ──
  function computeRanks(runners, getter) {
    const valid = runners.filter(r => getter(r) != null);
    valid.sort((a, b) => getter(b) - getter(a));
    const ranks = {};
    valid.forEach((r, i) => { ranks[r.rid] = i + 1; });
    return ranks;
  }
  const trRanks    = computeRanks(runners, r => r.trr);
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
  const todayGoing = goingCategory(race.going);

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
  function scoreCell(score, rank) {
    if (score == null || rank == null) return '<td class="score-cell">—</td>';
    const rkCls = rank === 1 ? 'r1' : (rank === 2 ? 'r2' : (rank === 3 ? 'r3' : ''));
    return '<td class="score-cell ' + rkCls + '" title="Predictive composite (TR + form + late-speed). Rank ' + rank + ' in field.">' +
      '<span class="v">' + score.toFixed(2) + '</span>' +
      '<span class="rk">#' + rank + '</span>' +
      '</td>';
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
    const trR = trRanks[rid];
    const trClass = trR === 1 ? 'r1' : (trR === 2 ? 'r2' : (trR === 3 ? 'r3' : ''));
    const fxp = u.fx;
    const trp = u.trp;

    rowsHtml += '<tr class="' + (isPick ? 'is-pick' : (trR > 5 ? 'muted' : '')) + '">' +
      '<td><span class="tn-cell">' + (u.tab || '?') + '</span></td>' +
      '<td class="horse-cell">' + escapeHtml(u.h || '') + '</td>' +
      '<td>' + escapeHtml(u.j || '') + '</td>' +
      '<td>' + escapeHtml(u.tn || '') + '</td>' +
      '<td>' + (u.b || '') + '</td>' +
      '<td class="rank-cell ' + trClass + '">' + (trR || '—') + '</td>' +
      '<td>' + (trp ? '$' + trp.toFixed(2) : '—') + '</td>' +
      '<td>' + (fxp ? '$' + fxp.toFixed(2) : '—') + '</td>' +
      scoreCell(u.cs, u.crk) +
      '<td>' + settlesLabel(u.asp) + '</td>' +
      sectCell(u.es, earlyRanks[rid]) +
      sectCell(u.ms, midRanks[rid]) +
      sectCell(u.ls, lateRanks[rid]) +
      sectCell(u.ts, totalRanks[rid]) +
      distanceCell(u) +
      (showGoing ? goingCell(u) : '') +
      ratingCell(u.jrt, jryRanks[rid]) +
      ratingCell(u.trt, tryRanks[rid]) +
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
        th('tab', 'Tab') + th('horse', 'Horse') +
        th('jky', 'Jky') +
        th('trn', 'Trn') +
        th('bar', 'Bar') +
        th('tr', 'TR$') +
        th('trp', 'TR $') +
        th('fxd', 'Fxd') +
        th('score', 'Score') +
        th('settles', 'Settles') +
        th('early', 'Early') + th('mid', 'Mid') + th('late', 'Late') + th('total', 'Total') +
        (showGoing ? th('dist', 'Distance') + th('going', 'Going') : th('dist', 'Distance')) +
        th('jkypc', 'Jky Rt') +
        th('trnpc', 'Trn Rt') +
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
        const ascDefault = ['tab', 'horse', 'jky', 'trn', 'bar', 'tr',
                            'early', 'mid', 'late', 'total', 'settles', 'fxd', 'trp', 'score'];
        raceSortState.dir = ascDefault.includes(col) ? 'asc' : 'desc';
      }
      renderRaceDetail(raceId);
    });
  });
}

function paceZoneHtml(cls, lbl, hint, runners) {
  if (runners.length === 0) {
    return '<div class="pace-zone ' + cls + '">' +
      '<div class="zone-lbl"><span>' + lbl + ' ' + hint + '</span><span>0</span></div>' +
      '<div class="zone-tabs"><span style="color:var(--ink-faint);font-size:11px;">—</span></div>' +
      '</div>';
  }
  return '<div class="pace-zone ' + cls + '">' +
    '<div class="zone-lbl"><span>' + lbl + ' ' + hint + '</span><span>' + runners.length + '</span></div>' +
    '<div class="zone-tabs">' +
    runners.map(r => '<span class="zone-tab">' + (r.tab || '?') + '</span>').join('') +
    '</div></div>';
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
    const hasPick = !!((MODEL_PICKS[race.race_id] || {})[PRIMARY_KEY] || []).length;
    return '<div class="ntj-pill ' + (hasPick ? 'has-pick' : '') + '" data-rid="' + race.race_id + '">' +
      '<span class="ntj-pill-name">' + escapeHtml(race.venue) + ' R' + race.race + '</span>' +
      '<span class="ntj-pill-cd ' + cdCls + '">' + fmtCountdown(secsUntil) + '</span>' +
      '</div>';
  }).join('');
  pillsEl.querySelectorAll('.ntj-pill').forEach(p => {
    p.addEventListener('click', () => {
      // Navigate to race tab and open the race
      document.querySelectorAll('.tab').forEach(x => x.classList.remove('active'));
      document.querySelectorAll('.section').forEach(x => x.classList.remove('active'));
      document.querySelector('.tab[data-tab="race"]').classList.add('active');
      document.getElementById('sec-race').classList.add('active');
      currentRaceId = p.dataset.rid;
      showRaceDetail(currentRaceId);
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
  period: '7d',          // '7d' | '30d' | 'all' | 'custom'
  customFrom: null,      // ISO date string for custom range
  customTo: null,
  view: 'actual',        // 'actual' | 'theoretical'
  filterOnlyBet: false,  // when true, hides bets marked No
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
  const settled = allSettled.filter(s => withinPeriod(s.date));

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

  sortedForStats.forEach(s => {
    const entry = log[String(s.run_id)] || { placed: false, oddsTaken: null, comments: '', deadHeat: false };
    const hasOddsTaken = entry.oddsTaken != null && entry.oddsTaken > 1;

    // Stake source same as Today/settled-row logic
    const stakePrice = hasOddsTaken ? entry.oddsTaken : s.fxprice;
    if (!stakePrice || stakePrice <= 1) return;
    const stake = calcStake(stakePrice, { capExempt: hasOddsTaken });
    if (!stake) return;

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
  // Model metadata for chart baselines (expected ROI / WR lines on the dashed lines).
  // Reintroduced after stats rewrite removed earlier reference - cum-units chart and
  // rolling WR chart both still need this.
  const meta = MODEL_META[PRIMARY_KEY] || {};

  function statBlock(lbl, val, sub, cls) {
    return '<div class="pnl-stat">' +
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

  document.getElementById('pnl-stats-strip').innerHTML =
    statBlock('Bets', sortedForStats.length, pnlState.view === 'actual' ? 'placed' : 'all picks') +
    statBlock('P&amp;L', profitStr, profitDollarSub, profitCls) +
    statBlock('Win rate', wrStr, '') +
    statBlock('Place rate', prStr, '') +
    statBlock('ROI', roiStr, '', roiCls) +
    statBlock('Win streak', winStreakStr, winStreakSub, curWinStreak > 0 ? 'pos' : '') +
    statBlock('Loss streak', lossStreakStr, lossStreakSub, curLossStreak > 0 ? 'neg' : '');

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
    const maxV = Math.max(1, ...cumPoints.map(p => Math.max(p.cum, p.expected)));
    const minV = Math.min(0, ...cumPoints.map(p => Math.min(p.cum, p.expected)));
    const range = maxV - minV || 1;
    const xs = cumPoints.map((_, i) => pad + (cumPoints.length === 1 ? (W - 2*pad) / 2 : i * (W - 2*pad) / (cumPoints.length - 1)));
    const yScale = v => H - pad - ((v - minV) / range) * (H - 2*pad);
    const zeroY = yScale(0);
    let svgHtml = '<line class="axis" x1="' + pad + '" y1="' + zeroY + '" x2="' + (W-pad) + '" y2="' + zeroY + '" stroke-width="1"/>';
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
    const sigsTopHtml =
      sigPill('Score', r.crk) +
      sigPill('TR', s.tr_rank) +
      sigPill('Mid', s.mid_rank) +
      sigPill('Late', s.late_rank) +
      sigPill('Tot', s.total_rank);
    const formHtml = r.fm ?
      '<div class="pr-form" title="Last 4 finishes">' + escapeHtml(r.fm) + '</div>' : '';
    const sigsHtml = '<div class="pr-sigs-top">' + sigsTopHtml + '</div>' + formHtml;

    // Fxd display (read-only, same as Today)
    const fxdValStr = csvPrice != null ? csvPrice.toFixed(2) : '—';
    const fxdValCls = csvPrice != null ? 'v' : 'v empty';
    const oddsHtml =
      '<div class="pr-odds-display" title="Live fixed odds at last refresh">' +
        (csvPrice != null ? '<span class="cur">$</span>' : '') +
        '<span class="' + fxdValCls + '">' + fxdValStr + '</span>' +
      '</div>';

    // Stake display (units + dollars)
    const stakeWrapCls = 'pr-stake' + (usingFallback ? ' muted' : '');
    const returnWrapCls = 'pr-return' + (usingFallback ? ' muted' : '');
    let stakeHtml, returnHtml;
    if (stake) {
      stakeHtml = '<span class="units">' + stake.toFixed(2) + 'u</span>' +
        '<span class="ret">' + fmtDollar(stake) + '</span>';
      // Return for settled bets is the ACTUAL return: stake * settlePrice on a win,
      // 0 on a loss. Dead heat halving applies to the win return.
      const returnUnits = s.won ? (stake * settlePrice * dhMult) : 0;
      if (s.won) {
        returnHtml = '<span class="units">' + returnUnits.toFixed(2) + 'u</span>' +
          '<span class="ret">' + fmtDollar(returnUnits) + '</span>';
      } else {
        returnHtml = '<span class="units" style="color:var(--ink-faint);">0.00u</span>' +
          '<span class="ret" style="color:var(--ink-faint);">$0</span>';
      }
    } else {
      stakeHtml = '<span class="skip">—</span>';
      returnHtml = '<span class="skip">—</span>';
    }

    // Result chip - shows finish position with W/L tag (same as Today's hasOfficial branch)
    let resultHtml;
    if (s.finish != null) {
      resultHtml = '<span class="res-tag ' + (s.won ? 'win' : 'loss') + '">' +
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
    }

    // Meta line: distance · going · jky · trn (matches Today tab)
    const metaParts = [];
    if (s.distance) metaParts.push(s.distance + 'm');
    if (s.going) metaParts.push(escapeHtml(s.going));
    if (r.j || s.jockey) metaParts.push(escapeHtml(r.j || s.jockey));
    if (r.tn || s.trainer) metaParts.push(escapeHtml(r.tn || s.trainer));
    const metaLine = metaParts.join(' · ');

    const rowHtml =
      '<div class="pick-row ' + cardClass + (placed ? ' bet-placed' : '') +
        '" data-row-idx="' + idx + '" data-run-id="' + s.run_id + '" data-race-id="' + (s.race_id || '') + '">' +
        dateHtml +
        '<div class="pr-venue">' +
          '<div class="v-name">' + escapeHtml(s.venue || '') + '</div>' +
          '<div class="v-race">R' + s.race + '</div>' +
        '</div>' +
        '<div class="pr-runner">' +
          '<span class="tab-bdg">' + (s.tab || '?') + '</span>' +
          '<div class="rdetails">' +
            '<div class="rhorse">' + escapeHtml(s.horse || '') + '</div>' +
            '<div class="rmeta">' + metaLine + '</div>' +
          '</div>' +
        '</div>' +
        '<div class="pr-sigs">' + sigsHtml + '</div>' +
        '<div class="pr-odds">' + oddsHtml + '</div>' +
        '<div class="' + stakeWrapCls + '">' + stakeHtml + '</div>' +
        '<div class="' + returnWrapCls + '">' + returnHtml + '</div>' +
        '<div class="pr-result">' + resultHtml + '</div>' +
        '<div class="pr-bet">' + betHtml + '</div>' +
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

  const contextHtml = '<div class="pd-context">' +
    field('Form', r.fm) +
    field('Drift', driftStr) +
    field('Settles', settleStr) +
    field('Distance', s.distance ? s.distance + 'm' : null) +
    field('Going', s.going) +
    field('Distance perf', distPerf) +
    field('Going perf', goingPerf) +
    field('Jockey', r.j || s.jockey) +
    field('Trainer', r.tn || s.trainer) +
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

  return linkHtml +
    '<div class="pd-section"><div class="pd-section-title">Context</div>' + contextHtml + '</div>' +
    '<div class="pd-section"><div class="pd-section-title">Speed scores</div>' + speedHtml + '</div>' +
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
  // Filter checkbox
  const filterChk = document.getElementById('bh-filter-only-bet');
  if (filterChk) {
    filterChk.addEventListener('change', e => {
      pnlState.filterOnlyBet = e.target.checked;
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

// ── INSIGHTS tab rendering ─────────────────────────────────────────────────
function renderInsights() {
  const settled = SETTLED || [];
  const meta = MODEL_META[PRIMARY_KEY] || {};

  // ── Helper: build a perf-bar row showing wr + roi ──
  function perfBarRow(label, sub, group, maxBets) {
    if (!group || group.length === 0) {
      return '<div class="perf-bar"><div class="label">' + escapeHtml(label) +
        (sub ? '<span class="sub">' + escapeHtml(sub) + '</span>' : '') +
        '</div><div class="bar-track"></div><div class="wr">—</div><div class="roi neutral">no data</div></div>';
    }
    let wins = 0, stake = 0, ret = 0;
    group.forEach(s => {
      const st = calcStake(s.fxprice);
      if (!st) return;
      stake += st;
      const price = s.sp || s.top || s.fxprice;
      if (s.won) { wins++; ret += st * price; }
    });
    const wr = wins / group.length;
    const roi = stake > 0 ? (ret - stake) / stake : 0;
    const pct = (group.length / Math.max(1, maxBets)) * 100;
    const roiCls = roi > 0.02 ? 'pos' : (roi < -0.02 ? 'neg' : 'neutral');
    return '<div class="perf-bar">' +
      '<div class="label">' + escapeHtml(label) +
        '<span class="sub">' + group.length + ' bets</span>' +
      '</div>' +
      '<div class="bar-track"><div class="bar-fill" style="width:' + pct.toFixed(0) + '%;"></div></div>' +
      '<div class="wr">' + (wr * 100).toFixed(0) + '%</div>' +
      '<div class="roi ' + roiCls + '">' + (roi >= 0 ? '+' : '') + (roi * 100).toFixed(1) + '%</div>' +
      '</div>';
  }

  function emptyMsg(text) {
    return '<div class="empty-text">' + text + '</div>';
  }

  // ── 1. Distribution by price band ──
  const dp = document.getElementById('dist-price');
  if (dp) {
    const bands = [[0,3],[3,5],[5,8],[8,15],[15,1000]];
    const labels = ['Under $3','$3 to $5','$5 to $8','$8 to $15','$15 plus'];
    const counts = bands.map(() => 0);
    settled.forEach(s => {
      const p = s.fxprice;
      if (!p) return;
      for (let i = 0; i < bands.length; i++) {
        if (p >= bands[i][0] && p < bands[i][1]) { counts[i]++; break; }
      }
    });
    const max = Math.max(1, ...counts);
    let html = '';
    counts.forEach((c, i) => {
      const pct = (c / max * 100).toFixed(0);
      html += '<div class="dist-bar"><div class="label">' + labels[i] +
        '</div><div class="bar-track"><div class="bar-fill" style="width:' + pct + '%;"></div></div>' +
        '<div class="count">' + c + '</div></div>';
    });
    dp.innerHTML = settled.length > 0 ? html : emptyMsg('No settled bets yet.');
  }

  // ── 2. Distribution by venue (top 10) ──
  const dv = document.getElementById('dist-venue');
  if (dv) {
    const counts = {};
    settled.forEach(s => {
      const v = s.venue || 'Unknown';
      counts[v] = (counts[v] || 0) + 1;
    });
    const sorted = Object.entries(counts).sort((a, b) => b[1] - a[1]).slice(0, 10);
    const max = Math.max(1, ...sorted.map(e => e[1]));
    let html = '';
    sorted.forEach(([v, c]) => {
      const pct = (c / max * 100).toFixed(0);
      html += '<div class="dist-bar"><div class="label">' + escapeHtml(v) +
        '</div><div class="bar-track"><div class="bar-fill" style="width:' + pct + '%;"></div></div>' +
        '<div class="count">' + c + '</div></div>';
    });
    dv.innerHTML = settled.length > 0 ? html : emptyMsg('No settled bets yet.');
  }

  // ── 3. Performance by going ──
  const pg = document.getElementById('perf-going');
  if (pg) {
    function goingCategory(g) {
      if (!g) return null;
      const gl = g.toLowerCase();
      if (gl.startsWith('firm')) return 'Firm';
      if (gl.startsWith('good')) return 'Good';
      if (gl.startsWith('soft')) return 'Soft';
      if (gl.startsWith('heavy')) return 'Heavy';
      if (gl.startsWith('synth')) return 'Synth';
      return null;
    }
    const buckets = { 'Firm': [], 'Good': [], 'Soft': [], 'Heavy': [], 'Synth': [] };
    settled.forEach(s => {
      const cat = goingCategory(s.going);
      if (cat && buckets[cat]) buckets[cat].push(s);
    });
    const maxBets = Math.max(1, ...Object.values(buckets).map(b => b.length));
    let html = '';
    Object.keys(buckets).forEach(cat => {
      if (buckets[cat].length > 0) {
        html += perfBarRow(cat, '', buckets[cat], maxBets);
      }
    });
    pg.innerHTML = settled.length > 0 ? (html || emptyMsg('No going data on settled bets.')) : emptyMsg('No settled bets yet.');
  }

  // ── 4. Performance by signal strength (TR rank) ──
  const ps = document.getElementById('perf-signal');
  if (ps) {
    const bucketsTR = {
      'TR rank 1': [],
      'TR rank 2': [],
      'TR rank 3': [],
    };
    settled.forEach(s => {
      const tr = s.tr_rank;
      if (tr === 1) bucketsTR['TR rank 1'].push(s);
      else if (tr === 2) bucketsTR['TR rank 2'].push(s);
      else if (tr === 3) bucketsTR['TR rank 3'].push(s);
    });
    const maxBets = Math.max(1, ...Object.values(bucketsTR).map(b => b.length));
    let html = '';
    Object.keys(bucketsTR).forEach(lbl => {
      if (bucketsTR[lbl].length > 0) {
        html += perfBarRow(lbl, '', bucketsTR[lbl], maxBets);
      }
    });
    ps.innerHTML = settled.length > 0 ? (html || emptyMsg('No TR rank data on settled bets.')) : emptyMsg('No settled bets yet.');
  }

  // ── 5. Performance by day of week ──
  const pdw = document.getElementById('perf-dow');
  if (pdw) {
    const dows = ['Sunday','Monday','Tuesday','Wednesday','Thursday','Friday','Saturday'];
    const buckets = dows.map(() => []);
    settled.forEach(s => {
      if (!s.date) return;
      const d = new Date(s.date);
      if (isNaN(d.getTime())) return;
      buckets[d.getDay()].push(s);
    });
    const maxBets = Math.max(1, ...buckets.map(b => b.length));
    let html = '';
    dows.forEach((lbl, i) => {
      if (buckets[i].length > 0) {
        html += perfBarRow(lbl, '', buckets[i], maxBets);
      }
    });
    pdw.innerHTML = settled.length > 0 ? (html || emptyMsg('No date data on settled bets.')) : emptyMsg('No settled bets yet.');
  }
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
    version: 1,
    deviceTs: new Date().toISOString(),
    manualOdds: manualOdds,
    manualResults: manualResults,
    settings: settings,
  };
}

async function syncPush() {
  if (!syncCfg.pat || !syncCfg.gistId) { syncLog('Need both PAT and Gist ID.'); return; }
  syncLog('Pushing to Gist…');
  try {
    const payload = buildSyncPayload();
    await gistFetch('PATCH', '/gists/' + syncCfg.gistId, {
      files: { 'toprate_sync.json': { content: JSON.stringify(payload, null, 2) } },
    });
    syncLog('Pushed ' + Object.keys(payload.manualOdds).length + ' odds entries + settings.');
  } catch (e) {
    syncLog('Push failed: ' + e.message);
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
    if (payload.settings) {
      settings = Object.assign({}, defaultSettings, payload.settings);
      try { localStorage.setItem(STORAGE_KEY, JSON.stringify(settings)); } catch(e) {}
      // Re-hydrate UI
      document.getElementById('setting-unit').value = settings.unitDollar;
      document.getElementById('setting-target').value = settings.targetReturn;
      document.getElementById('setting-min').value = settings.minStake;
      document.getElementById('setting-max').value = settings.maxStake;
      document.getElementById('unit-display').textContent = '1u = $' + settings.unitDollar;
    }
    renderToday(); renderPnL(); renderInsights();
    syncLog('Pulled ' + Object.keys(manualOdds).length + ' odds entries + settings from ' +
            (payload.deviceTs ? new Date(payload.deviceTs).toLocaleString() : 'unknown time'));
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

// Auto-push debounced when manualOdds changes
let _syncPushTimer = null;
function scheduleSyncPush() {
  if (!syncCfg.pat || !syncCfg.gistId) return;  // not configured
  clearTimeout(_syncPushTimer);
  _syncPushTimer = setTimeout(syncPush, 4000);  // wait 4s for typing to settle
}

updateSyncUI();

// Auto-pull on page load if sync is configured
// (so opening the dashboard on iPhone after entering odds on computer just works)
if (syncCfg.pat && syncCfg.gistId) {
  syncPull().catch(() => {/* silent on auto-pull */});
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
