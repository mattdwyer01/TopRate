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

Stake rule: stake = round(4 / (price - 1), 2), min 0.25u, max 4u, "bet to return 4u"
Stake price source: fixed_win_price (current bookie price)
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
        settled_history.append({
            'date': r.get('date'),
            'venue': r.get('venue'),
            'race': r.get('race'),
            'horse': r.get('horse'),
            'run_id': r.get('run_id'),
            'fxprice': r.get('fixed_win_price'),
            'sp': r.get('starting_price_sp'),
            'top': r.get('price_top'),
            'finish': r.get('finish_position'),
            'won': bool(r.get('won')),
            'placed': bool(r.get('placed')),
            'tr_rank': r.get('tr_rank'),
            'mid_rank': r.get('mid_rank'),
            'late_rank': r.get('late_rank'),
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
    52px         /* time */
    140px        /* venue + race # */
    1fr          /* horse + meta */
    180px        /* signals strip */
    100px        /* odds */
    100px        /* stake */
    140px        /* result */
    24px;        /* expand chevron */
  gap: 14px;
  padding: 10px 14px;
  align-items: center;
  border-bottom: 1px solid var(--line-soft);
  cursor: pointer;
  transition: background 0.12s;
  position: relative;
  min-height: 48px;
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
.pr-odds-input {
  display: flex; align-items: baseline; gap: 2px;
  background: var(--line-soft); border: 1px solid var(--line);
  border-radius: 4px; padding: 4px 8px;
  transition: all 0.12s;
}
.pr-odds-input:focus-within {
  background: var(--panel); border-color: var(--emerald);
  box-shadow: 0 0 0 2px var(--emerald-bg);
}
.pr-odds-input.qualifies {
  background: var(--emerald-bg); border-color: var(--emerald-line);
}
.pr-odds-input.below {
  background: #fafafa; border-color: var(--line);
}
.pr-odds-input .cur {
  font-family: var(--font-body); font-size: 11px; color: var(--ink-mute);
  font-weight: 500;
}
.pr-odds-input input {
  font-family: var(--font-body); font-weight: 700; font-size: 14px;
  font-variant-numeric: tabular-nums;
  background: transparent; border: none; outline: none;
  width: 48px; text-align: right; color: var(--ink); padding: 0;
  -moz-appearance: textfield;
}
.pr-odds-input input::-webkit-outer-spin-button,
.pr-odds-input input::-webkit-inner-spin-button {
  -webkit-appearance: none; margin: 0;
}

.pr-stake {
  font-family: var(--font-body); text-align: right;
  font-variant-numeric: tabular-nums;
}
.pr-stake .units {
  font-weight: 700; font-size: 13px; color: var(--ink);
  display: block; line-height: 1.2;
}
.pr-stake .ret {
  font-weight: 500; font-size: 11px; color: var(--emerald-deep);
  margin-top: 2px;
}
.pr-stake .skip {
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

/* Speed scores in expanded view - 4 inline cells */
.pd-speed {
  display: grid; grid-template-columns: repeat(4, 1fr); gap: 8px;
}
.pd-speed-cell {
  background: var(--panel); border: 1px solid var(--line);
  border-radius: 6px; padding: 10px 12px;
  display: flex; align-items: baseline; justify-content: space-between; gap: 8px;
}
.pd-speed-cell .sp-lbl {
  font-family: var(--font-body); font-size: 10px; font-weight: 600;
  text-transform: uppercase; letter-spacing: 0.06em; color: var(--ink-mute);
}
.pd-speed-cell .sp-val {
  font-family: var(--font-body); font-weight: 700; font-size: 16px;
  color: var(--ink); letter-spacing: -0.01em;
  font-variant-numeric: tabular-nums;
}
.pd-speed-cell .sp-rk {
  font-family: var(--font-body); font-size: 10px; font-weight: 600;
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
    grid-template-columns: 1fr auto;
    grid-template-areas:
      'time   chev'
      'venue  venue'
      'runner runner'
      'sigs   sigs'
      'odds   stake'
      'result result';
    gap: 8px 12px;
    padding: 12px;
  }
  .pr-time { grid-area: time; }
  .pr-venue { grid-area: venue; flex-direction: row; gap: 8px; align-items: baseline; }
  .pr-venue .v-race { margin-top: 0; }
  .pr-runner { grid-area: runner; }
  .pr-sigs { grid-area: sigs; }
  .pr-odds { grid-area: odds; justify-content: flex-start; }
  .pr-stake { grid-area: stake; }
  .pr-result { grid-area: result; justify-content: flex-start; flex-wrap: wrap; }
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

/* Race context bar (between header and runners) */
.race-context-bar {
  background: var(--panel); border-left: 1px solid var(--line);
  border-right: 1px solid var(--line); padding: 12px 20px;
  display: flex; gap: 18px; flex-wrap: wrap;
  font-family: var(--font-mono); font-size: 12px;
}
.race-context-bar .ctx-item { color: var(--ink-mute); }
.race-context-bar .ctx-item .ctx-v {
  color: var(--ink); font-weight: 600; margin-left: 4px;
}

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
  font-family: var(--font-mono); font-size: 9px;
  text-transform: uppercase; letter-spacing: 0.08em;
  color: var(--ink-mute); margin-bottom: 6px;
  display: flex; justify-content: space-between;
}
.pace-zone .zone-tabs {
  display: flex; flex-wrap: wrap; gap: 4px;
}
.pace-zone .zone-tab {
  display: inline-block; min-width: 22px; height: 22px; line-height: 22px;
  text-align: center; background: var(--panel); color: var(--ink);
  font-family: var(--font-mono); font-size: 11px; font-weight: 500;
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
  font-family: var(--font-display); font-weight: 700; font-size: 18px;
  letter-spacing: -0.01em;
}
.race-header .race-meta-line {
  font-family: var(--font-mono); font-size: 11px; color: #a8a29e;
  margin-top: 4px;
}
.race-header-stats {
  display: flex; gap: 24px;
  font-family: var(--font-mono); font-size: 11px;
}
.race-header-stats .item { color: #a8a29e; }
.race-header-stats .item .v { color: #fafaf9; font-weight: 600; }

.race-table-wrap { overflow-x: auto; }
.race-table {
  width: 100%; border-collapse: collapse;
  font-family: var(--font-mono); font-size: 12px;
}
.race-table thead th {
  background: var(--line-soft); border-bottom: 1px solid var(--line);
  text-align: left; padding: 10px 12px;
  font-family: var(--font-mono); font-size: 10px; font-weight: 600;
  text-transform: uppercase; letter-spacing: 0.06em; color: var(--ink-mute);
  cursor: pointer; user-select: none; white-space: nowrap;
}
.race-table thead th:hover { background: #ede9e1; }
.race-table thead th.sort-asc::after { content: ' ↑'; color: var(--emerald); }
.race-table thead th.sort-desc::after { content: ' ↓'; color: var(--emerald); }
.race-table tbody td {
  padding: 9px 12px; border-bottom: 1px solid var(--line-soft);
  white-space: nowrap;
}
.race-table tbody tr:hover { background: var(--line-soft); }
.race-table tbody tr.is-pick {
  background: var(--emerald-bg);
}
.race-table tbody tr.is-pick:hover { background: #d1fae5; }
.race-table tbody tr.muted { color: var(--ink-faint); }
.tn-cell {
  display: inline-block; min-width: 22px; height: 22px; line-height: 22px;
  text-align: center; background: var(--ink); color: var(--panel);
  font-weight: 600; border-radius: 4px; padding: 0 6px;
  font-size: 11px;
}
.horse-cell { font-weight: 600; color: var(--ink); }
.is-pick .horse-cell { color: var(--emerald-deep); }

.rank-cell { font-weight: 600; color: var(--ink-soft); }
.rank-cell.r1 { color: var(--emerald); font-weight: 700; }
.rank-cell.r2 { color: var(--emerald-deep); font-weight: 600; }
.rank-cell.r3 { color: var(--ink-soft); }

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

.drift-cell.firmed { color: var(--emerald-deep); }
.drift-cell.drifted { color: var(--rose); }

.edge-cell.value { color: var(--emerald-deep); font-weight: 600; }
.edge-cell.under { color: var(--rose); }

.model-badge {
  display: inline-block; padding: 2px 7px;
  background: var(--emerald); color: var(--panel);
  border-radius: 4px; font-size: 10px; font-weight: 700;
  letter-spacing: 0.04em; text-transform: uppercase;
}

/* PNL tab */
.pnl-grid {
  display: grid; grid-template-columns: 2fr 1fr; gap: 18px;
  margin-bottom: 18px;
}
@media (max-width: 900px) { .pnl-grid { grid-template-columns: 1fr; } }

.pnl-chart-card {
  background: var(--panel); border: 1px solid var(--line);
  border-radius: var(--radius-lg); padding: 18px 22px;
}
.pnl-chart-card h3, .pnl-health h3 {
  font-family: var(--font-display); font-weight: 700; font-size: 14px;
  margin-bottom: 14px; color: var(--ink); letter-spacing: -0.01em;
}
.pnl-chart-svg { width: 100%; height: 200px; }
.pnl-chart-svg .axis { stroke: var(--line); }
.pnl-chart-svg .grid { stroke: var(--line-soft); stroke-dasharray: 2,3; }
.pnl-chart-svg .actual { fill: none; stroke: var(--emerald); stroke-width: 2; }
.pnl-chart-svg .expected { fill: none; stroke: var(--ink-faint); stroke-width: 1.5; stroke-dasharray: 4,3; }
.pnl-chart-svg .axis-text {
  fill: var(--ink-mute); font-family: var(--font-mono); font-size: 9px;
}

.pnl-health {
  background: var(--panel); border: 1px solid var(--line);
  border-radius: var(--radius-lg); padding: 18px 22px;
}
.health-row {
  display: grid; grid-template-columns: auto 1fr auto;
  gap: 12px; align-items: baseline;
  padding: 10px 0; border-bottom: 1px solid var(--line-soft);
  font-family: var(--font-mono); font-size: 12px;
}
.health-row:last-child { border-bottom: none; }
.health-row .lbl {
  font-size: 10px; text-transform: uppercase; letter-spacing: 0.06em;
  color: var(--ink-mute);
}
.health-row .v { font-weight: 600; color: var(--ink); }
.health-row .delta { font-size: 10px; color: var(--ink-mute); text-align: right; }
.health-row .delta.pos { color: var(--emerald-deep); }
.health-row .delta.neg { color: var(--rose); }

.bet-history {
  background: var(--panel); border: 1px solid var(--line);
  border-radius: var(--radius-lg); overflow: hidden;
}
.bet-history h3 {
  font-family: var(--font-display); font-weight: 700; font-size: 14px;
  padding: 16px 22px; border-bottom: 1px solid var(--line);
  color: var(--ink); letter-spacing: -0.01em;
}
.bet-history-table-wrap { overflow-x: auto; }
.bet-history table {
  width: 100%; border-collapse: collapse;
  font-family: var(--font-mono); font-size: 12px;
}
.bet-history thead th {
  background: var(--line-soft); padding: 10px 14px;
  font-size: 10px; text-transform: uppercase; letter-spacing: 0.06em;
  font-weight: 600; color: var(--ink-mute); text-align: left;
  border-bottom: 1px solid var(--line);
  cursor: pointer; user-select: none;
}
.bet-history thead th:hover { background: #ede9e1; }
.bet-history tbody td {
  padding: 9px 14px; border-bottom: 1px solid var(--line-soft);
  white-space: nowrap;
}
.bet-history tr.win { background: linear-gradient(to right, rgba(16,185,129,0.04), transparent 50%); }
.bet-history tr.win .pl { color: var(--emerald-deep); font-weight: 600; }
.bet-history tr.loss .pl { color: var(--rose); }

/* Insights tab */
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
  font-family: var(--font-display); font-weight: 700; font-size: 14px;
  margin-bottom: 12px; color: var(--ink);
}
.insight-card .desc {
  font-family: var(--font-mono); font-size: 11px;
  color: var(--ink-mute); margin-bottom: 16px; line-height: 1.5;
}

.model-compare {
  display: grid; grid-template-columns: auto 1fr auto auto auto;
  gap: 8px 14px; align-items: baseline;
  font-family: var(--font-mono); font-size: 11px;
  padding: 10px 0; border-bottom: 1px solid var(--line-soft);
}
.model-compare:last-child { border-bottom: none; }
.model-compare .name {
  font-weight: 600; color: var(--ink); font-size: 12px;
}
.model-compare .name.primary {
  color: var(--emerald-deep);
}
.model-compare .name .tag {
  display: inline-block; padding: 1px 5px; margin-left: 6px;
  background: var(--emerald-bg); color: var(--emerald-deep);
  font-size: 9px; border-radius: 3px; letter-spacing: 0.05em;
  text-transform: uppercase; vertical-align: 1px;
}
.model-compare .desc-mini { color: var(--ink-mute); font-size: 10px; }
.model-compare .stat {
  text-align: right; color: var(--ink-soft);
}
.model-compare .stat .lbl {
  font-size: 9px; text-transform: uppercase; letter-spacing: 0.06em;
  color: var(--ink-mute); display: block;
}

.dist-bars { display: flex; flex-direction: column; gap: 8px; }
.dist-bar {
  display: grid; grid-template-columns: 80px 1fr auto;
  gap: 10px; align-items: center;
  font-family: var(--font-mono); font-size: 11px;
}
.dist-bar .label { color: var(--ink-soft); }
.dist-bar .bar-track {
  height: 6px; background: var(--line-soft); border-radius: 3px;
  overflow: hidden;
}
.dist-bar .bar-fill {
  height: 100%; background: var(--emerald); border-radius: 3px;
}
.dist-bar .count { color: var(--ink-mute); font-size: 10px; min-width: 30px; text-align: right; }

/* Settings tab */
.settings-card {
  background: var(--panel); border: 1px solid var(--line);
  border-radius: var(--radius-lg); padding: 22px 26px;
  max-width: 560px;
}
.settings-card h3 {
  font-family: var(--font-display); font-weight: 700; font-size: 16px;
  margin-bottom: 18px; color: var(--ink);
}
.setting-row {
  display: flex; align-items: center; justify-content: space-between;
  padding: 14px 0; border-top: 1px solid var(--line-soft);
}
.setting-row:first-of-type { border-top: none; }
.setting-row .lbl {
  font-family: var(--font-display); font-weight: 600; font-size: 13px;
  color: var(--ink);
}
.setting-row .desc {
  font-family: var(--font-mono); font-size: 11px; color: var(--ink-mute);
  margin-top: 2px;
}
.setting-input {
  font-family: var(--font-mono); font-size: 13px;
  background: var(--panel); border: 1px solid var(--line);
  border-radius: var(--radius-sm); padding: 6px 10px;
  width: 100px; text-align: right; color: var(--ink);
}
.setting-input.wide {
  width: 240px; text-align: left; font-size: 11px;
}
.setting-input:focus {
  outline: none; border-color: var(--emerald); box-shadow: 0 0 0 3px var(--emerald-bg);
}

.btn {
  font-family: var(--font-body); font-weight: 500; font-size: 12px;
  background: var(--panel); color: var(--ink-soft);
  border: 1px solid var(--line); border-radius: var(--radius-sm);
  padding: 7px 14px; cursor: pointer; transition: all 0.15s;
  text-decoration: none; display: inline-block; line-height: 1.2;
}
.btn:hover { background: var(--line-soft); color: var(--ink); border-color: #d6d3d1; }
.btn-primary {
  background: var(--ink); color: var(--panel); border-color: var(--ink);
}
.btn-primary:hover { background: var(--ink-soft); color: var(--panel); border-color: var(--ink-soft); }

.state-pill {
  display: inline-block; padding: 3px 10px; border-radius: 999px;
  font-family: var(--font-mono); font-size: 10px; font-weight: 600;
  letter-spacing: 0.05em; text-transform: uppercase;
}
.state-pill.state-on  { background: var(--emerald-bg); color: var(--emerald-deep); }
.state-pill.state-off { background: var(--line-soft); color: var(--ink-mute); }
.state-pill.state-err { background: var(--rose-bg); color: var(--rose); }

.sync-log {
  font-family: var(--font-mono); font-size: 10px; color: var(--ink-mute);
  background: var(--line-soft); border-radius: var(--radius-sm);
  padding: 8px 12px; margin-top: 12px; min-height: 36px;
  white-space: pre-wrap; max-height: 180px; overflow-y: auto;
}
.sync-log:empty::before {
  content: 'sync log appears here'; color: var(--ink-faint);
}

.fetch-status {
  font-family: var(--font-mono); font-size: 11px; color: var(--ink-mute);
}
.fetch-status.ok  { color: var(--emerald-deep); }
.fetch-status.err { color: var(--rose); }

/* Stale-data banner */
.stale-banner {
  background: var(--amber-bg); border: 1px solid var(--amber-line);
  border-radius: var(--radius-md); padding: 10px 16px; margin-bottom: 14px;
  display: flex; align-items: center; justify-content: space-between;
  font-family: var(--font-mono); font-size: 11px; color: var(--amber);
}
.stale-banner .msg { font-weight: 500; }
.stale-banner .btn-stale {
  background: var(--amber); color: var(--panel); border-color: var(--amber);
}
.stale-banner .btn-stale:hover { background: #b45309; }

/* Mobile adjustments */
@media (max-width: 720px) {
  .topbar { padding: 12px 0; margin-bottom: 14px; }
  .brand { font-size: 17px; }
  .tabs { overflow-x: auto; -webkit-overflow-scrolling: touch; }
  .tab { padding: 10px 12px; font-size: 11px; flex-shrink: 0; }
  .hero { padding: 14px 16px; }
  .hero-title { font-size: 16px; }
  .hero-stat .val { font-size: 18px; }
  .race-table { font-size: 11px; }
  .race-table thead th, .race-table tbody td { padding: 8px 8px; }
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

  <div id="stale-host"></div>

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
          <div class="lbl">Today's picks</div>
          <div class="val" id="hs-today-count">{n_today}</div>
          <div class="sub" id="hs-today-pending">all pending</div>
        </div>
        <div class="hero-stat">
          <div class="lbl">Today P&amp;L</div>
          <div class="val" id="hs-today-pnl">&mdash;</div>
          <div class="sub" id="hs-today-pnl-units">&mdash;</div>
        </div>
        <div class="hero-stat">
          <div class="lbl">30d ROI@SP</div>
          <div class="val" id="hs-30d-roi-sp">&mdash;</div>
          <div class="sub">expected {primary_roi_sp}%</div>
        </div>
        <div class="hero-stat">
          <div class="lbl">30d Win rate</div>
          <div class="val" id="hs-30d-wr">&mdash;</div>
          <div class="sub">expected {primary_wr}%</div>
        </div>
      </div>
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
      <div class="race-detail">
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
    <div class="pnl-grid">
      <div class="pnl-chart-card">
        <h3>Cumulative units</h3>
        <svg class="pnl-chart-svg" id="pnl-chart" viewBox="0 0 600 200" preserveAspectRatio="none">
          <!-- populated by JS -->
        </svg>
        <div style="display:flex;gap:24px;margin-top:10px;font-family:var(--font-mono);font-size:11px;color:var(--ink-mute);">
          <div><span style="display:inline-block;width:14px;height:2px;background:var(--emerald);vertical-align:middle;margin-right:6px;"></span>Actual</div>
          <div><span style="display:inline-block;width:14px;height:1.5px;background:var(--ink-faint);vertical-align:middle;margin-right:6px;border-top:1.5px dashed var(--ink-faint);"></span>Expected (model)</div>
        </div>
      </div>
      <div class="pnl-health">
        <h3>Model health</h3>
        <div id="health-rows">
          <!-- populated by JS -->
        </div>
        <div style="margin-top:14px;font-family:var(--font-mono);font-size:10px;color:var(--ink-mute);line-height:1.5;">
          Realised vs expected over <span id="health-sample">0</span> settled bets. Model expected: WR {primary_wr}%, ROI@SP {primary_roi_sp}%, ROI@Top {primary_roi_top}%.
        </div>
      </div>
    </div>

    <div class="bet-history">
      <h3>Settled bets &middot; <span id="bh-count">0</span></h3>
      <div class="bet-history-table-wrap">
        <table id="bh-table">
          <thead>
            <tr>
              <th data-sort="date">Date</th>
              <th data-sort="venue">Venue</th>
              <th data-sort="race">R</th>
              <th data-sort="horse">Horse</th>
              <th data-sort="fxprice">Fxd $</th>
              <th data-sort="sp">SP</th>
              <th data-sort="top">Top $</th>
              <th data-sort="finish">Pos</th>
              <th data-sort="result">Result</th>
              <th data-sort="pl">P&amp;L (u)</th>
            </tr>
          </thead>
          <tbody id="bh-body"></tbody>
        </table>
      </div>
    </div>
  </section>

  <!-- INSIGHTS -->
  <section class="section" id="sec-insights">
    <div class="insights-grid">
      <div class="insight-card">
        <h3>Model comparison &middot; primary vs reference</h3>
        <div class="desc">Realised performance across the three v3 models being tracked. Primary is the only one being bet; references give context for whether the chosen model is performing as expected.</div>
        <div id="model-compare"></div>
      </div>

      <div class="insight-card">
        <h3>Bets by price band</h3>
        <div class="desc">Distribution of primary model picks by fixed-win price. Higher buckets carry more variance but also more upside.</div>
        <div class="dist-bars" id="dist-price"></div>
      </div>

      <div class="insight-card">
        <h3>Bets by venue</h3>
        <div class="desc">Where the model finds qualifying bets most often.</div>
        <div class="dist-bars" id="dist-venue"></div>
      </div>

      <div class="insight-card">
        <h3>Rolling 14-day strike rate</h3>
        <div class="desc">14-day rolling win rate vs expected ({primary_wr}%). Persistent gaps over 50+ bets warrant review.</div>
        <svg class="pnl-chart-svg" id="rolling-wr" viewBox="0 0 600 200" preserveAspectRatio="none"></svg>
      </div>
    </div>
  </section>

  <!-- SETTINGS -->
  <section class="section" id="sec-settings">

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
          <div class="desc">Format: <code>owner/name</code> — case sensitive. Used to dispatch workflows.</div>
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
          <div class="desc" id="sync-status">Not configured. Add a GitHub token and Gist ID below to sync manual odds and settings between iPhone and computer.</div>
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
      <div class="setting-row" style="display:flex;gap:10px;justify-content:flex-end;border-top:none;">
        <button class="btn" id="btn-sync-create">Create new Gist</button>
        <button class="btn" id="btn-sync-test">Test sync</button>
        <button class="btn btn-primary" id="btn-sync-pull">Pull from Gist</button>
        <button class="btn btn-primary" id="btn-sync-push">Push to Gist</button>
      </div>
      <div id="sync-log" class="sync-log"></div>
    </div>

    <!-- Stake preferences -->
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
          <div class="desc">Target return per bet in units. Stake = target / (price &minus; 1).</div>
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

    <!-- About -->
    <div class="settings-card">
      <h3>About</h3>
      <div style="font-family:var(--font-mono);font-size:11px;color:var(--ink-soft);line-height:1.7;">
        <p style="margin-bottom:8px;"><strong>Primary model:</strong> {primary_label} &mdash; {primary_desc}</p>
        <p style="margin-bottom:8px;"><strong>Walk-forward verified:</strong> Train ROI +24%, Test ROI +37% on Apr 9 - May 7 2026 sample.</p>
        <p style="margin-bottom:8px;"><strong>Expected:</strong> {primary_wr}% strike rate, {primary_roi_sp}% ROI@SP, {primary_roi_top}% ROI@Top.</p>
        <p style="margin-bottom:8px;"><strong>Pick volume:</strong> ~{primary_per_day}/day average.</p>
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
_JS_APP = """
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
function calcStake(price) {
  if (!price || price <= 1) return null;
  const raw = settings.targetReturn / (price - 1);
  const clamped = Math.min(settings.maxStake, Math.max(settings.minStake, raw));
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

// ── Manual fixed odds entry ────────────────────────────────────────────────
// Per-pick odds storage: {run_id: {odds: number, ts: ISO timestamp}}
// Persisted to localStorage and (if sync enabled) to a sync backend.
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

function saveOdds() {
  try { localStorage.setItem(ODDS_STORAGE_KEY, JSON.stringify(manualOdds)); } catch(e) {}
  if (typeof scheduleSyncPush === 'function') scheduleSyncPush();
}
function saveResults() {
  try { localStorage.setItem(RESULTS_STORAGE_KEY, JSON.stringify(manualResults)); } catch(e) {}
  if (typeof scheduleSyncPush === 'function') scheduleSyncPush();
}

function getEffectiveOdds(runId, fallback) {
  // If user has typed a value, use that. Otherwise use the CSV's fixed_win_price.
  const m = manualOdds[String(runId)];
  if (m && m.odds != null) return m.odds;
  return fallback != null ? fallback : null;
}

function setManualOdds(runId, value) {
  if (value == null || isNaN(value) || value <= 1) {
    delete manualOdds[String(runId)];
  } else {
    manualOdds[String(runId)] = { odds: parseFloat(value), ts: new Date().toISOString() };
  }
  saveOdds();
}

function resetManualOdds(runId) {
  delete manualOdds[String(runId)];
  saveOdds();
  renderToday();
}

// ── TODAY tab rendering ────────────────────────────────────────────────────
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

  // Filter to user's local today
  const localToday = isoDate(0);
  const todaysPicks = (PICKS_TODAY || []).filter(p => p.date === localToday);

  if (todaysPicks.length === 0) {
    const dates = [...new Set((PICKS_TODAY || []).map(p => p.date).filter(Boolean))];
    let hint = '';
    if (dates.length > 0) {
      hint = '<div class="sub" style="margin-top:12px;">Picks available for: ' +
        dates.slice(-3).join(', ') + '. Browse via the Race tab to see those days.</div>';
    }
    list.innerHTML = '<div class="empty-state"><div class="head">No picks for ' + localToday + '</div>' +
      '<div class="sub">The model did not find any qualifying runners today, or the data has not been refreshed yet.</div>' + hint + '</div>';
    return;
  }

  const minOdds = (MODEL_META[PRIMARY_KEY] && MODEL_META[PRIMARY_KEY].min_odds) || 3.0;

  // Sort by start time
  todaysPicks.sort((a, b) => (a.start_time || '').localeCompare(b.start_time || ''));

  let todayWins = 0, todayLosses = 0, todayPnL = 0, todaySettled = 0, todayQualifying = 0;
  const now = new Date();

  todaysPicks.forEach((p, idx) => {
    const r = p.runner_full || {};
    const csvPrice = p.fxprice;
    const effectivePrice = getEffectiveOdds(p.run_id, csvPrice);
    const isManualOverride = manualOdds[String(p.run_id)] != null;
    const meetsThreshold = effectivePrice != null && effectivePrice >= minOdds;
    const stake = meetsThreshold ? calcStake(effectivePrice) : null;
    if (meetsThreshold) todayQualifying++;

    // Result state
    const manRes = manualResults[String(p.run_id)];
    const officialFinish = r.f;
    const hasOfficial = officialFinish != null;
    const isSettled = hasOfficial || (manRes != null);
    const displayWon = hasOfficial ? (officialFinish === 1) : (manRes ? manRes.finish === 1 : false);

    // Update settled counters
    let cardClass = 'pending';
    if (isSettled) {
      todaySettled++;
      if (meetsThreshold && stake) {
        const settlePrice = r.sp || effectivePrice;
        if (displayWon) {
          todayWins++;
          todayPnL += stake * (settlePrice - 1);
          cardClass = 'settled-win';
        } else {
          todayLosses++;
          todayPnL -= stake;
          cardClass = 'settled-loss';
        }
      } else {
        cardClass = 'below-threshold';
      }
    } else if (!meetsThreshold) {
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

    // Signal pills - TR / Mid / Late / Total + form string underneath
    function sigPill(label, rank) {
      if (rank == null) return '<span class="sig"><span class="lbl">' + label + '</span><span class="v">—</span></span>';
      const cls = rank === 1 ? 'r1' : (rank === 2 ? 'r2' : (rank === 3 ? 'r3' : ''));
      return '<span class="sig ' + cls + '"><span class="lbl">' + label + '</span><span class="v">' + rank + '</span></span>';
    }
    const sigsTopHtml =
      sigPill('TR', p.tr_rank) +
      sigPill('Mid', p.mid_rank) +
      sigPill('Late', p.late_rank) +
      sigPill('Tot', p.total_rank);
    // Form string row underneath: "3-1-7-2"
    const formHtml = r.fm ?
      '<div class="pr-form" title="Last 4 finishes">' + escapeHtml(r.fm) + '</div>' : '';
    const sigsHtml = '<div class="pr-sigs-top">' + sigsTopHtml + '</div>' + formHtml;

    // Odds input
    const oddsCls = meetsThreshold ? 'qualifies' : 'below';
    const oddsValue = effectivePrice != null ? effectivePrice.toFixed(2) : '';
    const oddsHtml =
      '<div class="pr-odds-input ' + oddsCls + '" onclick="event.stopPropagation();">' +
        '<span class="cur">$</span>' +
        '<input type="number" step="0.05" min="1" data-rid="' + p.run_id + '" ' +
        'value="' + oddsValue + '" placeholder="' + (csvPrice ? csvPrice.toFixed(2) : '?') + '">' +
      '</div>';

    // Stake display
    let stakeHtml;
    if (meetsThreshold && stake) {
      const ret = stake * effectivePrice;
      stakeHtml = '<span class="units">' + stake.toFixed(2) + 'u</span>' +
        '<span class="ret">→ ' + fmtDollar(ret) + '</span>';
    } else if (!meetsThreshold) {
      stakeHtml = '<span class="skip">no bet</span>';
    } else {
      stakeHtml = '<span class="skip">enter odds</span>';
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

    // Build the row
    const row = document.createElement('div');
    row.className = 'pick-row ' + cardClass;
    row.dataset.idx = idx;

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
      '<div class="pr-stake">' + stakeHtml + '</div>' +
      '<div class="pr-result">' + resultHtml + '</div>' +
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
      if (e.target.closest('.pr-odds-input, .pr-result button, .res-clear')) return;
      const isExpanded = row.classList.toggle('expanded');
      detail.classList.toggle('show', isExpanded);
    });
  });

  // Wire odds input handlers (event delegation)
  list.querySelectorAll('.pr-odds-input input').forEach(el => {
    el.addEventListener('change', e => {
      const rid = e.target.dataset.rid;
      const v = e.target.value === '' ? null : parseFloat(e.target.value);
      setManualOdds(rid, v);
      renderToday();
    });
    el.addEventListener('click', e => e.stopPropagation());
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

  // Update hero strip
  document.getElementById('hs-today-count').textContent = todaysPicks.length;
  const subEl = document.getElementById('hs-today-pending');
  if (todaySettled === 0) {
    subEl.textContent = todayQualifying + ' over $' + minOdds + ' · ' + (todaysPicks.length - todayQualifying) + ' below';
  } else {
    subEl.textContent = todaySettled + ' settled · ' + (todaysPicks.length - todaySettled) + ' pending';
  }

  const pnlEl = document.getElementById('hs-today-pnl');
  if (todaySettled > 0) {
    pnlEl.textContent = (todayPnL >= 0 ? '+' : '') + todayPnL.toFixed(2) + 'u';
    pnlEl.classList.toggle('pos', todayPnL > 0);
    pnlEl.classList.toggle('neg', todayPnL < 0);
    document.getElementById('hs-today-pnl-units').textContent =
      (todayPnL >= 0 ? '+' : '') + fmtDollar(todayPnL) + ' · ' + todayWins + 'W ' + todayLosses + 'L';
  } else {
    pnlEl.textContent = '—';
    pnlEl.className = 'val';
    document.getElementById('hs-today-pnl-units').textContent = 'no settled bets';
  }

  // 30d stats
  const cutoff30 = new Date(now); cutoff30.setDate(cutoff30.getDate() - 30);
  const last30 = (SETTLED || []).filter(s => s.date && new Date(s.date) >= cutoff30);
  if (last30.length > 0) {
    let wins = 0, totalSpStake = 0, spReturn = 0, betsTaken = 0;
    last30.forEach(s => {
      const effective = getEffectiveOdds(s.run_id, s.fxprice);
      if (effective == null || effective < minOdds) return;
      const stake = calcStake(effective);
      if (!stake) return;
      betsTaken++;
      const sp = s.sp || effective;
      if (s.won) { wins++; spReturn += stake * sp; }
      totalSpStake += stake;
    });
    if (betsTaken > 0) {
      const wr = wins / betsTaken;
      const roi = totalSpStake > 0 ? (spReturn - totalSpStake) / totalSpStake : 0;
      document.getElementById('hs-30d-wr').textContent = (wr * 100).toFixed(1) + '%';
      const roiEl = document.getElementById('hs-30d-roi-sp');
      roiEl.textContent = (roi >= 0 ? '+' : '') + (roi * 100).toFixed(1) + '%';
      roiEl.classList.toggle('pos', roi > 0);
      roiEl.classList.toggle('neg', roi < 0);
    }
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

  return '<div class="pd-section"><div class="pd-section-title">Speed scores</div>' + speedHtml + '</div>' +
         '<div class="pd-section"><div class="pd-section-title">Context</div>' + contextHtml + '</div>';
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
  renderRaceDetail(raceId);
}

function exitRaceDetail() {
  document.getElementById('race-browser').style.display = 'block';
  document.getElementById('race-detail').style.display = 'none';
  currentRaceId = null;
}

function renderRaceDetail(raceId) {
  const race = RACES.find(r => String(r.race_id) === String(raceId));
  if (!race) {
    document.getElementById('rd-title').textContent = 'Race not found';
    return;
  }
  const picks = (MODEL_PICKS[raceId] || {})[PRIMARY_KEY] || [];
  const pickIds = new Set(picks.map(p => String(p.run_id)));
  const runners = race.runners || [];

  // Header
  document.getElementById('rd-title').textContent = race.venue + ' · R' + race.race;
  document.getElementById('rd-subtitle').textContent = race.race_name || '';
  document.getElementById('rd-header-stats').innerHTML =
    '<div class="item">' + fmtTime(race.start_time) + '</div>' +
    '<div class="item">' + race.distance + 'm</div>' +
    '<div class="item">' + escapeHtml(race.going || '') + '</div>' +
    '<div class="item">$' + (race.prize/1000).toFixed(0) + 'k</div>' +
    '<div class="item">' + runners.length + ' runners</div>' +
    '<div class="item"><span class="v">' + picks.length + '</span> model pick' + (picks.length !== 1 ? 's' : '') + '</div>';

  // Context bar - show track grading, rail, race shape
  const ctx = [];
  if (race.race_name) ctx.push({ lbl: '', v: race.race_name });
  ctx.push({ lbl: 'Distance', v: race.distance + 'm' });
  ctx.push({ lbl: 'Going', v: race.going || '—' });
  ctx.push({ lbl: 'Prize', v: '$' + (race.prize / 1000).toFixed(0) + 'k' });
  ctx.push({ lbl: 'Field', v: runners.length });
  document.getElementById('rd-context-bar').innerHTML =
    ctx.filter(c => c.lbl).map(c =>
      '<div class="ctx-item">' + c.lbl + '<span class="ctx-v">' + escapeHtml(String(c.v)) + '</span></div>'
    ).join('');

  // Pace map - group runners by avg_settled position
  // Use avg_settled_pos relative to field size (need to fetch from runner data)
  // For simplicity, group by quartile of avg_settled if available
  // Settling categories: leaders (1-2), on-pace (3-4), midfield (5-8), back (9+)
  const settled = { leaders: [], onpace: [], midfield: [], back: [] };
  runners.forEach(u => {
    const pos = u.asp; // avg_settled_pos
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

  // Runners table
  function computeRanks(runners, getter, ascending) {
    const valid = runners.filter(r => getter(r) != null);
    valid.sort((a, b) => ascending ? getter(a) - getter(b) : getter(b) - getter(a));
    const ranks = {};
    valid.forEach((r, i) => { ranks[r.rid] = i + 1; });
    return ranks;
  }
  const trRanks = computeRanks(runners, r => r.trr, false);
  const midRanks = computeRanks(runners, r => r.ms, false);
  const lateRanks = computeRanks(runners, r => r.ls, false);
  const totalRanks = computeRanks(runners, r => r.ts, false);

  function rankPill(rank) {
    if (rank == null) return '<span class="sect-pill other">—</span>';
    if (rank === 1) return '<span class="sect-pill top1">' + rank + '</span>';
    if (rank === 2) return '<span class="sect-pill top2">' + rank + '</span>';
    return '<span class="sect-pill other">' + rank + '</span>';
  }

  // Sort: pick runners first, then by tr_rank
  const sortedRunners = runners.slice().sort((a, b) => {
    const aPick = pickIds.has(String(a.rid)) ? 0 : 1;
    const bPick = pickIds.has(String(b.rid)) ? 0 : 1;
    if (aPick !== bPick) return aPick - bPick;
    return (trRanks[a.rid] || 99) - (trRanks[b.rid] || 99);
  });

  let rowsHtml = '';
  sortedRunners.forEach(u => {
    const rid = u.rid;
    const isPick = pickIds.has(String(rid));
    const trR = trRanks[rid];
    const midR = midRanks[rid];
    const lateR = lateRanks[rid];
    const totR = totalRanks[rid];
    const trClass = trR === 1 ? 'r1' : (trR === 2 ? 'r2' : (trR === 3 ? 'r3' : ''));
    const wt = u.wtr;
    const wtClass = wt > 0 ? 'up' : (wt < 0 ? 'down' : '');
    const wd = u.wad;
    const wdClass = wd && wd > 0 ? 'has-win' : '';
    const fxp = u.fx;
    const trp = u.trp;
    const edge = (trp && fxp) ? (fxp / trp).toFixed(2) : null;
    const edgeClass = edge != null ? (parseFloat(edge) > 1.05 ? 'value' : (parseFloat(edge) < 0.95 ? 'under' : '')) : '';
    rowsHtml += '<tr class="' + (isPick ? 'is-pick' : (trR > 5 ? 'muted' : '')) + '">' +
      '<td><span class="tn-cell">' + (u.tab || '?') + '</span></td>' +
      '<td class="horse-cell">' + escapeHtml(u.h || '') + '</td>' +
      '<td>' + escapeHtml(u.j || '') + '</td>' +
      '<td>' + escapeHtml(u.tn || '') + '</td>' +
      '<td>' + (u.b || '') + '</td>' +
      '<td class="rank-cell ' + trClass + '">' + (trR || '—') + '</td>' +
      '<td>' + rankPill(midR) + '</td>' +
      '<td>' + rankPill(lateR) + '</td>' +
      '<td>' + rankPill(totR) + '</td>' +
      '<td>' + (u.spd != null ? u.spd.toFixed(0) : '—') + '</td>' +
      '<td class="wt-cell ' + wtClass + '">' + (wt != null ? (wt > 0 ? '+' : '') + wt.toFixed(1) : '—') + '</td>' +
      '<td class="dist-cell ' + wdClass + '">' + (wd != null ? wd : '—') + '</td>' +
      '<td>' + (u.dslr != null ? u.dslr + 'd' : '—') + '</td>' +
      '<td>' + (fxp ? '$' + fxp.toFixed(2) : '—') + '</td>' +
      '<td>' + (trp ? '$' + trp.toFixed(2) : '—') + '</td>' +
      '<td class="edge-cell ' + edgeClass + '">' + (edge || '—') + '</td>' +
      '<td>' + (isPick ? '<span class="model-badge">MAIN</span>' : '') + '</td>' +
      '</tr>';
  });

  document.getElementById('rd-runners-table').innerHTML =
    '<table class="race-table">' +
      '<thead><tr>' +
        '<th>Tab</th><th>Horse</th><th>Jky</th><th>Trn</th><th>Bar</th>' +
        '<th>TR$</th><th>Mid</th><th>Late</th><th>Total</th>' +
        '<th>Spd</th><th>Wt Tr</th><th>W@D</th><th>DSLR</th>' +
        '<th>Fxd</th><th>TR $</th><th>Edge</th><th>Model</th>' +
      '</tr></thead>' +
      '<tbody>' + rowsHtml + '</tbody>' +
    '</table>';
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

// ── PNL tab rendering ──────────────────────────────────────────────────────
function renderPnL() {
  const settled = SETTLED || [];

  // Compute cumulative actual + expected
  const expectedROI_SP = MODEL_META[PRIMARY_KEY] ? MODEL_META[PRIMARY_KEY].roi_sp : 0;

  // Group by date, sum daily P&L
  const byDate = {};
  settled.forEach(s => {
    const stake = calcStake(s.fxprice);
    if (!stake) return;
    const sp = s.sp || s.top || s.fxprice;
    const profit = s.won ? stake * (sp - 1) : -stake;
    const d = s.date || 'unknown';
    if (!byDate[d]) byDate[d] = { profit: 0, stake: 0, n: 0, wins: 0 };
    byDate[d].profit += profit;
    byDate[d].stake += stake;
    byDate[d].n += 1;
    if (s.won) byDate[d].wins += 1;
  });
  const dates = Object.keys(byDate).sort();
  const cum = []; let running = 0; let runningStake = 0;
  dates.forEach(d => {
    running += byDate[d].profit;
    runningStake += byDate[d].stake;
    cum.push({ date: d, cum: running, expected: runningStake * expectedROI_SP });
  });

  // Render chart
  const svg = document.getElementById('pnl-chart');
  svg.innerHTML = '';
  if (cum.length === 0) {
    svg.innerHTML = '<text x="300" y="100" text-anchor="middle" class="axis-text" style="font-size:12px;">No settled bets yet</text>';
  } else {
    const W = 600, H = 200, pad = 30;
    const maxV = Math.max(1, ...cum.map(p => Math.max(p.cum, p.expected)));
    const minV = Math.min(0, ...cum.map(p => Math.min(p.cum, p.expected)));
    const range = maxV - minV || 1;
    const xs = cum.map((_, i) => pad + (cum.length === 1 ? (W - 2*pad) / 2 : i * (W - 2*pad) / (cum.length - 1)));
    const yScale = v => H - pad - ((v - minV) / range) * (H - 2*pad);
    // Grid + axes
    const zeroY = yScale(0);
    let svgHtml = `<line class="axis" x1="${pad}" y1="${zeroY}" x2="${W-pad}" y2="${zeroY}" stroke-width="1"/>`;
    // Actual line
    const actualPath = cum.map((p, i) => `${i === 0 ? 'M' : 'L'}${xs[i]},${yScale(p.cum)}`).join(' ');
    svgHtml += `<path class="actual" d="${actualPath}"/>`;
    // Expected line
    const expPath = cum.map((p, i) => `${i === 0 ? 'M' : 'L'}${xs[i]},${yScale(p.expected)}`).join(' ');
    svgHtml += `<path class="expected" d="${expPath}"/>`;
    // Y labels
    svgHtml += `<text x="4" y="${yScale(maxV)+4}" class="axis-text">${maxV.toFixed(1)}u</text>`;
    svgHtml += `<text x="4" y="${zeroY+3}" class="axis-text">0u</text>`;
    if (minV < 0) svgHtml += `<text x="4" y="${yScale(minV)+4}" class="axis-text">${minV.toFixed(1)}u</text>`;
    // X labels (first/last)
    svgHtml += `<text x="${xs[0]}" y="${H-8}" class="axis-text">${cum[0].date}</text>`;
    if (cum.length > 1) svgHtml += `<text x="${xs[xs.length-1]}" y="${H-8}" class="axis-text" text-anchor="end">${cum[cum.length-1].date}</text>`;
    svg.innerHTML = svgHtml;
  }

  // Health rows
  const hr = document.getElementById('health-rows');
  hr.innerHTML = '';
  let totalWins = 0, totalStake = 0, spReturn = 0, topReturn = 0;
  let bestWin = 0, worstLoss = 0;
  let currentStreak = 0, longestWinStreak = 0, longestLossStreak = 0;
  let lastResult = null;  // 'W' or 'L'
  // Use chronological order for streak calculation
  const settledChrono = settled.slice();
  settledChrono.forEach(s => {
    const stake = calcStake(s.fxprice);
    if (!stake) return;
    if (s.won) {
      totalWins++;
      if (s.sp) {
        const profit = stake * (s.sp - 1);
        spReturn += stake * s.sp;
        if (profit > bestWin) bestWin = profit;
      }
      if (s.top) topReturn += stake * s.top;
      if (lastResult === 'W') currentStreak++;
      else { currentStreak = 1; lastResult = 'W'; }
      if (currentStreak > longestWinStreak) longestWinStreak = currentStreak;
    } else {
      if (-stake < worstLoss) worstLoss = -stake;
      if (lastResult === 'L') currentStreak++;
      else { currentStreak = 1; lastResult = 'L'; }
      if (currentStreak > longestLossStreak) longestLossStreak = currentStreak;
    }
    totalStake += stake;
  });
  const realWR = settled.length > 0 ? totalWins / settled.length : null;
  const realROI_SP = totalStake > 0 ? (spReturn - totalStake) / totalStake : null;
  const realROI_Top = totalStake > 0 ? (topReturn - totalStake) / totalStake : null;
  const meta = MODEL_META[PRIMARY_KEY] || {};

  function healthRow(lbl, real, expected, type) {
    if (real == null) return '<div class="health-row"><div class="lbl">' + lbl + '</div><div class="v">— (no data)</div><div class="delta">expected ' + (type === 'pct' ? (expected*100).toFixed(1)+'%' : expected.toFixed(2)) + '</div></div>';
    const delta = real - expected;
    const deltaClass = delta > 0 ? 'pos' : (delta < 0 ? 'neg' : '');
    const realStr = type === 'pct' ? (real*100).toFixed(1)+'%' : real.toFixed(2);
    const expStr = type === 'pct' ? (expected*100).toFixed(1)+'%' : expected.toFixed(2);
    const deltaStr = type === 'pct' ? ((delta >= 0 ? '+' : '') + (delta*100).toFixed(1)+'pp') : ((delta >= 0 ? '+' : '') + delta.toFixed(2));
    return '<div class="health-row"><div class="lbl">' + lbl + '</div><div class="v">' + realStr + '</div><div class="delta ' + deltaClass + '">' + deltaStr + ' vs ' + expStr + '</div></div>';
  }
  hr.innerHTML = healthRow('Win rate', realWR, meta.wr || 0, 'pct')
               + healthRow('ROI@SP', realROI_SP, meta.roi_sp || 0, 'pct')
               + healthRow('ROI@Top', realROI_Top, meta.roi_top || 0, 'pct')
               + '<div class="health-row"><div class="lbl">Best win</div><div class="v">' + (bestWin > 0 ? '+' + bestWin.toFixed(2) + 'u' : '—') + '</div><div class="delta">' + (bestWin > 0 ? '+' + fmtDollar(bestWin) : '') + '</div></div>'
               + '<div class="health-row"><div class="lbl">Worst loss</div><div class="v">' + (worstLoss < 0 ? worstLoss.toFixed(2) + 'u' : '—') + '</div><div class="delta">' + (worstLoss < 0 ? fmtDollar(worstLoss) : '') + '</div></div>'
               + '<div class="health-row"><div class="lbl">Longest W streak</div><div class="v">' + longestWinStreak + '</div><div class="delta">in a row</div></div>'
               + '<div class="health-row"><div class="lbl">Longest L streak</div><div class="v">' + longestLossStreak + '</div><div class="delta">in a row</div></div>';

  document.getElementById('health-sample').textContent = settled.length;
  document.getElementById('bh-count').textContent = settled.length;

  // Bet history table
  const tbody = document.getElementById('bh-body');
  tbody.innerHTML = '';
  settled.slice().reverse().forEach(s => {
    const stake = calcStake(s.fxprice);
    const sp = s.sp;
    const settlePrice = sp || s.top || s.fxprice;
    const pl = stake ? (s.won ? stake * (settlePrice - 1) : -stake) : 0;
    tbody.innerHTML += `<tr class="${s.won ? 'win' : 'loss'}">
      <td>${s.date || ''}</td>
      <td>${escapeHtml(s.venue || '')}</td>
      <td>R${s.race}</td>
      <td>${escapeHtml(s.horse || '')}</td>
      <td>$${s.fxprice ? s.fxprice.toFixed(2) : '—'}</td>
      <td>${sp ? '$' + sp.toFixed(2) : '—'}</td>
      <td>${s.top ? '$' + s.top.toFixed(2) : '—'}</td>
      <td>${s.finish || '—'}</td>
      <td>${s.won ? '<span style="color:var(--emerald-deep);font-weight:600;">won</span>' : 'lost'}</td>
      <td class="pl">${pl >= 0 ? '+' : ''}${pl.toFixed(2)}u</td>
    </tr>`;
  });
}

// ── INSIGHTS tab rendering ─────────────────────────────────────────────────
function renderInsights() {
  // Model comparison
  const mc = document.getElementById('model-compare');
  if (mc) {
    let html = '';
    const flat = ALL_PICKS_FLAT || [];
    Object.keys(MODEL_META).forEach(mk => {
      const meta = MODEL_META[mk];
      const picks = flat.filter(p => p.model === mk && p.resulted);
      let wins = 0, stake = 0, ret = 0;
      picks.forEach(p => {
        const s = calcStake(p.fixed_win_price);
        if (!s) return;
        stake += s;
        if (p.won) {
          ret += s * (p.starting_price_sp || p.price_top || p.fixed_win_price || 0);
          wins++;
        }
      });
      const wr = picks.length > 0 ? wins / picks.length : null;
      const roi = stake > 0 ? (ret - stake) / stake : null;
      const isPrimary = mk === PRIMARY_KEY;
      html += `<div class="model-compare">
        <div class="name ${isPrimary ? 'primary' : ''}">${escapeHtml(meta.label || mk)}${isPrimary ? '<span class="tag">primary</span>' : ''}</div>
        <div class="desc-mini">${escapeHtml(meta.desc || '')}</div>
        <div class="stat"><span class="lbl">Bets</span>${picks.length}</div>
        <div class="stat"><span class="lbl">WR</span>${wr != null ? (wr*100).toFixed(1)+'%' : '—'}</div>
        <div class="stat"><span class="lbl">ROI@SP</span>${roi != null ? (roi >= 0 ? '+' : '') + (roi*100).toFixed(1)+'%' : '—'}</div>
      </div>`;
    });
    mc.innerHTML = html;
  }

  // Distribution by price band (settled bets)
  const dp = document.getElementById('dist-price');
  if (dp) {
    const bands = [[0,3],[3,5],[5,8],[8,15],[15,1000]];
    const labels = ['<$3','$3-5','$5-8','$8-15','$15+'];
    const counts = bands.map(() => 0);
    (SETTLED || []).forEach(s => {
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
      html += `<div class="dist-bar"><div class="label">${labels[i]}</div><div class="bar-track"><div class="bar-fill" style="width:${pct}%;"></div></div><div class="count">${c}</div></div>`;
    });
    dp.innerHTML = html || '<div style="color:var(--ink-mute);font-family:var(--font-mono);font-size:11px;">No settled bets yet.</div>';
  }

  // Distribution by venue
  const dv = document.getElementById('dist-venue');
  if (dv) {
    const counts = {};
    (SETTLED || []).forEach(s => {
      const v = s.venue || 'Unknown';
      counts[v] = (counts[v] || 0) + 1;
    });
    const sorted = Object.entries(counts).sort((a, b) => b[1] - a[1]).slice(0, 8);
    const max = Math.max(1, ...sorted.map(e => e[1]));
    let html = '';
    sorted.forEach(([v, c]) => {
      const pct = (c / max * 100).toFixed(0);
      html += `<div class="dist-bar"><div class="label">${escapeHtml(v)}</div><div class="bar-track"><div class="bar-fill" style="width:${pct}%;"></div></div><div class="count">${c}</div></div>`;
    });
    dv.innerHTML = html || '<div style="color:var(--ink-mute);font-family:var(--font-mono);font-size:11px;">No settled bets yet.</div>';
  }

  // Rolling 14-day strike rate
  const rwr = document.getElementById('rolling-wr');
  if (rwr) {
    const settled = (SETTLED || []).slice().sort((a, b) => (a.date || '').localeCompare(b.date || ''));
    if (settled.length === 0) {
      rwr.innerHTML = '<text x="300" y="100" text-anchor="middle" class="axis-text" style="font-size:12px;">No settled bets yet</text>';
    } else {
      const W = 600, H = 200, pad = 30;
      // Window of 14 most recent bets, walking through history
      const points = [];
      for (let i = 0; i < settled.length; i++) {
        const start = Math.max(0, i - 13);
        const window = settled.slice(start, i + 1);
        const wins = window.filter(s => s.won).length;
        points.push({ x: i, wr: wins / window.length });
      }
      const expectedWR = MODEL_META[PRIMARY_KEY] ? MODEL_META[PRIMARY_KEY].wr : 0.25;
      const xScale = i => pad + (points.length === 1 ? (W - 2*pad)/2 : i * (W - 2*pad) / (points.length - 1));
      const yScale = v => H - pad - v * (H - 2*pad);
      let svgHtml = `<line class="grid" x1="${pad}" y1="${yScale(expectedWR)}" x2="${W-pad}" y2="${yScale(expectedWR)}"/>`;
      svgHtml += `<text x="${W-pad+4}" y="${yScale(expectedWR)+3}" class="axis-text">expected ${(expectedWR*100).toFixed(0)}%</text>`;
      const linePath = points.map((p, i) => `${i === 0 ? 'M' : 'L'}${xScale(i)},${yScale(p.wr)}`).join(' ');
      svgHtml += `<path class="actual" d="${linePath}"/>`;
      svgHtml += `<text x="${pad}" y="${H-8}" class="axis-text">bet 1</text>`;
      svgHtml += `<text x="${W-pad}" y="${H-8}" class="axis-text" text-anchor="end">bet ${points.length}</text>`;
      svgHtml += `<text x="4" y="${yScale(0)+3}" class="axis-text">0%</text>`;
      svgHtml += `<text x="4" y="${yScale(0.5)+3}" class="axis-text">50%</text>`;
      svgHtml += `<text x="4" y="${yScale(1)+8}" class="axis-text">100%</text>`;
      rwr.innerHTML = svgHtml;
    }
  }
}

// ── Init ────────────────────────────────────────────────────────────────────
currentBrowseDate = isoDate(0);
renderToday();
renderMeetingsGrid();
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
  // Stale banner: show if data > 6 hours old
  const t = new Date(RUN_ISO).getTime();
  const ageHr = (Date.now() - t) / (1000 * 60 * 60);
  const host = document.getElementById('stale-host');
  if (host) {
    if (ageHr > 6 && !isNaN(t)) {
      host.innerHTML = '<div class="stale-banner">' +
        '<div class="msg">⚠ Data is ' + Math.floor(ageHr) + ' hours old. Recent picks may be missing.</div>' +
        '<button class="btn btn-stale" id="stale-refetch-btn">Refetch today →</button>' +
        '</div>';
      const btn = document.getElementById('stale-refetch-btn');
      if (btn) btn.addEventListener('click', () => {
        document.querySelectorAll('.tab').forEach(x => x.classList.remove('active'));
        document.querySelectorAll('.section').forEach(x => x.classList.remove('active'));
        document.querySelector('.tab[data-tab="settings"]').classList.add('active');
        document.getElementById('sec-settings').classList.add('active');
        // Then dispatch
        dispatchWorkflow(isoDate(0));
      });
    } else {
      host.innerHTML = '';
    }
  }
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
"""
