"""Scores upcoming races with the market-residual win model and writes bet_signals.json (+ an append-only log).

For every race that has not started and whose whole field is known and priced it computes, per runner:
  price  the current fixed win price (the price the edge is judged against)
  pmod   the model's win probability (market probability corrected by the model, renormalised within the race)
  ev     pmod * price  (1.20 means 20% above break-even)
  tier   'S' Select, 'V' Volume, '' none
The tier rules and their backtest are in betsignal/README.md. EXPERIMENTAL: validated against closing SP only.
usage: python betsignal/score.py [--now 2026-10-11T03:00:00+00:00]
"""
import argparse
import json
import os
import sys
from datetime import datetime, timedelta, timezone

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import numpy as np
import pandas as pd

from betsignal import features as F

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
MODELS = os.path.join(HERE, 'models')
OUT_JSON = os.path.join(ROOT, 'bet_signals.json')
OUT_LOG = os.path.join(ROOT, 'bet_signal_log.csv.gz')
KEEP_DAYS = 10
FREEZE_MINS = 5          # the frozen (scoreboard) pass is the last one made at least this long before the jump
LOG_WINDOW_MINS = 90     # passes are logged only within this long of the jump

# Tier rules (11 Oct 2026): Select = any runner with EV > 1.20 at any price; Volume = EV > 1.05 at $3 or more. Select is contained in Volume's EV range;
# a runner gets its highest tier. Backtest at SP in README (the $3 floor on Volume turns -6.9% into +1.7% for all EV > 1.05 at $3+).
SELECT_EV, VOLUME_EV, VOLUME_MIN_PRICE = 1.20, 1.05, 3.0


def tier(ev, price=None, rank_m=None):
    if ev > SELECT_EV:
        return 'S'
    if ev > VOLUME_EV and price is not None and price >= VOLUME_MIN_PRICE:
        return 'V'
    return ''


def win_probabilities(s, race_ids, index):
    """Per-runner win probability from the model's log-odds s, BEFORE scaling to sum to 1 within the race. The model is a binary classifier on the
    log-odds scale, so each runner's probability is sigmoid(s). (Until 11 Oct 2026 this was exp(s), which scales the ODDS to sum to 1 and quietly
    pushed probability onto favourites even with no model correction: favourites' average win chance 31.5% -> 36.9% with the correction off.)"""
    return pd.Series(1.0 / (1.0 + np.exp(-np.asarray(s, dtype=float))), index=index)


def no_first_starter_races(tiers, race_ids, nruns):
    """No bets in a race that has a first starter (a runner with no prior run): its tier is cleared (user rule, 11 Oct 2026). EV and model price stay."""
    d = pd.DataFrame({'t': list(tiers), 'r': list(race_ids), 'first': (pd.Series(list(nruns)).fillna(0).values == 0)})
    d['has'] = d.groupby('r')['first'].transform('any')
    return ['' if h else t for t, h in zip(d.t, d.has)]


def _results_signature():
    """Sizes of the results files: changes exactly when the backfill rewrites them (file times are reset by every checkout, so not used)."""
    import glob
    return sorted((os.path.basename(f), os.path.getsize(f)) for f in glob.glob(os.path.join(ROOT, 'race_results_20*.csv.gz')))


def ensure_state(now):
    """Per-horse / jockey / trainer state from the results files. Not committed (13 MB, changes daily): rebuilt here when missing or when the
    results files have changed, and kept between runs by the workflow cache."""
    path = os.path.join(MODELS, 'state.pkl')
    sig = _results_signature()
    if os.path.exists(path):
        state = pd.read_pickle(path)
        if state.get('sig') == sig:
            return state
    H = F.load_history()
    state = F.build_state(H)
    state['sig'] = sig
    pd.to_pickle(state, path)
    print('rebuilt history state through', state['through'].date())
    return state


def load_model(now):
    import lightgbm as lgb
    meta = json.load(open(os.path.join(MODELS, 'meta.json')))
    boosters = [lgb.Booster(model_file=os.path.join(MODELS, f'bet_seed{s}.txt')) for s in meta['seeds']]
    return meta, boosters, ensure_state(now)


def eligible_rows(R, now, stale_horses=frozenset()):
    """One row per runner of every unstarted, fully known and fully priced race. A race is skipped when any runner has a recent run the history
    does not hold yet (results files lag a few days), since its form features would be out of date."""
    R = R.copy()
    R['start'] = pd.to_datetime(R.start_time, utc=True, errors='coerce')
    R = R[(R.scratched != 1) & R.start.notna() & (R.start > now)]
    R['price'] = pd.to_numeric(R.fixed_win_price, errors='coerce')
    R['wt'] = pd.to_numeric(R.weight_carried, errors='coerce').fillna(pd.to_numeric(R.weight_handicap_today, errors='coerce'))
    R['bar'] = pd.to_numeric(R.barrier, errors='coerce')
    R['horse_id'] = pd.to_numeric(R.horse_id, errors='coerce')
    ok_cols = ~R.horse_id.isin(stale_horses) & (R.price > 1) & R.horse_id.notna() & R.jockey.notna() & R.trainer.notna() & (R.bar > 0) & R.wt.notna()
    g = R.assign(ok=ok_cols).groupby('race_id')
    good = g.ok.all() & (g.size() >= 5)
    R = R[R.race_id.isin(good[good].index)].copy()
    n = R.groupby('race_id').race_id.transform('size')
    U = pd.DataFrame({
        'run_id': R.run_id, 'race_id': R.race_id, 'date': R.date, 'start': R.start, 'track': R.venue,
        'raceNumber': pd.to_numeric(R.race, errors='coerce'), 'horse_id': R.horse_id.astype(int), 'jockey': R.jockey, 'trainer': R.trainer,
        'field_size': n, 'distance': pd.to_numeric(R.distance, errors='coerce'),
        'going': R.going.fillna('Good 4'), 'weightCarried': R.wt, 'barrier': R.bar,
        'race_class': R.race_class.map(F.norm_class), 'sp': R.price})
    return U


def score(U, meta, boosters, state):
    X = F.serve_features(U, state, meta['cats'])
    raw = np.mean([b.predict(X[meta['features']], raw_score=True) for b in boosters], axis=0)
    logit = np.log(X.pm / (1 - X.pm))
    s = raw + logit.values
    X['e'] = win_probabilities(s, X.race_id, X.index)
    X['pmod'] = X.e / X.groupby('race_id').e.transform('sum')
    X['ev'] = X.pmod * X.sp
    X['tier'] = [tier(e, p, r) for e, p, r in zip(X.ev, X.sp, X.rank_m)]
    X['tier'] = no_first_starter_races(X.tier, X.race_id, X.nruns)
    return X


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--now', default=None)
    a = ap.parse_args()
    now = pd.Timestamp(a.now) if a.now else pd.Timestamp(datetime.now(timezone.utc))
    sys.path.insert(0, ROOT)
    import runners_io
    R = runners_io.read_runners()
    today = (now + timedelta(hours=10)).strftime('%Y-%m-%d')
    horizon = (now + timedelta(hours=10) + timedelta(days=1)).strftime('%Y-%m-%d')
    meta, boosters, state = load_model(now)
    through = state['through']
    # horses that have run since the history ends (before today): their last run is not in the state, so their races are not scored
    gap = R[(R.date > str(through.date())) & (R.date < today) & (R.scratched != 1)]
    stale = set(pd.to_numeric(gap.horse_id, errors='coerce').dropna().astype(int))
    R = R[(R.date >= today) & (R.date <= horizon)]
    U = eligible_rows(R, now, stale)
    prev = {}
    if os.path.exists(OUT_JSON):
        try:
            prev = json.load(open(OUT_JSON)).get('runs', {})
        except Exception:
            prev = {}
    runs = {}
    if len(U):
        X = score(U, meta, boosters, state)
        stamp = now.strftime('%Y-%m-%dT%H:%M:%SZ')
        rows = []
        for r in X.itertuples():
            mins = (r.start - now).total_seconds() / 60
            cur = dict(p=round(float(r.sp), 2), m=round(float(r.pmod), 4), e=round(float(r.ev), 3), t=r.tier, at=stamp, k=int(r.rank_m))
            old = prev.get(str(r.run_id), {})
            ent = dict(old) if old else {}
            ent['now'] = cur
            if mins >= FREEZE_MINS:
                ent['fz'] = cur   # last pass made before the jump: what the scoreboard judges
            day = pd.Timestamp(r.date).strftime('%Y-%m-%d')
            ent['d'] = day
            runs[str(r.run_id)] = ent
            if mins <= LOG_WINDOW_MINS:
                rows.append((r.run_id, r.race_id, day, stamp, round(mins, 1), cur['p'], cur['m'], cur['e'], r.tier, int(r.rank_m)))
        if rows:
            L = pd.DataFrame(rows, columns=['run_id', 'race_id', 'date', 'made', 'mins', 'price', 'pmod', 'ev', 'tier', 'rank_m'])
            if os.path.exists(OUT_LOG):
                L = pd.concat([pd.read_csv(OUT_LOG), L], ignore_index=True)
            L.to_csv(OUT_LOG, index=False, compression='gzip')
    # carry earlier runs (frozen history) forward, drop anything older than KEEP_DAYS
    cutoff = (now - timedelta(days=KEEP_DAYS)).strftime('%Y-%m-%d')
    for k, v in prev.items():
        if k not in runs and v.get('d', '') >= cutoff:
            runs[k] = v
    out = dict(v=1, made=now.strftime('%Y-%m-%dT%H:%M:%SZ'), trained_through=meta['trained_through'], experimental=True,
               rules=dict(select_ev=SELECT_EV, volume_ev=VOLUME_EV, volume_min_price=VOLUME_MIN_PRICE, freeze_mins=FREEZE_MINS), runs=runs)
    with open(OUT_JSON, 'w') as f:
        json.dump(out, f, separators=(',', ':'))
    n_s = sum(1 for v in runs.values() if v.get('now', {}).get('t') == 'S')
    n_v = sum(1 for v in runs.values() if v.get('now', {}).get('t') in ('S', 'V'))
    print(f'history through {through.date()}, {len(stale)} horses with an unrecorded recent run; scored {len(U)} runners in {U.race_id.nunique() if len(U) else 0} races; tiers now: Select {n_s}, Volume incl. Select {n_v}; file has {len(runs)} runs')


if __name__ == '__main__':
    main()
