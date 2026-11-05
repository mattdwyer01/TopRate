"""overlay_layer.py -- stage 3: does the direct (winner) model add anything to an EARLY fixed price, and does it find overlay winners?

The winner model (direct_score.py -> data/direct_scores) ranks a field. This layer asks the separate question: against a price you could actually take
before the jump, where does the model's view beat the market? Evaluated only on prices from toprate_price_history.csv (TAB fixed-odds reads), never SP.

  python overlay_layer.py eval [--mins 30] [--from 2026-10-30]   joins scores, early prices and results; prints the pre-registered metrics

Pre-registered metrics (fixed before looking, see CLAUDE.md entry):
  1. gain in winner log-lik of (price + model) over price alone, weight fitted leave-one-day-out
  2. flagged runners (blended EV >= EV_MIN): win rate vs price-implied rate, flat ROI at the early price, ROI excluding the 3 / 6 biggest winners, by date half
  3. winner capture: top pick / top 3 of the model vs the market
No rule is adopted from a single run: forward log first."""
import argparse, json, sys
from pathlib import Path
import numpy as np, pandas as pd

ROOT = Path(__file__).resolve().parent
BOOK_MIN, BOOK_MAX = 1.05, 2.0
EV_MIN = 1.05


def load(mins, start):
    import runners_io
    r = runners_io.read_runners()
    r['date'] = pd.to_datetime(r.date)
    r = r[r.date >= start]
    r['race_id'] = pd.to_numeric(r.race_id, errors='coerce')
    r['tab'] = pd.to_numeric(r.tab_number, errors='coerce')
    r['run_id'] = pd.to_numeric(r.run_id, errors='coerce')
    # model chances
    rows = []
    for f in sorted((ROOT / 'data' / 'direct_scores').glob('*.json')):
        for rid, tabs in json.loads(f.read_text())['races'].items():
            for t, p in tabs.items():
                rows.append((int(rid), int(t), p))
    S = pd.DataFrame(rows, columns=['race_id', 'tab', 'dm'])
    d = r.merge(S, on=['race_id', 'tab'], how='inner')
    # early price: latest read at or before `mins` minutes before the jump
    P = pd.read_csv(ROOT / 'toprate_price_history.csv')
    P['t'] = pd.to_datetime(P.snapshot_time, utc=True)
    d['start'] = pd.to_datetime(d.start_time, utc=True, errors='coerce')
    st = d.groupby('race_id').start.first()
    P['start'] = P.race_id.map(st)
    P['m'] = (P.start - P.t).dt.total_seconds() / 60
    P = P[(P.m >= mins) & (P.fixed_win_price > 1)].sort_values('t').groupby('run_id').tail(1)
    d = d.merge(P[['run_id', 'fixed_win_price']].rename(columns={'fixed_win_price': 'ep'}), on='run_id', how='left')
    d['won'] = pd.to_numeric(d.won, errors='coerce')
    d['sp'] = pd.to_numeric(d.get('starting_price_sp'), errors='coerce')
    d['scr'] = d.scratched.astype(str).isin(['1', '1.0', 'True'])
    return d[~d.scr]


def clean_races(d):
    """Races usable for a log-lik test: every runner has a model chance and an early price, one winner, price book in range."""
    g = d.groupby('race_id')
    ok = g.ep.apply(lambda s: s.notna().all()) & (g.won.sum() == 1) & g.dm.apply(lambda s: s.notna().all()) & (g.size() >= 5)
    d = d[d.race_id.isin(ok[ok].index)].copy()
    d['imp'] = 1 / d.ep
    book = d.groupby('race_id').imp.transform('sum')
    d = d[(book >= BOOK_MIN) & (book <= BOOK_MAX)].copy()
    d['q'] = d.imp / d.groupby('race_id').imp.transform('sum')
    d['dm'] = d.dm / d.groupby('race_id').dm.transform('sum')
    return d


def ll(d, p):
    return float(np.log(np.clip(p[d.won == 1], 1e-9, 1)).mean())


def blend(d, w):
    z = np.log(d.q) + w * np.log(d.dm)
    e = np.exp(z - z.groupby(d.race_id).transform('max'))
    return e / e.groupby(d.race_id).transform('sum')


def fit_w(d):
    best = (-9, 0)
    for w in np.arange(-0.2, 1.01, 0.05):
        v = ll(d, blend(d, w))
        if v > best[0]:
            best = (v, w)
    return best[1]


def roi(x, ex=0):
    if not len(x):
        return np.nan
    ret = (x.won * x.ep).sort_values(ascending=False)
    keep = x.index.difference(ret.index[:ex]) if ex else x.index
    xs = x.loc[keep]
    return float((xs.won * xs.ep - 1).mean())


def evaluate(mins, start):
    d = clean_races(load(mins, start))
    nr = d.race_id.nunique()
    print(f'{nr} clean races, {len(d)} runners, early price >= {mins} min out, from {start}')
    if nr < 30:
        print('too few races for a test'); return
    dates = sorted(d.date.unique())
    # leave-one-day-out weight
    d['p'] = np.nan
    for day in dates:
        tr, te = d[d.date != day], d[d.date == day]
        w = fit_w(tr)
        d.loc[te.index, 'p'] = blend(te, w)
    w_all = fit_w(d)
    print(f'weight on model (all days) {w_all:.2f}')
    print(f'winner log-lik: price alone {ll(d, d.q):.4f}   model alone {ll(d, d.dm):.4f}   price+model (LODO) {ll(d, d.p):.4f}   gain {ll(d, d.p) - ll(d, d.q):+.4f}')
    # capture
    for nm, col in (('market', 'q'), ('model', 'dm'), ('blend', 'p')):
        rk = d.groupby('race_id')[col].rank(ascending=False, method='first')
        w = d.won == 1
        print(f'  {nm:7s} top pick {100 * ((rk == 1) & w).sum() / nr:5.1f}%   winner in top 3 {100 * ((rk <= 3) & w).sum() / nr:5.1f}%')
    # overlay flags
    d['ev'] = d.p * d.ep
    d['evm'] = d.dm * d.ep
    mid = dates[len(dates) // 2]
    for nm, col, thr in (('blend EV', 'ev', 1.05), ('blend EV', 'ev', 1.10), ('blend EV', 'ev', 1.20), ('model-only EV', 'evm', 1.20), ('model-only EV', 'evm', 1.50)):
        x = d[d[col] >= thr]
        if not len(x):
            print(f'{nm} >= {thr}: none'); continue
        print(f'{nm} >= {thr:.2f}: n={len(x)} win {100 * x.won.mean():.1f}% vs price-implied {100 * x.q.mean():.1f}% avg ${x.ep.mean():.2f} ROI {100 * roi(x):+.1f}% ex3 {100 * roi(x, 3):+.1f}% ex6 {100 * roi(x, 6):+.1f}% halves {100 * roi(x[x.date < mid]):+.1f}/{100 * roi(x[x.date >= mid]):+.1f}')
    allr = d
    print(f'all runners ROI {100 * roi(allr):+.1f}%; model-top pick ROI {100 * roi(d[d.groupby("race_id").dm.rank(ascending=False, method="first") == 1]):+.1f}%')


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('cmd', choices=['eval'])
    ap.add_argument('--mins', type=float, default=30)
    ap.add_argument('--from', dest='start', default='2026-10-30')
    a = ap.parse_args()
    evaluate(a.mins, a.start)
