"""Barrier x run style table (A2E, POT%, win SR) per track, and an as-of test of whether it adds to the market.
Run: PYTHONPATH=. python research/barrier_style_table.py [track substring]"""
import sys, glob
import numpy as np, pandas as pd
from scipy.optimize import minimize

TRACK = sys.argv[1] if len(sys.argv) > 1 else 'Flemington'
want = ['race_id','date','track','distance','horse_id','field_size','barrier','priceStarting','position800m',
        'position600m','positionFinish','wpr','isBarrierTrial','race_class']
fr = []
for f in sorted(glob.glob('race_results_20[12]*.csv.gz')):
    c = pd.read_csv(f, nrows=0).columns
    d = pd.read_csv(f, usecols=[x for x in want if x in c]); fr.append(d)
d = pd.concat(fr, ignore_index=True)
d = d[(d.date >= '2019-01-01') & (d.isBarrierTrial != True) & d.barrier.notna() & d.field_size.notna()].copy()
d = d[d.field_size >= 6]
d['yr'] = d.date.astype(str).str[:4].astype(int)
d['won'] = (d.positionFinish == 1).astype(int)
pos = d.position800m.fillna(d.position600m)
d['early'] = (pos - 1) / (d.field_size - 1)          # 0 = led, 1 = last
d = d.sort_values(['date', 'race_id'])
# as-of horse style: mean early fraction of previous 5 runs (needs 2)
g = d.groupby('horse_id')['early']
d['sty'] = g.transform(lambda s: s.shift(1).rolling(5, min_periods=2).mean())
d['sgrp'] = pd.cut(d['sty'], [-1, .30, .55, 2], labels=['Forward', 'Midfield', 'Back'])
d['bgrp'] = pd.cut(d.barrier, [0, 3, 7, 99], labels=['Inside (1-3)', 'Middle (4-7)', 'Wide (8+)'])
# clean book + normalised implied prob
d = d[d.priceStarting > 1]
d['ip'] = 1 / d.priceStarting
bk = d.groupby('race_id').ip.transform('sum'); n = d.groupby('race_id').ip.transform('size')
d = d[(bk >= 1.05) & (bk <= 2.0) & (n == d.field_size)]
d['p'] = d.ip / d.groupby('race_id').ip.transform('sum')
d['ret'] = d.won * d.priceStarting - 1
d = d[d.won.groupby(d.race_id).transform('sum') == 1]
d['dgrp'] = pd.cut(d.distance, [0, 1300, 1700, 2100, 9999], labels=['sprint', 'mile', 'middle', 'stay'])

def table(x):
    r = x.groupby(['bgrp', 'sgrp'], observed=True).agg(w=('won', 'sum'), n=('won', 'size'), e=('p', 'sum'), roi=('ret', 'mean'))
    r['A2E'] = r.w / r.e; r['POT%'] = 100 * r.roi; r['WinSR%'] = 100 * r.w / r.n
    return r[['A2E', 'POT%', 'WinSR%', 'w', 'n']].round(2).unstack('sgrp')

t = d[d.track.astype(str).str.contains(TRACK, case=False)]
print(f'{TRACK}: {len(t)} runners, {t.race_id.nunique()} races, {t.date.min()} to {t.date.max()}')
pd.set_option('display.width', 250); pd.set_option('display.max_columns', 30)
print(table(t)); print('ALL TRACKS'); print(table(d))

# ---- as-of predictive test: does the cell's historical A2E add to the market? ----
d['cell'] = d.track.astype(str) + '|' + d.dgrp.astype(str) + '|' + d.bgrp.astype(str) + '|' + d.sgrp.astype(str)
d = d[d.sgrp.notna() & d.dgrp.notna()]
K = 60.0
def feat(test_year):
    h = d[d.yr < test_year].groupby('cell').agg(w=('won', 'sum'), e=('p', 'sum'))
    x = d[d.yr == test_year].join(h, on='cell')
    w = x.w.fillna(0); e = x.e.fillna(0)
    x['x'] = np.log((w + K * 0.0 + 1e-9 + 0.0) / 1) if False else np.log((w + K * 0.1) / (e + K * 0.1))  # shrunk log A2E (prior A2E 1)
    return x
rows = []
for y in (2023, 2024, 2025, 2026):
    rows.append(feat(y))
X = pd.concat(rows)
X['x'] = X.x.fillna(0.0)
X['lm'] = np.log(X.p)
codes, rid = np.unique(X.race_id.values, return_inverse=True)
def nll(par, use):
    u = par[0] * X.lm.values + (par[1] * X.x.values if use else 0)
    eu = np.exp(np.clip(u, -30, 30))
    s = np.bincount(rid, eu)[rid]
    lp = u - np.log(s) - 0  # stabiliser cancels
    return -(lp * X.won.values).sum()
def fit(use):
    r = minimize(nll, [1.0, 0.0], args=(use,), method='BFGS'); return r
a = fit(False); b = fit(True)
print('\nAS-OF TEST (cell = track x distance group x barrier group x style, history before each year, 2023-2026)')
print(f'races {len(codes)}  winner LL/race: market {-a.fun/len(codes):.4f}  + cell A2E {-b.fun/len(codes):.4f}  gain {(a.fun-b.fun)/len(codes):.5f}  coef on log A2E {b.x[1]:.3f}')
# per-race paired se
def per_race(par, use):
    u = par[0] * X.lm.values + (par[1] * X.x.values if use else 0)
    eu = np.exp(u); s = np.bincount(rid, eu)[rid]
    return np.bincount(rid, (np.log(eu / s)) * X.won.values)
dd = per_race(b.x, True) - per_race(a.x, False)
print(f'paired gain {dd.mean():.5f} se {dd.std()/np.sqrt(len(dd)):.5f}')
for y in (2023, 2024, 2025, 2026):
    m = (X.yr == y).values
    print(y, 'corr(x, won - p) =', round(np.corrcoef(X.x[m], X.won[m] - X.p[m])[0, 1], 4), 'n', m.sum())

# ---- rating test: does the as-of cell mean rating residual predict the next rating beyond prior form? ----
d = d.sort_values(['date', 'race_id'])
d['w'] = d.wpr - d.groupby('race_id').wpr.transform('mean')
d['l3'] = d.groupby('horse_id').wpr.transform(lambda s: s.shift(1).rolling(3, min_periods=2).mean())
d['l3'] = d.l3 - d.groupby('race_id').l3.transform('mean')
r = d.dropna(subset=['w', 'l3']).copy()
tr = r[r.yr < 2025]; b1 = np.polyfit(tr.l3, tr.w, 1)
r['res'] = r.w - np.polyval(b1, r.l3)
r['fld'] = pd.cut(r.field_size, [0, 9, 12, 99], labels=['s', 'm', 'l'])
r['cell2'] = r.cell + '|' + r.fld.astype(str)
r['cellb'] = r.track.astype(str) + '|' + r.dgrp.astype(str) + '|' + r.bgrp.astype(str) + '|' + r.fld.astype(str)
for nm, col in (('track x dist x barrier x STYLE x field', 'cell2'), ('track x dist x barrier x field (no style)', 'cellb')):
    for y in (2025, 2026):
        h = r[r.yr < y].groupby(col).res.agg(['sum', 'size'])
        x = r[r.yr == y].join(h, on=col)
        k = 40.0
        x['eff'] = (x['sum'].fillna(0) / (x['size'].fillna(0) + k))
        c = np.corrcoef(x.eff, x.res)[0, 1]; sl = np.polyfit(x.eff, x.res, 1)[0]
        mse0 = (x.res ** 2).mean(); mse1 = ((x.res - sl * x.eff) ** 2).mean()
        print(f'{nm:42s} {y}: corr {c:.3f} slope {sl:.2f} MSE {mse0:.3f} -> {mse1:.3f} ({100*(mse0-mse1)/mse0:.2f}%) n {len(x)}')
