"""Tests 1, 3, 5 on 2026 complete fields (results files on the page ATW scale, test-model Proj fit before 2026)."""
import numpy as np, pandas as pd
from scipy.optimize import minimize
T = pd.read_pickle('beatflags.pkl')  # frame from research/beat_proj_flags.py
T = T[T.P.notna() & T.wpr.notna()].copy()
T['date'] = pd.to_datetime(T.date)
ok = T.groupby('rk').won.transform('sum') == 1
T = T[ok & (T.groupby('rk').P.transform('size') >= 5)].copy()
gid = T.rk.astype('category').cat.codes.values; y = T.won.values
T['half'] = (T.date >= T.date.median()).astype(int)
def cl(X, pen=0.0):
    X = np.column_stack(X); out = []; bs = []
    for h in (0, 1):
        tr = np.where(T.half.values != h)[0]; te = np.where(T.half.values == h)[0]
        def ll(b, idx):
            z = X[idx] @ b; z = z - pd.Series(z).groupby(gid[idx]).transform('max').values; e = np.exp(z)
            return -(np.log(e / pd.Series(e).groupby(gid[idx]).transform('sum').values)[y[idx] == 1]).mean() + pen * (b[1:] ** 2).sum()
        b = minimize(ll, np.r_[0.2, np.zeros(X.shape[1] - 1)], args=(tr,), method='L-BFGS-B').x; bs.append(b)
        z = X[te] @ b; z = z - pd.Series(z).groupby(gid[te]).transform('max').values; e = np.exp(z)
        p = e / pd.Series(e).groupby(gid[te]).transform('sum').values
        out.append(pd.Series(np.log(p)[y[te] == 1], index=gid[te][y[te] == 1]))
    return pd.concat(out).sort_index(), bs
def gain(a, b): d = b - a; return f'{d.mean():+.4f} (se {d.std()/np.sqrt(len(d)):.4f})'
Pd = (T.P - T.groupby('rk').P.transform('mean')).values
base, bb = cl([Pd]); print(f'{T.rk.nunique()} races, {len(T)} runners; Proj alone winner log-lik {base.mean():.4f}, scale {bb[0][0]:.3f}')

print('\n=== TEST 3: weight credit ===')
W = pd.to_numeric(T.weightCarried, errors='coerce')
Wd = (W - W.groupby(T.rk).transform('mean')).fillna(0).values
Wc = T.wchg.clip(-8, 8).fillna(0).values
e = (T.wpr - T.P).values; ed = e - pd.Series(e).groupby(gid).transform('mean').values
m = np.isfinite(ed) & np.isfinite(Wd)
b1 = np.polyfit(Wd[m], ed[m], 1)[0]; b2 = np.polyfit(Wc[m], ed[m], 1)[0]
print(f'rating miss (actual ATW - Proj, demeaned in race) per kg above field-average weight: {b1:+.3f} points; per kg up on last run: {b2:+.3f}')
s1, b = cl([Pd, Wd]); print(f'winner: Proj + weight vs field   {gain(base, s1)}  coefs {np.round(b[0],3)} (points per kg = {b[0][1]/b[0][0]:+.2f})')
s2, b = cl([Pd, Wc]); print(f'winner: Proj + weight change     {gain(base, s2)}  coefs {np.round(b[0],3)} (points per kg = {b[0][1]/b[0][0]:+.2f})')
s3, b = cl([Pd, Wd, Wc]); print(f'winner: Proj + both             {gain(base, s3)}')
for k in (0.1, 0.2, 0.3, 0.4):
    s, _ = cl([Pd + k * Wd]); print(f'   Proj + {k} points per kg above field average (fixed): {gain(base, s)}')

print('\n=== TEST 5: big fields ===')
T['fs'] = T.groupby('rk').P.transform('size')
fsb = pd.cut(T.fs, [0, 7, 10, 13, 16, 30], labels=['5-7', '8-10', '11-13', '14-16', '17+'])
T['top3'] = T.groupby('rk').P.rank(ascending=False, method='first') <= 3
print(pd.DataFrame({'races': T.groupby(fsb, observed=True).rk.nunique(), 'median miss all': T.groupby(fsb, observed=True).e.median(),
      'median miss Proj top 3': T[T.top3].groupby(fsb[T.top3], observed=True).e.median(),
      'top pick won': T[T.groupby('rk').P.rank(ascending=False, method='first') == 1].groupby(fsb, observed=True).won.mean()}).round(3).to_string())
L = np.log(T.fs.values)
s5, b = cl([Pd, Pd * (L - L.mean())]); print(f'winner: Proj x log field size (sharper or flatter in big fields) {gain(base, s5)} coefs {np.round(b[0],3)}')
long = (T.distance >= 2400).astype(float).values
s6, b = cl([Pd, Pd * long * (T.fs.values >= 14)]); print(f'winner: Proj x (2400m+ and 14+ runners)  {gain(base, s6)} coefs {np.round(b[0],3)}  n races {T[(T.distance>=2400)&(T.fs>=14)].rk.nunique()}')

print('\n=== TEST 1: how close is Proj to the ability limit ===')
d = pd.read_pickle('std_runs.pkl')  # from the race standards scratch build[['horse_id', 'date', 'wpr', 'atw']]
d = d[d.wpr.notna()].sort_values(['horse_id', 'date']); d['date'] = pd.to_datetime(d.date)
g = d.groupby('horse_id').wpr
prev = np.nanmean(np.c_[[g.shift(k).values for k in range(1, 5)]].T, axis=1)
nxt = np.nanmean(np.c_[[g.shift(-k).values for k in range(1, 5)]].T, axis=1)
npv = np.isfinite(np.c_[[g.shift(k).values for k in range(1, 5)]].T).sum(1); nnx = np.isfinite(np.c_[[g.shift(-k).values for k in range(1, 5)]].T).sum(1)
d['orc'] = np.where((npv == 4) & (nnx == 4), (prev + nxt) / 2, np.nan) + (d.atw - d.wpr)
d['prev4'] = np.where(npv == 4, prev, np.nan) + (d.atw - d.wpr)
X = T.merge(d[['horse_id', 'date', 'orc', 'prev4']].drop_duplicates(['horse_id', 'date']), on=['horse_id', 'date'], how='left')
okr = X.groupby('rk').orc.transform(lambda s: s.notna().all())
X = X[okr].copy()
print(f'{X.rk.nunique()} races where every runner has 4 runs before and 4 after; runners {len(X)}')
for c, nm in (('P', 'Proj (test model)'), ('prev4', 'mean of last 4 (past only)'), ('orc', 'oracle: mean of 4 before + 4 after')):
    ee = X.wpr - X[c]; eed = ee - ee.groupby(X.rk).transform('mean')
    print(f'  {nm:38s} RMSE {np.sqrt((ee**2).mean()):.3f}  within-race RMSE {np.sqrt((eed**2).mean()):.3f}  median |miss| {ee.abs().median():.3f}')
gid2 = X.rk.astype('category').cat.codes.values; y2 = X.won.values; X['half'] = (X.date >= X.date.median()).astype(int)
def cl2(col):
    v = (X[col] - X.groupby('rk')[col].transform('mean')).values; out = []
    for h in (0, 1):
        tr = X.half.values != h; te = X.half.values == h
        def ll(b, m):
            z = b[0] * v[m]; gg = gid2[m]; z = z - pd.Series(z).groupby(gg).transform('max').values; e = np.exp(z)
            return -(np.log(e / pd.Series(e).groupby(gg).transform('sum').values)[y2[m] == 1]).mean()
        b = minimize(ll, [0.2], args=(tr,)).x; out.append(-ll(b, te))
    return np.mean(out)
for c, nm in (('P', 'Proj'), ('prev4', 'last 4 mean'), ('orc', 'oracle')):
    sub = X[c].notna()
    print(f'  winner log-lik {nm:12s} {cl2(c):.4f}  top pick wins {(X.loc[X.groupby("rk")[c].idxmax()].won.mean()):.1%}')
