"""Compare the Huber Proj trained on excuse-uplifted history (research/excuse_uplift.py -> /tmp/excuse_te.parquet) with the current Huber Proj
(/tmp/train_ctx_gps_oos.parquet, written by analysis/trip_map/train_ctx_gps.py) on the same held-out 2026 runs. Miss = actual rating - Proj (actual never uplifted)."""
import numpy as np, pandas as pd
from scipy.optimize import minimize
a = pd.read_parquet('/tmp/excuse_te.parquet'); a['date'] = pd.to_datetime(a.date)
b = pd.read_parquet('/tmp/train_ctx_gps_oos.parquet'); b['date'] = pd.to_datetime(b.date)
b = b[b.date >= '2026-01-01'][['horse_id', 'date', 'proj0', 'half', 'rid', 'priceStarting', 'positionFinish', 'rank_prior' if 'rank_prior' in b.columns else 'horse_id']]
m = a.merge(b, on=['horse_id', 'date'], how='inner', suffixes=('', '_b'))
m['mb'] = m.wpr - m.proj0; m['ma'] = m.wpr - m.projA
print('matched runs', len(m), 'of', len(a))
def st(e): return f'MAE {e.abs().mean():.3f} within3 {100 * (e.abs() <= 3).mean():.1f}% within5 {100 * (e.abs() <= 5).mean():.1f}% rmse {np.sqrt((e ** 2).mean()):.3f} median {e.median():+.2f}'
def pair(e0, e1):
    d = e0.abs() - e1.abs(); s = e0 ** 2 - e1 ** 2
    return f'abs gain {d.mean():+.4f} (se {d.std() / np.sqrt(len(d)):.4f}), sq gain {s.mean():+.4f} (se {s.std() / np.sqrt(len(s)):.4f})'
subs = {'all runs': m.n >= 0, '3+ earlier runs': m.n >= 3, 'top half by prior': m.half == True,
        'an uplifted run in the last 3': m.n_up3 >= 1, 'two or more uplifted runs in the last 3': m.n_up3 >= 2, 'uplift sum over last 3 >= 6 points': m.up_sum3 >= 6, 'no uplifted run in the last 3': (m.n_up3 == 0) & (m.n >= 3),
        'top half and an uplifted run in last 3': (m.half == True) & (m.n_up3 >= 1)}
for k, msk in subs.items():
    d = m[msk]; print(f'{k:42s} n={len(d):6d}\n   current Proj: {st(d.mb)}\n   with uplift : {st(d.ma)}\n   {pair(d.mb, d.ma)}   mean Proj change {d.projA.mean() - d.proj0.mean():+.2f}')
# mean miss by uplift amount: does the current Proj under-rate horses with excused runs?
m['up_bin'] = pd.cut(m.up_sum3, [-1, 0.5, 3, 6, 10, 100])
print('\nmean miss of the CURRENT Proj by total uplift in the last 3 runs (positive = Proj too low):')
print(m[m.n >= 3].groupby('up_bin', observed=True).agg(n=('mb', 'size'), mean_miss_current=('mb', 'mean'), mean_miss_uplift=('ma', 'mean'), median_current=('mb', 'median'), median_uplift=('ma', 'median')).round(2).to_string())
# winners, partial fields
w = m[m.rid.notna() & m.priceStarting.notna() & (m.priceStarting > 1)].copy()
w['win'] = (w.positionFinish == 1).astype(int); w['lp'] = -np.log(w.priceStarting)
gb = w.groupby('rid'); w = w[(gb.win.transform('sum') == 1) & (gb.win.transform('size') >= 6)].copy()
for c in ('proj0', 'projA', 'lp'): w['x_' + c] = w[c] - w.groupby('rid')[c].transform('mean')
d0 = w.date.sort_values().iloc[len(w) // 2]
def nll(par, d, cols):
    e = pd.Series(sum(p * d[c].values for p, c in zip(par, cols)), index=d.index)
    mx = e.groupby(d.rid).transform('max'); ex = np.exp(e - mx); den = ex.groupby(d.rid).transform('sum')
    return -np.log(ex / den)[d.win == 1].sum(), np.log(ex / den)[d.win == 1]
def cross(cols, sel=None):
    ll = []
    for x, y in ((w[w.date < d0], w[w.date >= d0]), (w[w.date >= d0], w[w.date < d0])):
        r = minimize(lambda p: nll(p, x, cols)[0], np.full(len(cols), 0.1), method='Nelder-Mead'); ll.append(nll(r.x, y, cols)[1])
    s = pd.concat(ll)
    return s if sel is None else s[s.index.isin(sel)]
print('\nWINNERS: races', w.rid.nunique(), 'runners', len(w))
up_races = set(w.index[w.n_up3 >= 1]); 
raceflag = w.groupby('rid').n_up3.transform(lambda s: (s >= 1).any()); sel = set(w.index[(raceflag) & (w.win == 1)])
for lab, c0, c1 in (('Proj alone', ['x_proj0'], ['x_projA']), ('market + Proj', ['x_lp', 'x_proj0'], ['x_lp', 'x_projA'])):
    l0, l1 = cross(c0), cross(c1); d = (l1 - l0).dropna()
    print(f'  {lab:14s} current {l0.mean():.4f}  with uplift {l1.mean():.4f}  gain {d.mean():+.4f} (se {d.std() / np.sqrt(len(d)):.4f})  [{len(d)} races]')
    ds = d[d.index.isin(sel)]
    print(f'     only races with a runner that had an uplifted run in its last 3: gain {ds.mean():+.4f} (se {ds.std() / np.sqrt(len(ds)):.4f}) [{len(ds)} races]')
