"""How low can the error go? A future-peeking ceiling plus the winner test for the relevance-weighted history model (22 Oct 2026). Needs the pickle written by
research/proj_history_relevance.py (HR_OUT). The oracle predicts a run from the mean of the horse's 4 runs before AND 4 runs after it (future runs included, which a real
projection never has), through a fitted line; if that cannot beat the live Proj, run-to-run noise in the ratings is the limit, not the method.
Run: PYTHONPATH=. python research/proj_ceiling.py path/to/hr.pkl"""
import sys
import numpy as np, pandas as pd
from scipy.optimize import minimize
te = pd.read_pickle(sys.argv[1]).sort_values(['horse_id', 'date']).reset_index(drop=True)
te['mu_base'] = te.wpr - te.e_base; te['mu_all'] = te.wpr - te.e_all
g = te.groupby('horse_id').wpr
def nb(s):
    v = s.values; out = np.full(len(v), np.nan)
    for i in range(len(v)):
        idx = [j for j in range(max(0, i - 4), min(len(v), i + 5)) if j != i]
        if len(idx) >= 6: out[i] = v[idx].mean()
    return pd.Series(out, index=s.index)
te['orc'] = g.transform(nb); z = te.dropna(subset=['orc'])
rm = lambda x: float(np.sqrt((x ** 2).mean()))
A = np.polyfit(z.orc, z.wpr, 1)
print(f"{len(z):,} runs with 8 neighbours: oracle (4 before + 4 after, future included) RMSE {rm(z.wpr - np.polyval(A, z.orc)):.3f}; live Proj {rm(z.e_base):.3f}; relevance-weighted model {rm(z.e_all):.3f}")
te['race'] = te.date.astype(str) + '|' + te.track.astype(str) + '|' + te.distance.astype(str) + '|' + te.field_size.astype(str) + '|' + te.race_class.astype(str)
te['won'] = (te.positionFinish == 1).astype(int); te['nr'] = te.groupby('race').won.transform('size'); te['nw'] = te.groupby('race').won.transform('sum')
d = te[(te.nr >= 3) & (te.nw == 1)].copy(); d['rid'] = d.race.astype('category').cat.codes
def ll(df, col, b):
    s = b * df[col].values; mx = pd.Series(s).groupby(df.rid.values).transform('max').values; e = np.exp(s - mx)
    return (s - (np.log(pd.Series(e).groupby(df.rid.values).transform('sum').values) + mx))[df.won.values == 1]
fit = lambda df, c: minimize(lambda b: -ll(df, c, b[0]).mean(), [0.15], method='L-BFGS-B').x[0]
dates = sorted(d.date.unique()); half = dates[len(dates) // 2]; A_, B_ = d[d.date < half], d[d.date >= half]
o = {c: np.concatenate([ll(B_, c, fit(A_, c)), ll(A_, c, fit(B_, c))]) for c in ('mu_base', 'mu_all')}
dd = o['mu_all'] - o['mu_base']
print(f"winner test ({d.rid.nunique():,} store races): live {o['mu_base'].mean():.4f}  relevance-weighted {o['mu_all'].mean():.4f}  gain {dd.mean():+.4f} (se {dd.std()/np.sqrt(len(dd)):.4f})")
