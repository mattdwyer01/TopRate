"""Test 2 (early prices): does the Proj or the finishing-position model add to the fixed price 30 minutes before the jump? Run from the repo root on a current main
after research/five_tests_live.py's frame code (toprate_price_history.csv, runners.csv, data/direct_scores)."""
import numpy as np, pandas as pd
from scipy.optimize import minimize
exec(open('research/five_tests_live.py').read().split("print('\\n=== TEST 4")[0])
E = R[R.groupby('race_id').e30.transform(lambda s: s.notna().all())].copy()
for c, s in (('lme', 'e30'), ('lsp', 'sp')):
    E[c] = np.log(1 / E[s]); E[c] -= E.groupby('race_id')[c].transform('mean')
E['Pd'] = E.P - E.groupby('race_id').P.transform('mean')
E['ldm'] = np.log(E.dm.clip(1e-4)); E['ldm'] -= E.groupby('race_id').ldm.transform('mean')
E = E.reset_index(drop=True); E["half"] = (E.race_id.rank(method="dense") > E.race_id.nunique() / 2).astype(int) if False else (pd.to_datetime(E.date) >= pd.to_datetime(E.date).median()).astype(int)
gid = E.race_id.astype('category').cat.codes.values; y = E.won.values
print('winners per race', pd.Series(y).groupby(gid).sum().value_counts().to_dict(), 'half counts', E.half.value_counts().to_dict())
def ll(b, X, m):
    z = X[m] @ b; g = gid[m]
    df = pd.DataFrame({'z': z, 'g': g}); df['z'] -= df.groupby('g').z.transform('max'); df['e'] = np.exp(df.z)
    p = df.e / df.groupby('g').e.transform('sum')
    return -np.log(p.values[y[m] == 1]).mean()
def per_race(b, X, m):
    z = X[m] @ b; g = gid[m]
    df = pd.DataFrame({'z': z, 'g': g}); df['z'] -= df.groupby('g').z.transform('max'); df['e'] = np.exp(df.z)
    p = df.e / df.groupby('g').e.transform('sum')
    return pd.Series(np.log(p.values[y[m] == 1]), index=g[y[m] == 1])
def run(cols):
    per = []
    X = E[cols].values.astype(float); tot = 0; n = 0
    for h in sorted(E.half.unique()):
        tr = E.half.values != h; te = E.half.values == h
        if tr.sum() == 0: tr = te
        b = minimize(ll, np.full(len(cols), 0.2), args=(X, tr), method='L-BFGS-B').x
        tot += -ll(b, X, te) * (y[te] == 1).sum(); n += (y[te] == 1).sum()
        per.append(per_race(b, X, te))
    return tot / n, b, pd.concat(per)
res = {}
for cols in (['lme'], ['lme', 'Pd'], ['lme', 'ldm'], ['lme', 'Pd', 'ldm'], ['lsp'], ['lsp', 'Pd'], ['lsp', 'Pd', 'ldm']):
    v, b, pr = run(cols); res['+'.join(cols)] = pr.sort_index()
    base = res['lme'] if cols[0] == 'lme' else res['lsp']; d = pr.sort_index() - base
    print(f'{"+".join(cols):14s} winner log-lik {v:.4f}  gain over market alone {d.mean():+.4f} (se {d.std()/np.sqrt(len(d)):.4f})  coefs {np.round(b,3)}')
