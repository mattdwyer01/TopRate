# ATW-calibrated direct-model blend: weight s in rating = race mean of Proj + (1-s)(Proj dev) + s x 5 x (ln chance dev), fit on TopRate's published ATW.
# Inputs: live_frame.pkl (logged Proj, direct scores dm, results) and data/tr_results. Scratch-built, see CLAUDE.md entry of 10 Nov 2026.
import json, gzip, glob, numpy as np, pandas as pd
from scipy.optimize import minimize, minimize_scalar
R = pd.read_pickle('live_frame.pkl')
act = {}; fin = {}
for f in glob.glob('wt/data/tr_results/*.json.gz'):
    x = json.load(gzip.open(f)); d = x['date']
    for rid, rr in x['races'].items():
        st = rr.get('status') or rr.get('ratingStatus')
        for u in rr['runners']:
            if u.get('atw') is not None: act[(str(u['horse']).lower(), d)] = u['atw']
R['h'] = R.horse.astype(str).str.lower(); R['atw'] = [act.get((h, d)) for h, d in zip(R.h, R.date)]
D = R[R.groupby('race_id').dm.transform(lambda s: s.notna().all())].copy()
D['ldm'] = np.log(D.dm.clip(1e-4))
D['Pm'] = D.groupby('race_id').P.transform('mean'); D['Pd'] = D.P - D.Pm
D['Ld'] = D.ldm - D.groupby('race_id').ldm.transform('mean')
D['dt'] = pd.to_datetime(D.date); D['wk'] = D.dt.dt.isocalendar().week
print('races', D.race_id.nunique(), 'dates', D.date.min(), D.date.max())
print('sd within race: Pd %.2f  5*Ld %.2f  corr %.3f' % (D.Pd.std(), (5*D.Ld).std(), np.corrcoef(D.Pd, D.Ld)[0,1]))
gid = D.race_id.astype('category').cat.codes.values; y = D.won.values
A = D.atw.notna().values
def hub(e, k=4): a = np.abs(e); return np.where(a < k, .5*e*e, k*a-k*k/2)
def fig(s, m=None):
    return (D.Pm + (1-s)*D.Pd + s*5*D.Ld).values
def atw_stats(v, m):
    e = (D.atw.values - v)[m & A]; g = gid[m & A]
    ed = e - pd.Series(e).groupby(g).transform('mean').values
    return np.sqrt((e**2).mean()), np.median(np.abs(e)), (np.abs(e) <= 3).mean(), np.sqrt((ed**2).mean()), hub(e).mean()
def wll(v, m, beta=None):
    df = pd.DataFrame({'v': v[m], 'g': gid[m], 'y': y[m]}); df['v'] -= df.groupby('g').v.transform('mean')
    def ll(b):
        z = b*df.v; z = z - z.groupby(df.g).transform('max'); e = np.exp(z); p = e/e.groupby(df.g).transform('sum')
        return -np.log(p[df.y == 1]).mean()
    if beta is None: beta = minimize_scalar(ll, bounds=(.01, 1), method='bounded').x
    return -ll(beta), beta
allm = np.ones(len(D), bool)
print('\n s   RMSE  med|e| within3 inRaceRMSE huber | winLL(beta fit) beta | winLL@0.20')
for s in [0, .1, .2, .25, .3, .4, .5, .6, .7]:
    v = fig(s); r = atw_stats(v, allm); w, b = wll(v, allm); w2, _ = wll(v, allm, .2)
    print(f'{s:.2f} {r[0]:.3f} {r[1]:.3f} {r[2]:.1%} {r[3]:.3f} {r[4]:.3f} | {w:.4f} {b:.3f} | {w2:.4f}')
# fit s on ATW (Huber), by half, by week, bootstrap
def fit_s(m):
    mm = m & A; e0 = D.atw.values[mm]
    f = lambda s: hub(e0 - fig(s)[mm]).mean()
    return minimize_scalar(f, bounds=(0, 1), method='bounded').x
med = D.dt.median(); h1 = (D.dt < med).values
print('\nATW-fitted s: all %.3f  first half %.3f  second half %.3f' % (fit_s(allm), fit_s(h1), fit_s(~h1)))
for w in sorted(D.wk.unique()):
    m = (D.wk == w).values; print('  week', w, 'races', D.race_id[m].nunique(), 's %.3f' % fit_s(m))
rng = np.random.default_rng(1); races = D.race_id.unique(); idx = D.groupby('race_id').indices
bs = []
for i in range(200):
    pick = rng.choice(races, len(races)); rows = np.concatenate([idx[r] for r in pick])
    mm = np.zeros(len(D), bool); cnt = np.bincount(rows, minlength=len(D))
    e0 = D.atw.values; ok = A & (cnt > 0)
    f = lambda s: (hub(e0[ok] - fig(s)[ok]) * cnt[ok]).sum() / cnt[ok].sum()
    bs.append(minimize_scalar(f, bounds=(0, 1), method='bounded').x)
print('bootstrap s: mean %.3f  5-95%% %.3f to %.3f' % (np.mean(bs), *np.percentile(bs, [5, 95])))
# also squared loss fit and the free 2-coef fit for comparison
mm = A; X = np.c_[D.Pd, D.Ld][mm]; yy = (D.atw - D.Pm).values[mm]
b = np.linalg.lstsq(X, yy, rcond=None)[0]; print('OLS free fit: %.3f x Pd + %.3f x Ld (direct share in points %.0f%%)' % (b[0], b[1], 100*b[1]/5/(b[0]+b[1]/5)))
# winner-LL fitted s, by half
def fit_sw(m):
    return minimize_scalar(lambda s: -wll(fig(s), m, .2)[0], bounds=(0, 1), method='bounded').x
print('winner-fitted s (beta 0.20): first half %.3f  second half %.3f' % (fit_sw(h1), fit_sw(~h1)))
D.to_pickle('blend_s.pkl')
