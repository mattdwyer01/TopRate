import numpy as np, pandas as pd, re
from scipy.optimize import minimize
T = pd.read_pickle('longdist.pkl')     # 2026 complete fields: P (test-model Proj, fit before 2026), wpr actual, l3, n, d_last
cols = ['horse_id','date','race_id','weightCarried','positionFinish','starters','field_size','marginFinish','comments_steward','comments_video','gear_changes','blinkers_on','prize_money','priceStarting']
H = []
for y in (2025, 2026):
    h = pd.read_csv(f'/home/user/TopRate/race_results_{y}.csv.gz', usecols=lambda c: c in cols, low_memory=False); H.append(h)
H = pd.concat(H); H['date'] = pd.to_datetime(H.date); H = H.drop_duplicates(['horse_id','date']).sort_values(['horse_id','date'])
g = H.groupby('horse_id')
for c in ('weightCarried','positionFinish','marginFinish','comments_steward','comments_video'):
    H['prev_' + c] = g[c].shift(1)
H['prev_date'] = g.date.shift(1)
H['prev2_comments_steward'] = g.comments_steward.shift(2); H['prev2_comments_video'] = g.comments_video.shift(2)
H['gear_today'] = H.gear_changes.fillna('').astype(str)
T = T.merge(H[['horse_id','date','weightCarried','priceStarting','gear_today'] + [c for c in H.columns if c.startswith('prev')]], on=['horse_id','date'], how='left', suffixes=('','_h'))
T['won'] = (T.positionFinish == 1).astype(int)
T['sp'] = pd.to_numeric(T.priceStarting, errors='coerce')
EXC = r'held up|checked|hampered|blocked|no clear run|crowded|interfer|tight|steadied|disappointed for a run|lost ground|dwelt|slowly away|began awkwardly|wide without cover|three wide|four wide|raced wide|failed to handle|lost a plate|shifted|bumped|inconvenienced|unable to obtain'
txt1 = (T.prev_comments_steward.fillna('') + ' ' + T.prev_comments_video.fillna('')).str.lower()
txt2 = (T.prev2_comments_steward.fillna('') + ' ' + T.prev2_comments_video.fillna('')).str.lower()
T['f_excuse_last'] = txt1.str.contains(EXC)
T['f_traffic_last'] = txt1.str.contains(r'held up|checked|hampered|blocked|no clear run|disappointed for a run|steadied|unable to obtain')
T['f_wide_last'] = txt1.str.contains(r'wide without cover|three wide|four wide|raced wide|wide throughout')
T['f_slow_last'] = txt1.str.contains(r'slowly away|dwelt|began awkwardly|lost ground')
T['f_excuse_2back'] = txt2.str.contains(r'held up|checked|hampered|blocked|no clear run|disappointed for a run')
T['wchg'] = T.weightCarried - T.prev_weightCarried
T['f_wt_drop3'] = T.wchg <= -3
T['f_wt_up3'] = T.wchg >= 3
T['f_lightly'] = T.n <= 5
T['f_very_light'] = T.n <= 2
T['f_won_last'] = T.prev_positionFinish == 1
T['f_close_last'] = (T.prev_marginFinish > 0) & (T.prev_marginFinish <= 1.0)
T['f_rising'] = (T.last1 - T.l3) >= 3
T['f_first_up'] = T.d_last > 60
T['f_second_up'] = (T.d_last <= 60) & ((T.prev_date - T.prev_date.groupby(T.horse_id).shift(1)).dt.days > 60)
T['f_gear'] = T.gear_today.str.len() > 2
T['f_blinkers_ft'] = T.gear_today.str.lower().str.contains('blinkers first')
T['Prank'] = T.groupby('rk').P.rank(ascending=False, method='min')
T['Mrank'] = T.groupby('rk').sp.rank(method='min')
T['f_mkt_keener3'] = (T.Prank - T.Mrank) >= 3
T['f_mkt_cooler3'] = (T.Mrank - T.Prank) >= 3
T['beat5'] = T.e >= 5
flags = [c for c in T.columns if c.startswith('f_')]
base = T.beat5.mean()
print(f'{len(T)} runs in {T.rk.nunique()} complete 2026 fields; base rate of running 5+ above Proj {base:.1%}, median actual-Proj {T.e.median():+.2f}')
rows = []
for f in flags:
    m = T[f].fillna(False).astype(bool)
    rows.append(dict(flag=f[2:], share=m.mean(), n=int(m.sum()), beat5_with=T.beat5[m].mean(), beat5_without=T.beat5[~m].mean(), med_with=T.e[m].median(), med_without=T.e[~m].median(),
                     win_with=T.won[m].mean(), mean_with=T.e[m].mean(), mean_without=T.e[~m].mean()))
R = pd.DataFrame(rows).sort_values('med_with', ascending=False)
pd.set_option('display.width', 220); print(R.round(3).to_string(index=False))
# conditional logit on winner: Proj, + all flags; and market + Proj + flags (cross-fit halves)
T['half'] = (T.date >= T.date.median()).astype(int)
ok = T.groupby('rk').sp.transform(lambda s: s.notna().all() & (s > 1).all())
T2 = T[ok].copy()
gid = T2.rk.astype('category').cat.codes.values; y = T2.won.values
Pd = (T2.P - T2.groupby('rk').P.transform('mean')).values
lm = np.log((1 / T2.sp) / (1 / T2.sp).groupby(T2.rk).transform('sum')).values
F = T2[flags].fillna(False).astype(float).values
def run(X):
    out = []
    for h in (0, 1):
        tr = np.where(T2.half.values != h)[0]; te = np.where(T2.half.values == h)[0]
        def ll(b, idx):
            z = X[idx] @ b; z = z - pd.Series(z).groupby(gid[idx]).transform('max').values; e = np.exp(z)
            return -(np.log(e / pd.Series(e).groupby(gid[idx]).transform('sum').values)[y[idx] == 1]).mean() + 1e-3 * (b[1:] ** 2).sum()
        b = minimize(ll, np.r_[0.2, np.zeros(X.shape[1] - 1)], args=(tr,), method='L-BFGS-B').x
        z = X[te] @ b; z = z - pd.Series(z).groupby(gid[te]).transform('max').values; e = np.exp(z)
        p = e / pd.Series(e).groupby(gid[te]).transform('sum').values
        out.append(pd.Series(np.log(p)[y[te] == 1], index=gid[te][y[te] == 1]))
    return pd.concat(out).sort_index(), b
nf = [f for f in flags if not f.startswith('f_mkt')]
Fn = T2[nf].fillna(False).astype(float).values
a, _ = run(np.c_[Pd]); b2, bb = run(np.c_[Pd, Fn]); d = b2 - a
print(f'\nwinner log-lik on {T2.rk.nunique()} priced races: Proj {a.mean():.4f}; Proj + all non-market flags {b2.mean():.4f}, gain {d.mean():+.4f} (se {d.std()/np.sqrt(len(d)):.4f})')
print('   flag weights (2nd half fit):', dict(zip([f[2:] for f in nf], np.round(bb[1:], 3))))
m0, _ = run(np.c_[lm]); m1, _ = run(np.c_[lm, Pd]); m2, _ = run(np.c_[lm, Pd, Fn])
print(f'market {m0.mean():.4f}; + Proj {m1.mean():.4f} ({(m1-m0).mean():+.4f}); + Proj + flags {m2.mean():.4f} (gain over market+Proj {(m2-m1).mean():+.4f}, se {(m2-m1).std()/np.sqrt(len(m2)):.4f})')
T.to_pickle('beatflags.pkl')
