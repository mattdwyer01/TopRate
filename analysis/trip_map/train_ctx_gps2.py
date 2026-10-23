"""Rich GPS profile inside the Huber-4 context Proj training, then per-run accuracy and model-only winner accuracy (23 Oct 2026).
Inputs added to the shipped feature set (analysis/trip_map/gps_profile.py builds them): the horse's running profile as of the race (early, mid and finishing speed, kick, fade, peak speed,
positions at 800 / 400 / 0 to go, positions gained, lane at 800 / 400, lane drift, stride late; mean of the last 3 and last 8 GPS runs) and the race set-up from the whole field's profiles
(rivals with faster early speed, own gap to the fastest other runner, field mean and spread of early speed, rivals with a stronger kick, rivals usually further forward at 800m).
Same folds and params as projection/train_ctx.py (fit before 2025 and before 2026). Baseline = /tmp/train_ctx_gps_oos.parquet (shipped features).
Run: PYTHONPATH=. python analysis/trip_map/train_ctx_gps2.py"""
import os, sys
import numpy as np, pandas as pd, lightgbm as lgb
from scipy.optimize import minimize_scalar
sys.path.insert(0, os.path.dirname(__file__)); sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'projection'))
import build_trip_map as B
import ctx as C
OUT = '/tmp/train_ctx_gps2_oos.parquet'
H = pd.read_parquet('/tmp/gps_profile_hist.parquet'); H['hdate'] = H.hdate.astype('datetime64[ns]'); H = H.sort_values('hdate')
PFH = [c for c in H.columns if c.startswith(('pf3_', 'pf8_'))] + ['pf_n']
if not os.path.exists(OUT):
    # race set-up from every runner's history as of each race
    res = B.load_results()[['race_id', 'hn', 'date']].drop_duplicates(['race_id', 'hn'])
    res['date'] = pd.to_datetime(res.date).astype('datetime64[ns]'); res = res[res.date >= '2019-06-01'].sort_values('date')
    res = pd.merge_asof(res, H, left_on='date', right_on='hdate', by='hn', allow_exact_matches=False, tolerance=pd.Timedelta(days=900))
    g = res.groupby('race_id')
    PRESS = []
    for m, nm in (('pf3_z_early', 'early'), ('pf3_kick', 'kick'), ('pf3_pos_s800_pct', 'pos800'), ('pf3_z_fin', 'fin')):
        res[f'pr_{nm}_cov'] = g[m].transform('count')
        res[f'pr_{nm}_mean'] = g[m].transform('mean'); res[f'pr_{nm}_sd'] = g[m].transform('std')
        tmp = res[['race_id', m]].dropna().sort_values(['race_id', m], ascending=[True, False]); tmp['r'] = tmp.groupby('race_id').cumcount()
        t1 = tmp[tmp.r == 0].set_index('race_id')[m]; t2 = tmp[tmp.r == 1].set_index('race_id')[m]
        top1, top2 = res.race_id.map(t1), res.race_id.map(t2)
        best_other = np.where(res[m] == top1, top2, top1)
        res[f'pr_{nm}_gap_best'] = res[m] - best_other
        asc = nm in ('pos800',)             # for position share, SMALLER = further forward
        res[f'pr_{nm}_rivals_ahead'] = (g[m].rank(ascending=asc, method='min') - 1).where(res[m].notna())
        PRESS += [f'pr_{nm}_cov', f'pr_{nm}_mean', f'pr_{nm}_sd', f'pr_{nm}_gap_best', f'pr_{nm}_rivals_ahead']
    res = res.drop_duplicates(['hn', 'date'])[['hn', 'date'] + PRESS]
    res.to_parquet('/tmp/gps_pressure_feats.parquet'); print('pressure features', len(res), flush=True)
    rp = C.training_frame_rel(); pg = rp[rp.f.notna()].copy()
    classes = sorted(pg.cls.dropna().unique().tolist()); pg['cls_c'] = C._cls(pg.cls, classes)
    pg['hn'] = B.clean_name(pg.horse); pg['date'] = pd.to_datetime(pg.date).dt.normalize().astype('datetime64[ns]')
    pg = pg.sort_values('date')
    pg = pd.merge_asof(pg, H, left_on='date', right_on='hdate', by='hn', allow_exact_matches=False, tolerance=pd.Timedelta(days=900)).drop(columns='hdate')
    pg = pg.merge(res, on=['hn', 'date'], how='left')
    params = dict(n_estimators=4000, learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1, objective='huber', alpha=4.0)
    F0, F1 = C.FEATS, C.FEATS + C.REL_FEATS
    for c in ('cA', 'cB'): pg[c] = np.nan
    for cut_, es_, hi_ in (('2025-01-01', '2024-10-01', '2026-01-01'), ('2026-01-01', '2025-10-01', '2099-01-01')):
        cut, es, hi = map(pd.Timestamp, (cut_, es_, hi_))
        tr, va = pg[pg.date < es], pg[(pg.date >= es) & (pg.date < cut)]; te = pg[(pg.date >= cut) & (pg.date < hi)]
        rel = lambda d: d[d.n >= C.REL_MIN_RUNS]
        def fit(feats, a, b):
            m = lgb.LGBMRegressor(**params); m.fit(a[feats], a.resid, eval_set=[(b[feats], b.resid)], callbacks=[lgb.early_stopping(100, verbose=False)]); return m
        use = (te.n >= C.REL_MIN_RUNS).values
        for tag, extra in (('cA', PFH), ('cB', PFH + PRESS)):
            m0 = fit(F0 + extra, tr, va); m1 = fit(F1 + extra, rel(tr), rel(va))
            c = m0.predict(te[F0 + extra]); c[use] = m1.predict(te.loc[use, F1 + extra]); pg.loc[te.index, tag] = c
            print('fold', cut_, tag, 'trees', m0.best_iteration_, m1.best_iteration_, flush=True)
    pg = pg[pg.cA.notna()].copy(); pg['projA'] = pg.f + pg.cA; pg['projB'] = pg.f + pg.cB
    pg[['horse_id', 'date', 'hn', 'wpr', 'projA', 'projB', 'n', 'positionFinish', 'priceStarting'] + PFH[:3]].to_parquet(OUT)
a = pd.read_parquet(OUT); b = pd.read_parquet('/tmp/train_ctx_gps_oos.parquet')[['horse_id', 'date', 'proj0', 'half', 'rid', 'rank_prior']]
b['date'] = pd.to_datetime(b.date); a['date'] = pd.to_datetime(a.date)
m = a.merge(b, on=['horse_id', 'date'], how='inner'); m = m[m.date >= '2026-01-01']
for k in ('0', 'A', 'B'): m['miss' + k] = m.wpr - m['proj' + k]
def st(e): return f'MAE {e.abs().mean():.3f} within3 {100 * (e.abs() <= 3).mean():.1f}% rmse {np.sqrt((e ** 2).mean()):.3f}'
def pair(e0, e1):
    d = e0.abs() - e1.abs(); s = e0 ** 2 - e1 ** 2
    return f'abs gain {d.mean():+.4f} (se {d.std() / np.sqrt(len(d)):.4f}), sq gain {s.mean():+.4f} (se {s.std() / np.sqrt(len(s)):.4f})'
print('\nPER RUN, 2026 held out (miss = actual rating - Proj)')
cov = m.pf3_z_early.notna() | m.pf3_kick.notna() if 'pf3_kick' in m else m.pf3_z_early.notna()
for lab, d in (('all runs', m), ('3+ earlier runs', m[m.n >= 3]), ('top half by prior', m[m.half == True]), ('runs with GPS profile history', m[m.pf3_z_early.notna()]), ('top half with profile history', m[(m.half == True) & m.pf3_z_early.notna()])):
    print(f'  {lab:32s} n={len(d):6d}\n     shipped : {st(d.miss0)}\n     +profile: {st(d.missA)}   {pair(d.miss0, d.missA)}\n     +profile+race set-up: {st(d.missB)}   {pair(d.miss0, d.missB)}')
# winners, model only, partial fields
w = m[m.rid.notna() & m.priceStarting.notna()].copy()
w['win'] = (w.positionFinish == 1).astype(int)
gb = w.groupby('rid'); w = w[(gb.win.transform('sum') == 1) & (gb.win.transform('size') >= 5)].copy()
def beta_ll(col):
    def f(b):
        s = b * (w[col] - w.groupby('rid')[col].transform('mean')); mx = s.groupby(w.rid).transform('max'); ex = np.exp(s - mx); den = ex.groupby(w.rid).transform('sum')
        return -np.log(ex / den)[w.win == 1].sum()
    b = minimize_scalar(f, bounds=(0.01, 1), method='bounded').x
    s = b * (w[col] - w.groupby('rid')[col].transform('mean')); mx = s.groupby(w.rid).transform('max'); ex = np.exp(s - mx); den = ex.groupby(w.rid).transform('sum')
    return np.log(ex / den)[w.win == 1], b
l0, b0 = beta_ll('proj0')
print('\nWINNERS (model only, no price): races', w.rid.nunique(), 'runners', len(w), f'| shipped Proj LL {l0.mean():.4f} (beta {b0:.3f})')
for k, lab in (('projA', '+profile'), ('projB', '+profile+race set-up')):
    l, bb = beta_ll(k); d = l.values - l0.values
    print(f'  {lab:24s} LL {l.mean():.4f}  gain {d.mean():+.4f} (se {d.std() / np.sqrt(len(d)):.4f}) [beta in-sample {bb:.3f}; tuned on the test year, so slightly flattering]')
