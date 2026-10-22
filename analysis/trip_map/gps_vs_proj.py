"""GPS vs the live Proj (Huber alpha 4, 22 Oct 2026). Out-of-sample Proj for 2025 (models fit before 2025) and 2026 (fit before 2026), same code as
projection/train_ctx.py. miss = actual ATW rating - Proj. Questions, all judged on MAE / within-3 / RMSE of the miss, on all runs and on the top half
of each field by prior rating (contenders), second stage fit on 2025 and scored on 2026:
  A  explainers: does the run's own trip (GPS ground lost, lane, early speed; comment flags) explain its miss?  (hindsight)
  B  does the previous run's GPS trip effect predict the NEXT run's miss?
  C  pre-race: GPS history (avg ground lost / lane / early speed of earlier GPS runs), settle forecast, contention features, burn: do they cut the miss?"""
import glob, os, sys
import numpy as np, pandas as pd, lightgbm as lgb
sys.path.insert(0, os.path.dirname(__file__)); sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'projection'))
import build_trip_map as B
import ctx as C
ROOT = B.ROOT
CACHE = '/tmp/gps_vs_proj_oos.parquet'
if os.path.exists(CACHE):
    pg = pd.read_parquet(CACHE)
else:
    rp = C.training_frame_rel(); pg = rp[rp.f.notna()].copy()
    classes = sorted(pg.cls.dropna().unique().tolist()); pg['cls_c'] = C._cls(pg.cls, classes)
    params = dict(n_estimators=4000, learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1, objective='huber', alpha=4.0)
    F0, F1 = C.FEATS, C.FEATS + C.REL_FEATS
    pg['corr'] = np.nan
    for cut_, es_, hi_ in (('2025-01-01', '2024-10-01', '2026-01-01'), ('2026-01-01', '2025-10-01', '2099-01-01')):
        cut, es, hi = map(pd.Timestamp, (cut_, es_, hi_))
        tr, va = pg[pg.date < es], pg[(pg.date >= es) & (pg.date < cut)]
        te = pg[(pg.date >= cut) & (pg.date < hi)]
        rel = lambda d: d[d.n >= C.REL_MIN_RUNS]
        def fit(feats, a, b):
            m = lgb.LGBMRegressor(**params); m.fit(a[feats], a.resid, eval_set=[(b[feats], b.resid)], callbacks=[lgb.early_stopping(100, verbose=False)]); return m
        m0 = fit(F0, tr, va); m1 = fit(F1, rel(tr), rel(va))
        c0 = m0.predict(te[F0]); use = (te.n >= C.REL_MIN_RUNS).values
        c = c0.copy(); c[use] = m1.predict(te.loc[use, F1])
        pg.loc[te.index, 'corr'] = c
        print('fold', cut_, 'trees', m0.best_iteration_, m1.best_iteration_, 'n', len(te), flush=True)
    pg['proj'] = pg.f + pg['corr']; pg['miss'] = pg.wpr - pg.proj
    pg = pg[pg.date >= '2025-01-01']
    pg.to_parquet(CACHE)
pg = pg[pg['corr'].notna()].copy()
pg['hn'] = B.clean_name(pg.horse); pg['date'] = pd.to_datetime(pg.date).dt.normalize()
print('OOS Proj runs', len(pg), '| miss: mean %.2f median %.2f MAE %.3f RMSE %.3f' % (pg.miss.mean(), pg.miss.median(), pg.miss.abs().mean(), np.sqrt((pg.miss ** 2).mean())), flush=True)

# ---------------- results side: GPS per run, comments, settle history, contention
cols = ['race_id', 'horse_id', 'comments_steward', 'comments_video', 'position600m', 'position400m', 'margin600m', 'margin400m', 'positionFinish']
ex = pd.concat([pd.read_csv(f, usecols=lambda c: c in cols, low_memory=False) for f in sorted(glob.glob(os.path.join(ROOT, 'race_results_20*.csv.gz')))]).drop_duplicates(['race_id', 'horse_id'])
res = B.add_result_features(B.load_results()).merge(ex.drop(columns=['positionFinish']), on=['race_id', 'horse_id'], how='left')
res['date'] = pd.to_datetime(res.date).dt.normalize()
res['gap600'] = res.margin600m.clip(0, 30); res['gap400'] = res.margin400m.clip(0, 30)
res = res.sort_values(['horse_id', 'date', 'race_id']).reset_index(drop=True)
gh = res.groupby('horse_id')
for t in ('settle', 'gap800'):
    res[t + '_h3'] = gh[t].transform(lambda s: s.shift(1).rolling(3, min_periods=1).mean()); res[t + '_h8'] = gh[t].transform(lambda s: s.shift(1).rolling(8, min_periods=2).mean())
res['prior3'] = gh.wpr.transform(lambda s: s.shift(1).rolling(3, min_periods=2).mean())
res['rank_prior'] = res.groupby('race_id').prior3.rank(ascending=False, method='first')
res['half'] = res.rank_prior <= (res.fs / 2).round()
txt = (res.comments_steward.fillna('') + ' ' + res.comments_video.fillna('')).str.lower()
FL = {'f_wide': r'\b(?:wide|three wide|four wide|five wide|without cover|exposed|no cover)\b', 'f_blocked': r'(?:held up|blocked|checked|not clear|hampered|bumped|interfer|steadied|crowded|squeezed|shut in)',
      'f_slow': r'(?:slow(?:ly)? away|began awkward|missed the start|fumbled|dwelt|stumbled|reared)', 'f_keen': r'(?:keen|pulled|over ?raced|fought|laid out|laid in|hung)',
      'f_vet': r'(?:vet|lame|bled|bleed|arrhythm|sore|injur|tailed|distress|cardiac)', 'f_soft': r'(?:eased|not persevered|not knocked|dropped out|weak)'}
for k, p in FL.items(): res[k] = txt.str.contains(p, regex=True).astype(int)
cf = pd.read_parquet('/tmp/contention_feats.parquet')
cf = cf.drop_duplicates(['race_id', 'horse_id']); res = res.merge(cf.drop(columns=['date']), on=['race_id', 'horse_id'], how='left')
v = B.vicsa_runs(res); q = B.qld_runs(res); v['src'] = 0; q['src'] = 1
gp = pd.concat([v, q], ignore_index=True)[['race_id', 'horse_id', 'src', 'extra', 'lane', 'early']]
gp['extra_rel'] = gp.extra - gp.groupby('race_id').extra.transform('median'); gp['lane_rel'] = gp.lane - gp.groupby('race_id').lane.transform('median'); gp['early_z'] = gp.early / gp.groupby('src').early.transform('std')
a = pd.concat([pd.read_parquet(f) for f in glob.glob(os.path.join(ROOT, 'data/gps/atc_gps_runs_*.parquet'))])
a['date'] = pd.to_datetime(a.race_date); a['hn'] = B.clean_name(a.horse); gg = ['meet_code', 'race_no']
a['extra_rel'] = a.dist_vs_winner_m - a.groupby(gg).dist_vs_winner_m.transform('median'); e = -(a.first400_s - a.groupby(gg).first400_s.transform('mean')); a['early_z'] = e / e.std()
a = a[['date', 'hn', 'distance', 'extra_rel', 'early_z']]; a = a[~a.duplicated(['date', 'hn', 'distance'], keep=False)]
at = res.merge(a, on=['date', 'hn', 'distance'])[['race_id', 'horse_id', 'extra_rel', 'early_z']]; at['src'] = 2
G = pd.concat([gp[['race_id', 'horse_id', 'src', 'extra_rel', 'lane_rel', 'early_z']], at], ignore_index=True).drop_duplicates(['race_id', 'horse_id'])
res = res.merge(G, on=['race_id', 'horse_id'], how='left'); res['gps'] = res.src.notna()
res['pace'] = res.groupby('race_id').early_z.transform(lambda s: s.nlargest(3).mean() if s.notna().sum() >= 4 else np.nan)
# horse GPS history (strictly earlier GPS runs), over the full res so history is not cut by the Proj window
res = res.sort_values(['horse_id', 'date', 'race_id']).reset_index(drop=True); gh = res.groupby('horse_id')
for t in ('extra_rel', 'lane_rel', 'early_z'):
    res[t + '_h3'] = gh[t].transform(lambda s: s.shift(1).rolling(6, min_periods=1).apply(lambda w: np.nanmean(w[-3:]) if np.isfinite(w).any() else np.nan, raw=True))
    res[t + '_h8'] = gh[t].transform(lambda s: s.shift(1).rolling(12, min_periods=2).mean())
res['n_gps'] = gh.gps.transform(lambda s: s.shift(1).astype(float).fillna(0).cumsum())
res['burn_h'] = res.early_z_h3 - res.early_z_h8
res['bar_x_early'] = res.barfrac * res.early_z_h3
keep = ['hn', 'date', 'race_id', 'half', 'rank_prior', 'gps', 'extra_rel', 'lane_rel', 'early_z', 'pace', 'settle', 'gap800', 'gap600', 'gap400', 'barfrac', 'fs', 'settle_h3', 'gap800_h3', 'prior3',
        'extra_rel_h3', 'extra_rel_h8', 'lane_rel_h3', 'lane_rel_h8', 'early_z_h3', 'early_z_h8', 'n_gps', 'burn_h', 'bar_x_early'] + list(FL) + list(cf.columns.difference(['race_id', 'horse_id', 'date']))
rr = res[keep].rename(columns={'race_id': 'rid', 'barfrac': 'bf', 'fs': 'fs_res'}).drop_duplicates(['hn', 'date'])
D = pg.merge(rr, on=['hn', 'date'], how='left')
D['matched'] = D.rid.notna()
print('Proj runs matched to results rows %.1f%%, with GPS this run %.1f%%, with earlier GPS history %.1f%%' % (100 * D.matched.mean(), 100 * D.gps.fillna(False).astype(bool).mean(), 100 * (D.n_gps > 0).mean()), flush=True)
D = D[D.matched].copy(); D['gps'] = D.gps.astype(bool)
D['half'] = D.half.astype(bool)
tr_ = D[D.date < '2026-01-01']; te_ = D[D.date >= '2026-01-01']
print('second stage: train (2025)', len(tr_), 'test (2026)', len(te_), flush=True)
BASE = ['proj', 'n', 'std4', 'ldays', 'distance', 'field_size', 'barr_f', 'going_n']
P2 = dict(B.PARAMS, objective='huber', alpha=4.0, num_threads=4)
def stats(m, mask, lab):
    e = m[mask]; return f'{lab:28s} n={len(e):6d} MAE {e.abs().mean():.3f} within3 {100 * (e.abs() <= 3).mean():.1f}% rmse {np.sqrt((e ** 2).mean()):.3f} median {e.median():+.2f}'
def run(feats, trn, tst, rounds=250):
    m = lgb.train(P2, lgb.Dataset(trn[feats], trn.miss), rounds); return tst.miss - m.predict(tst[feats])
def paired(e0, e1, mask, lab):
    d = e0.abs()[mask] - e1.abs()[mask]; ds = (e0 ** 2)[mask] - (e1 ** 2)[mask]
    print(f'    {lab:26s} abs-error gain {d.mean():+.4f} (se {d.std() / np.sqrt(len(d)):.4f}), sq-error gain {ds.mean():+.4f} (se {ds.std() / np.sqrt(len(ds)):.4f}), n={len(d)}')
# ---------------- A: explain the run's own miss (hindsight)
print('\nA. same-run trip explains the miss? (second stage trained 2025, scored 2026; GPS-covered runs)')
A_tr = tr_[tr_.gps]; A_te = te_[te_.gps]
CTXA = BASE + ['bf', 'settle', 'gap800', 'gap600', 'gap400']; CMT = list(FL); GPSA = ['extra_rel', 'lane_rel', 'early_z', 'pace']
eA = {k: run(f, A_tr, A_te) for k, f in {'proj+context': CTXA, '+comments': CTXA + CMT, '+GPS': CTXA + GPSA, '+comments+GPS': CTXA + CMT + GPSA}.items()}
for lab, mask in (('all GPS runs', A_te.index == A_te.index), ('top half by prior', A_te.half.values), ('top 4 by prior', (A_te.rank_prior <= 4).values)):
    print('  ', lab)
    for k, e in eA.items(): print('    ' + stats(e, mask, k))
    paired(eA['+comments'], eA['+comments+GPS'], mask, 'GPS beyond comments')
    paired(eA['proj+context'], eA['+GPS'], mask, 'GPS beyond context')
# effect sizes: mean miss by trip bin (positive = ran better than Proj)
print('  mean miss (actual - Proj) by this run\'s trip, 2026 GPS runs:')
for lab, col, bins in (('extra ground vs race median (m)', 'extra_rel', [-99, -3, 1, 5, 10, 99]), ('lane vs race median (m)', 'lane_rel', [-99, -2, 1, 3, 6, 99]), ('early speed z', 'early_z', [-9, -1, -.3, .3, 1, 9])):
    t = A_te.groupby(pd.cut(A_te[col], bins), observed=True).miss.agg(['mean', 'median', 'size']); print('   ', lab, {str(i): (round(float(r['mean']), 2), round(float(r['median']), 2), int(r['size'])) for i, r in t.iterrows()})
# ---------------- B: previous run's GPS trip effect vs next run's miss
print('\nB. does the last run\'s GPS trip effect predict the next run\'s miss?')
mA = lgb.train(P2, lgb.Dataset(A_tr[CTXA + CMT + GPSA], A_tr.miss), 250); mC = lgb.train(P2, lgb.Dataset(A_tr[CTXA + CMT], A_tr.miss), 250)
Dall = D.sort_values(['horse_id', 'date']).reset_index(drop=True)
gz = Dall.gps & (Dall.date >= '2026-01-01')
Dall['trip_eff'] = np.nan
Dall.loc[gz, 'trip_eff'] = mA.predict(Dall.loc[gz, CTXA + CMT + GPSA]) - mC.predict(Dall.loc[gz, CTXA + CMT])
Dall['next_miss'] = Dall.groupby('horse_id').miss.shift(-1); Dall['gapd'] = (Dall.groupby('horse_id').date.shift(-1) - Dall.date).dt.days
Bq = Dall[Dall.trip_eff.notna() & Dall.next_miss.notna() & (Dall.gapd <= 120)]
print('   trip effect sd %.2f (5%% %.2f, 95%% %.2f), rows %d' % (Bq.trip_eff.std(), Bq.trip_eff.quantile(.05), Bq.trip_eff.quantile(.95), len(Bq)))
for lab, sub in (('all', Bq), ('top half', Bq[Bq.half]), ('top 4 by prior', Bq[Bq.rank_prior <= 4])):
    X = np.c_[np.ones(len(sub)), sub.trip_eff]; c = np.linalg.lstsq(X, sub.next_miss, rcond=None)[0]; r = sub.next_miss - X @ c
    print(f'    {lab:16s} n={len(sub):5d} slope of next run\'s miss on last run\'s GPS trip effect {c[1]:+.2f} (se {np.sqrt(r.var() / (len(sub) * sub.trip_eff.var())):.2f})')
# ---------------- C: pre-race features
print('\nC. pre-race GPS-derived features added to the Huber Proj (second stage trained 2025, scored 2026)')
HIST = ['extra_rel_h3', 'extra_rel_h8', 'lane_rel_h3', 'lane_rel_h8', 'early_z_h3', 'early_z_h8', 'n_gps', 'burn_h']
CONT = [c for c in D.columns if c.startswith('c_')] + ['settle_h3', 'gap800_h3', 'bf', 'bar_x_early']
sets = {'Proj + base': BASE, '+ GPS history': BASE + HIST, '+ settle/contention': BASE + CONT, '+ both': BASE + HIST + CONT}
eC = {k: run(f, tr_, te_) for k, f in sets.items()}
for lab, mask in (('all runs', np.ones(len(te_), bool)), ('runs with earlier GPS', (te_.n_gps > 0).values), ('top half by prior', te_.half.values), ('top 4 by prior', (te_.rank_prior <= 4).values), ('top half with GPS history', (te_.half & (te_.n_gps > 0)).values)):
    print('  ', lab)
    print('    ' + stats(te_.miss, mask, 'no second stage (Proj as is)'))
    for k, e in eC.items(): print('    ' + stats(e, mask, k))
    for k in list(sets)[1:]: paired(eC['Proj + base'], eC[k], mask, k + ' vs base')
