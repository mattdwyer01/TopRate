"""Does a detailed post-race review of each run (settling, race shape, closing, track bias, run comments) predict the NEXT run's rating beyond the live Proj (formula + context)?
ATW figures only (runner-page store). Baseline = ctx FEATS; candidate = FEATS + review features of the last run (and the one before).
Run: PYTHONPATH=. python research/meeting_review_test.py"""
import glob, gzip, json, os, sys
import numpy as np, pandas as pd, lightgbm as lgb
sys.path.insert(0, 'projection')
import ctx as C

rows = []
for f in sorted(glob.glob('data/tr_form/*.json.gz')):
    for r in json.load(gzip.open(f, 'rt')).get('runs', {}).values():
        if r.get('isBarrierTrial') or r.get('isJumpout') or r.get('wpr') is None:
            continue
        rows.append(dict(horse_id=r['horse_id'], date=r['date'], raceId=r.get('raceId'), meetingId=r.get('meetingId'), p800=r.get('position800m'), p600=r.get('position600m'),
                         p400=r.get('position400m'), pset=r.get('positionSettled'), m800=r.get('margin800m'), m600=r.get('margin600m'), m400=r.get('margin400m'),
                         sE=r.get('raceShapeEarly'), sM=r.get('raceShapeMid'), sL=r.get('raceShapeLate'), wt=r.get('winnersTime'), cv=(r.get('commentsVideo') or '').lower(),
                         stew=(r.get('commentsSteward') or '').lower(), price=r.get('priceStarting')))
X = pd.DataFrame(rows)
X['horse_id'] = pd.to_numeric(X.horse_id, errors='coerce'); X['date'] = pd.to_datetime(X.date)
X = X.drop_duplicates(['horse_id', 'date'], keep='last')

rp = C.training_frame()
rp = rp.merge(X, on=['horse_id', 'date'], how='left')
rp['sf'] = rp.pset / rp.field_size
rp['f600'] = rp.p600 / rp.field_size
rp['close'] = rp.m600 - rp.marginFinish.clip(lower=0)      # lengths gained over the last 600m
rp['early_m'] = rp.m800
txt = rp.cv.fillna('') + ' ' + rp.stew.fillna('')
for k, pat in dict(wide='wide|three wide|3 wide|4 wide', check='checked|bumped|held up|blocked|hampered|tightened|clipped', slow='slow|missed the start|dwelt|fumbled', hard='hard ridden|laboured|weakened|tired|faded').items():
    rp['x_' + k] = txt.str.contains(pat).astype(float)
rp['has_cv'] = (rp.cv.fillna('') != '').astype(float)
# same-meeting-day bias from the other races' top 3 (store coverage is partial)
top = rp[rp.positionFinish <= 3].copy()
g = top.groupby('meetingId')
tot = g.agg(bs=('barr_f', 'sum'), bn=('barr_f', 'count'), ps=('f600', 'sum'), pn=('f600', 'count'))
rp = rp.join(tot, on='meetingId')
own_top = (rp.positionFinish <= 3)
bs = rp.bs - np.where(own_top, rp.barr_f.fillna(0), 0); bn = rp.bn - own_top.astype(int)
ps = rp.ps - np.where(own_top & rp.f600.notna(), rp.f600, 0); pn = rp.pn - (own_top & rp.f600.notna()).astype(int)
rp['bias_barr'] = np.where(bn >= 3, bs / bn.where(bn > 0) - 0.5, np.nan)
rp['bias_pace'] = np.where(pn >= 3, ps / pn.where(pn > 0) - 0.5, np.nan)   # <0 = leaders/forward runners won the day
rp['bias_fit'] = rp.barr_f - 0.5
rp['bias_fit'] = rp.bias_fit * rp.bias_barr
rp['pace_fit'] = (rp.f600 - 0.5) * rp.bias_pace
rp['shape_fit'] = (rp.f600 - 0.5) * rp.sE          # forward in a fast-early race
REV = ['sf', 'f600', 'close', 'early_m', 'sE', 'sM', 'sL', 'x_wide', 'x_check', 'x_slow', 'x_hard', 'has_cv', 'bias_barr', 'bias_pace', 'bias_fit', 'pace_fit', 'shape_fit', 'resid_l']
rp = rp.sort_values(['horse_id', 'date']).reset_index(drop=True)
rp['resid_l'] = np.nan
g = rp.groupby('horse_id')
rp['resid_l'] = g.resid.shift(1)
L1 = [c for c in REV if c != 'resid_l']
for c in L1:
    rp[c + '_L1'] = g[c].shift(1)
    rp[c + '_L2'] = g[c].shift(2)
rp['has_review'] = rp[[c + '_L1' for c in ['sf', 'sE', 'close']]].notna().any(axis=1)
NEW = [c + '_L1' for c in L1] + [c + '_L2' for c in ['sf', 'f600', 'close', 'sE', 'sL', 'x_check', 'x_wide']]
classes = sorted(rp.cls.dropna().unique().tolist())
rp['cls_c'] = C._cls(rp.cls, classes)
pg = rp[rp.f.notna()].copy()
print('rows', len(pg), 'with last-run review fields', int(pg.has_review.sum()), 'coverage by year:')
print(pg.groupby(pg.date.dt.year).has_review.mean().round(2).to_string())
cut, es = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')
tr, va, te = pg[pg.date < es], pg[(pg.date >= es) & (pg.date < cut)], pg[pg.date >= cut]
P = dict(n_estimators=3000, learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1)

def fit(feats, seed):
    m = lgb.LGBMRegressor(**P, random_state=seed)
    m.fit(tr[feats], tr.resid, eval_set=[(va[feats], va.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
    return m, m.predict(te[feats])
res = {}
for name, feats in (('ctx', C.FEATS), ('ctx+review', C.FEATS + NEW)):
    ps_ = []
    for s in range(3):
        m, p = fit(feats, s); ps_.append(p)
    res[name] = np.mean(ps_, axis=0)
    e = te.resid - res[name]
    print(f'{name:11s} trees~{m.best_iteration_} RMSE {np.sqrt((e**2).mean()):.4f}')
    if name == 'ctx+review':
        imp = pd.Series(m.booster_.feature_importance('gain'), index=feats).sort_values(ascending=False)
        print((imp / imp.sum()).head(12).round(3).to_string())
e0, e1 = te.resid - res['ctx'], te.resid - res['ctx+review']
d = e0**2 - e1**2
print('paired MSE gain per run', d.mean().round(4), 'se', (d.std() / np.sqrt(len(d))).round(4), ' RMSE', np.sqrt((e0**2).mean()).round(4), '->', np.sqrt((e1**2).mean()).round(4))
sub = te.has_review.values
print('on runs whose last run has review fields: n', sub.sum(), 'RMSE', np.sqrt((e0[sub]**2).mean()).round(4), '->', np.sqrt((e1[sub]**2).mean()).round(4))
# simple univariate checks: do the review features predict the NEXT run's ctx-residual?
te = te.assign(r0=e0)
print('\ncorr of next-run residual (after live Proj) with last-run review features (2026 held out):')
for c in L1:
    v = te[[c + '_L1', 'r0']].dropna()
    if len(v) > 500:
        print(f'  {c:10s} n={len(v):6d} corr {v.corr().iloc[0,1]:+.3f}')
