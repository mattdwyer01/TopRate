"""If settling, race shape and run comments were known BEFORE the race, would the live Proj (formula + context, ATW runner-page ratings) have been better, and how much of
that can be known beforehand? Target = the run's own ATW rating minus the formula (as projection/train_ctx.py). Baseline = ctx FEATS.
A (upper bound, uses the target run's own data): + own settle fraction at 800m, TopRate race shape (early / mid / late), trouble comments (wide / checked / slow away).
 NOT used: margins and the 400m position (the rating is computed from the margins, so they give away the answer: first run of this test showed RMSE 3.9, a leak) and finish-describing comments (weakened, tired). Not knowable pre-race; it measures how much of the miss is shape and trouble.
B (knowable): + history of the horse's own settling (mean and last of earlier runs' settle fraction, its closing gain, comment-trouble rate in earlier runs).
C (knowable, race context): B + the field's pace pressure from those histories (share of the stored runners that usually lead) and the horse's style x pressure.
D (predicted shape): replace A's own settle with a prediction from B/C features (out of sample) to see what is left when we only know the predicted shape.
Run: PYTHONPATH=. python research/shape_counterfactual.py"""
import glob, gzip, json, sys
import numpy as np, pandas as pd, lightgbm as lgb
sys.path.insert(0, 'projection')
import ctx as C

rows = []
for f in sorted(glob.glob('data/tr_form/*.json.gz')):
    for r in json.load(gzip.open(f, 'rt')).get('runs', {}).values():
        if r.get('isBarrierTrial') or r.get('isJumpout') or r.get('wpr') is None:
            continue
        rows.append(dict(horse_id=r['horse_id'], date=r['date'], raceId=r.get('raceId'), p800=r.get('position800m'), p400=r.get('position400m'), m800=r.get('margin800m'),
                         m600=r.get('margin600m'), sE=r.get('raceShapeEarly'), sM=r.get('raceShapeMid'), sL=r.get('raceShapeLate'),
                         cv=((r.get('commentsVideo') or '') + ' ' + (r.get('commentsSteward') or '')).lower()))
X = pd.DataFrame(rows); X['horse_id'] = pd.to_numeric(X.horse_id, errors='coerce'); X['date'] = pd.to_datetime(X.date)
rp = C.training_frame().merge(X.drop_duplicates(['horse_id', 'date'], keep='last'), on=['horse_id', 'date'], how='left')
rp['sf'] = rp.p800 / rp.field_size
rp['sf4'] = rp.p400 / rp.field_size
rp['gain'] = rp.m800 - rp.marginFinish.clip(lower=0)
for k, pat in dict(wide='wide', check='checked|bumped|held up|blocked|hampered|tightened|clipped', slow='slow|missed the start|dwelt|fumbled', hard='hard ridden|laboured|weakened|tired|faded|no extra').items():
    rp['x_' + k] = rp.cv.str.contains(pat).astype(float)
rp['trouble'] = ((rp.x_wide + rp.x_check + rp.x_slow) > 0).astype(float)
rp = rp.sort_values(['horse_id', 'date']).reset_index(drop=True)
g = rp.groupby('horse_id')
# B: history (earlier runs only)
rp['h_sf_last'] = g.sf.shift(1)
rp['h_sf_mean3'] = g.sf.transform(lambda s: s.shift(1).rolling(3, min_periods=1).mean())
rp['h_sf_sd'] = g.sf.transform(lambda s: s.shift(1).rolling(4, min_periods=2).std())
rp['h_gain_mean3'] = g.gain.transform(lambda s: s.shift(1).rolling(3, min_periods=1).mean())
rp['h_trouble3'] = g.trouble.transform(lambda s: s.shift(1).rolling(3, min_periods=1).mean())
rp['h_sf_n'] = g.sf.transform(lambda s: s.shift(1).notna().cumsum())
HIST = ['h_sf_last', 'h_sf_mean3', 'h_sf_sd', 'h_gain_mean3', 'h_trouble3']
# C: field pace pressure from the stored runners' histories in the same race
rp['leader_hist'] = (rp.h_sf_mean3 < 0.3).astype(float).where(rp.h_sf_mean3.notna())
gr = rp.groupby('raceId')
rp['n_hist'] = gr.leader_hist.transform('count')
rp['pressure'] = (gr.leader_hist.transform('sum') - rp.leader_hist.fillna(0)) / (rp.n_hist - rp.leader_hist.notna().astype(int)).replace(0, np.nan)
rp['style_x_press'] = (0.5 - rp.h_sf_mean3) * rp.pressure
CTX = ['pressure', 'style_x_press', 'n_hist']
OWN = ['sf', 'sE', 'sM', 'sL', 'x_wide', 'x_check', 'x_slow']
rp['cls_c'] = C._cls(rp.cls, sorted(rp.cls.dropna().unique().tolist()))
pg = rp[rp.f.notna()].copy()
cut, es = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')
tr, va, te = pg[pg.date < es], pg[(pg.date >= es) & (pg.date < cut)], pg[pg.date >= cut].copy()
P = dict(n_estimators=3000, learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1)
def fit(feats, target='resid', frame_tr=None, frame_va=None, frame_te=None, seeds=3):
    a, b, c = frame_tr if frame_tr is not None else tr, frame_va if frame_va is not None else va, frame_te if frame_te is not None else te
    p = []
    for s in range(seeds):
        m = lgb.LGBMRegressor(**P, random_state=s).fit(a[feats], a[target], eval_set=[(b[feats], b[target])], callbacks=[lgb.early_stopping(100, verbose=False)])
        p.append(m.predict(c[feats]))
    return np.mean(p, axis=0)
def rmse(e): return float(np.sqrt(np.mean(e ** 2)))
cov = te[OWN].notna().mean().round(2).to_dict(); print('held-out runs', len(te), 'own-shape coverage', cov)
base = fit(C.FEATS); e0 = te.resid.values - base
print(f'baseline (live Proj context model)           RMSE {rmse(e0):.4f}')
def report(name, feats, restrict=None, **kw):
    p = fit(feats, **kw); e = te.resid.values - p
    m = np.ones(len(te), bool) if restrict is None else restrict
    d = e0[m] ** 2 - e[m] ** 2
    print(f'{name:44s} RMSE {rmse(e[m]):.4f} (baseline on same runs {rmse(e0[m]):.4f})  paired MSE gain {d.mean():+.2f} +-{1.96 * d.std() / np.sqrt(m.sum()):.2f}')
    return p
has_own = te.sf.notna().values
report('A upper bound: own settle + shape + trouble', C.FEATS + OWN, has_own)
report('  A1 only own settle position at 800m', C.FEATS + ['sf'], has_own)
report('  A2 only TopRate race shape (early/mid/late)', C.FEATS + ['sE', 'sM', 'sL'], has_own)
report('  A2b settle x race shape (front runner in a fast/slow early)', C.FEATS + ['sf', 'sE', 'sM', 'sL'], has_own)
report('  A3 only trouble comments (wide/checked/slow away)', C.FEATS + ['x_wide', 'x_check', 'x_slow'], has_own)
report('B knowable: horse settling history', C.FEATS + HIST, te.h_sf_last.notna().values)
report('C knowable: + field pace pressure', C.FEATS + HIST + CTX, te.pressure.notna().values)
# D: predicted own settle from history/context, then fed to the Proj model in place of the actual
pg2 = pg[pg.sf.notna() & pg.h_sf_last.notna()].copy()
cols = HIST + CTX + ['barr_f', 'field_size', 'distance', 'going_n', 'cls_c', 'jock_eff', 'n']
t2, v2, e2 = pg2[pg2.date < es], pg2[(pg2.date >= es) & (pg2.date < cut)], pg2[pg2.date >= cut]
ps = fit(cols, 'sf', t2, v2, e2)
print(f'\npredict own settle fraction from history/barrier/field: held-out R2 {1 - ((e2.sf - ps) ** 2).sum() / ((e2.sf - e2.sf.mean()) ** 2).sum():.3f}, corr {np.corrcoef(ps, e2.sf)[0, 1]:.3f}')
# out-of-sample prediction for ALL rows (train rows get a cross-fitted value by date blocks so the Proj model never sees its own fit)
pg['sf_pred'] = np.nan
blocks = pd.cut(pg.date, bins=6, labels=False)
for b in range(6):
    trn = pg2[(blocks.loc[pg2.index] != b)]; val = pg2[(blocks.loc[pg2.index] == b)]
    if len(val) == 0: continue
    pg.loc[val.index, 'sf_pred'] = fit(cols, 'sf', trn, val.iloc[:2000] if len(val) > 2000 else val, val, seeds=1)
tr, va, te = pg[pg.date < es], pg[(pg.date >= es) & (pg.date < cut)], pg[pg.date >= cut].copy()
base = fit(C.FEATS); e0 = te.resid.values - base
m = te.sf_pred.notna().values
p = fit(C.FEATS + ['sf_pred'], seeds=3); e = te.resid.values - p
d = e0[m] ** 2 - e[m] ** 2
print(f'D predicted settle as a Proj input              RMSE {rmse(e[m]):.4f} (baseline {rmse(e0[m]):.4f})  paired MSE gain {d.mean():+.2f} +-{1.96 * d.std() / np.sqrt(m.sum()):.2f}  n={m.sum()}')
