"""Stretch and anchor test on the live Proj structure (9 Nov 2026). Was: winner and rating test for ctx.TRIAL_FEATS (9 Nov 2026): barrier trials and jump-outs, added to both context models on top of the live inputs (incl. FIT_FEATS).
Same structure as the live Proj (projection/train_ctx.py --v2 --conv-frac 1.0: runner-page ATW ratings plus converted results-file history for TRAINING rows, option 2 inputs, Huber 4),
the relevance model fitted with and without FIT_FEATS on runs before 2026-01-01 (early stop 2025-10..12), the plain context model shared. Scored on the 2026 page runs:
rating error (all runs, 3+ earlier runs) and winner log-likelihood in races as the page store holds them (4+ runners with a Proj, winner among them, softmax scale cross-fitted on date halves).
Run: PYTHONPATH=.:projection:research PROJECTION_RATINGS=toprate python research/proj_fit_feats_test.py [--conv-frac 1.0]"""
import argparse, os, sys, json
import numpy as np, pandas as pd, lightgbm as lgb
sys.path.insert(0, 'projection'); sys.path.insert(0, 'research')
import ctx as C

ap = argparse.ArgumentParser(); ap.add_argument('--conv-frac', type=float, default=1.0); ap.add_argument('--out', default='research/proj_stretch_test.json'); a = ap.parse_args()
conv = None
if a.conv_frac > 0:
    import conv_history as CH, features as FT
    real = FT.runner_page_runs().copy()
    FT._TR_CACHE['rows'] = CH.build(2020, '2025-12-31', a.conv_frac)
    conv = C.training_frame_rel(True); conv = conv[conv.f.notna()].copy()
    FT._TR_CACHE['rows'] = real
    print('converted training rows', len(conv), flush=True)
rp = C.training_frame_rel(True)
pg = rp[rp.f.notna()].copy()
classes = sorted(pg.cls.dropna().unique().tolist()); pg['cls_c'] = C._cls(pg.cls, classes)
cut, es = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')
te = pg[pg.date >= cut].copy()
if conv is not None:
    conv['cls_c'] = C._cls(conv.cls, classes); pa = pd.concat([conv, pg], ignore_index=True)
else:
    pa = pg
tr, va = pa[pa.date < es], pa[(pa.date >= es) & (pa.date < cut)]
P = dict(n_estimators=4000, learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1, objective='huber', alpha=4.0)
fit = lambda F, t, v: lgb.LGBMRegressor(**P).fit(t[F], t.resid, eval_set=[(v[F], v.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
F0 = C.FEATS2; F1 = F0 + C.REL_FEATS2 + C.FIT_FEATS; T0 = F0 + C.TRIAL_FEATS; T1 = F1 + C.TRIAL_FEATS
rel = lambda d: d[d.n >= C.REL_MIN_RUNS]
use = (te.n >= C.REL_MIN_RUNS).values
A, B = T0, T1      # the live inputs incl. FIT_FEATS and TRIAL_FEATS
m0 = fit(A, tr, va); m1 = fit(B, rel(tr), rel(va))
c = m0.predict(te[A]); c[use] = m1.predict(te.loc[use, B])
c = np.where(use, c, np.clip(c, -2, 2))     # run.py CTX_CAP_FEW for under 3 runs
te['corr'] = c
import breakdown as BK
te['tfa'] = BK.tf_array(pd.DataFrame({'horse_id': te.horse_id.values, 'date': te.date.values, 'distance': te.distance.values, 'going': te.going.values,
                                      'weight_carried': np.nan, 'prize_money': te.prize.values if 'prize' in te.columns else np.nan}))
te['rk'] = C._race_key(te)
def proj(k, cap):
    m = te.f + np.where(use, k * te['corr'], te['corr'])
    if cap is None: return m
    return np.where(use & te.tfa.notna().values, te.tfa + np.clip(m - te.tfa, -cap, cap), m)
t = te[te.positionFinish.notna()].copy(); t = t[t.groupby('rk').f.transform('size') >= 4]
t = t[t.groupby('rk').positionFinish.transform(lambda s: (s == 1).sum()) == 1]; t['half'] = (t.date >= t.date.median()).astype(int)
def wl(col):
    def ll(df, b):
        z = b * (df[col] - df.groupby('rk')[col].transform('max')); return (z - np.log(np.exp(z).groupby(df.rk).transform('sum')))[df.positionFinish == 1]
    out = []
    for h in (0, 1):
        bs = np.arange(0.1, 0.5, 0.005); b = bs[np.argmax([ll(t[t.half != h], b).mean() for b in bs])]; out.append(ll(t[t.half == h], b))
    return pd.concat(out).sort_index()
res = {}; ref = None
for cap in (3, 5, None):
    for k in (1.0, 1.1, 1.2, 1.3):
        name = f"cap {cap if cap else 'none'}, stretch {k}"
        p = proj(k, cap); te['_p'] = p; t['_p'] = te.loc[t.index, '_p']
        e = te.wpr - p; s = wl('_p')
        if ref is None: ref = s
        d = s - ref; top = t.loc[t.groupby('rk')['_p'].idxmax()]
        e3 = e[use]
        res[name] = dict(median=round(float(np.median(np.abs(e))), 4), within3=round(float((e.abs() <= 3).mean()), 4), rmse=round(float(np.sqrt((e ** 2).mean())), 4),
                         median_3plus=round(float(np.median(np.abs(e3))), 4), win_ll=round(float(s.mean()), 5), win_ll_vs_live=round(float(d.mean()), 5),
                         se=round(float(d.std() / np.sqrt(len(d))), 5), top_pick=round(float((top.positionFinish == 1).mean()), 4))
        print(name, res[name], flush=True)
x = te['corr'][use]; y = (te.wpr - te.f)[use]
res['slope_actual_on_step_3plus'] = round(float(((x - x.mean()) * (y - y.mean())).sum() / ((x - x.mean()) ** 2).sum()), 3)
res['runs'] = int(len(te)); res['races'] = int(t.rk.nunique())
print('slope', res['slope_actual_on_step_3plus'])
json.dump(res, open(a.out, 'w'), indent=1)
