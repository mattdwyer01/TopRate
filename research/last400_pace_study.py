"""The pace the horse will face (26 Oct 2026): predict each runner's early pace, then the race tempo and who contests the lead, and ask whether that
(and the horse's own as-of sensitivity to a hot or slow tempo) predicts its last-400m deficit.
Stage 1: LightGBM on the ABSOLUTE early time deficit a_E (early time minus the par for distance and section count, so a hot race shows) from pre-race inputs;
out-of-fold (5 date blocks) before 2025, fit on all pre-2025 for the 2025-on test. Race tempo = mean predicted a_E; contest = gaps to the predicted leader.
Stage 2: add these (and fade/tempo sensitivity interactions) to the study-2 field-relative last-400m model. R2 on 2025 on.
  PYTHONPATH=. python research/last400_pace_study.py
"""
import os, sys
import lightgbm as lgb, numpy as np, pandas as pd
sys.path.insert(0, os.path.dirname(__file__))
import last400_predictors_study2 as S2
d, allc, Hc, Rc = S2.d.copy(), S2.allc, S2.Hc, S2.Rc
d = d.sort_values(['date', 'key']).reset_index(drop=True)
pre = d.date < '2025-01-01'
par = d[pre].groupby(['dist', 'n_E']).t_E.mean().rename('par_E')
d = d.merge(par, on=['dist', 'n_E'], how='left')
d['a_E'] = d.t_E - d.par_E
d = d.sort_values(['hk', 'date', 'key']).reset_index(drop=True)
g = d.groupby('hk')
lg = pd.concat([g.a_E.shift(k) for k in range(1, 5)], axis=1)
d['m4_aE'] = lg.mean(axis=1); d['s4_aE'] = lg.std(axis=1); d['p1_aE'] = lg.iloc[:, 0]
d['e8_aE'] = g.a_E.transform(lambda s: s.shift(1).ewm(halflife=3, min_periods=1).mean())
gk = d.groupby('key')
d['f_aE'] = gk.m4_aE.transform('mean'); d['f_aE_rel'] = d.m4_aE - d.f_aE; d['f_aE_rk'] = gk.m4_aE.rank(pct=True)
d['f_aE_min'] = gk.m4_aE.transform('min'); d['f_aE_gap'] = d.m4_aE - d.f_aE_min
# realised race tempo (post-race) and the horse's as-of sensitivity of its last 400m to it
d['tempo_real'] = gk.a_E.transform('mean')
d['tempo_c'] = d.tempo_real - d.groupby(['dist', 'n_E']).tempo_real.transform('mean')
xy = d.tempo_c * d.d_L; xx = d.tempo_c ** 2
cxy = d.assign(v=xy).groupby('hk').v.cumsum() - xy; cxx = d.assign(v=xx).groupby('hk').v.cumsum() - xx
d['tempo_sens'] = cxy / (cxx + 3 * xx.mean())
S1 = [c for c in allc + Hc + Rc if c in d.columns and pd.api.types.is_numeric_dtype(d[c])] + ['m4_aE', 's4_aE', 'p1_aE', 'e8_aE', 'f_aE', 'f_aE_rel', 'f_aE_rk', 'f_aE_gap']
S1 = list(dict.fromkeys(S1)) + ['trk']
d['trk'] = d.venue.astype('category')
P1 = dict(learning_rate=0.05, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.5, reg_lambda=10, verbose=-1, n_estimators=400)
ok = d.h_E.notna() & d.a_E.notna()
d['pred_aE'] = np.nan
tr_idx = d.index[ok & (d.date < '2025-01-01')]
blocks = np.array_split(tr_idx[np.argsort(d.loc[tr_idx, 'date'].values)], 5)
for b in blocks:
    rest = tr_idx.difference(b)
    m = lgb.LGBMRegressor(**P1).fit(d.loc[rest, S1], d.loc[rest, 'a_E'])
    d.loc[b, 'pred_aE'] = m.predict(d.loc[b, S1])
m = lgb.LGBMRegressor(**P1).fit(d.loc[tr_idx, S1], d.loc[tr_idx, 'a_E'])
te_idx = d.index[d.h_E.notna() & (d.date >= '2025-01-01')]
d.loc[te_idx, 'pred_aE'] = m.predict(d.loc[te_idx, S1])
te = d.loc[te_idx]; y = te.a_E.dropna(); pr = te.loc[y.index, 'pred_aE']
yr = y - te.loc[y.index].groupby('key').a_E.transform('mean'); pr_r = pr - te.loc[y.index].groupby('key').pred_aE.transform('mean')
print(f'stage 1 (2025 on): R2 absolute early deficit {1 - ((y - pr) ** 2).sum() / ((y - y.mean()) ** 2).sum():.3f}; within-race {1 - ((yr - pr_r) ** 2).sum() / ((yr - yr.mean()) ** 2).sum():.3f}', flush=True)
gk = d.groupby('key')
d['pr_tempo'] = gk.pred_aE.transform('mean')
d['pr_rel'] = d.pred_aE - d.pr_tempo
d['pr_rank'] = gk.pred_aE.rank(method='min')
d['pr_gap_lead'] = d.pred_aE - gk.pred_aE.transform('min')
d['pr_n_close'] = gk.pred_aE.transform(lambda s: (s - s.min() < 0.15).sum())
d['pr_spread'] = gk.pred_aE.transform('std')
d['pr_tempo_c'] = d.pr_tempo - d.groupby(['dist', 'n_E']).pr_tempo.transform('mean')
d['x_fade_pr'] = d.fade_slope * d.pr_rel
d['x_tempo_sens'] = d.tempo_sens * d.pr_tempo_c
d['x_fade_tempo'] = d.fade_slope * d.pr_tempo_c
PC = ['pred_aE', 'pr_tempo', 'pr_rel', 'pr_rank', 'pr_gap_lead', 'pr_n_close', 'pr_spread', 'pr_tempo_c', 'tempo_sens', 'x_fade_pr', 'x_tempo_sens', 'x_fade_tempo']
cols0 = allc + Rc
P = dict(learning_rate=0.03, num_leaves=31, min_child_samples=150, subsample=0.8, subsample_freq=1, colsample_bytree=0.5, reg_lambda=10, verbose=-1, n_estimators=3000)
tr = d[(d.date < '2024-07-01') & d.pred_aE.notna()]; va = d[(d.date >= '2024-07-01') & (d.date < '2025-01-01') & d.pred_aE.notna()]; tt = d[(d.date >= '2025-01-01') & d.pred_aE.notna()]
print(f'stage 2: fit {len(tr):,} val {len(va):,} test {len(tt):,}')
last = None
for nm, cols in (('study-2 B (field-relative)', cols0), ('+ pace the horse will face', cols0 + PC), ('+ pace and tempo sensitivity only', cols0 + ['tempo_sens', 'x_tempo_sens'])):
    out = []
    for tgt in ('L', 'T'):
        mm = lgb.LGBMRegressor(**P).fit(tr[cols], tr[f'd_{tgt}'], eval_set=[(va[cols], va[f'd_{tgt}'])], callbacks=[lgb.early_stopping(100, verbose=False)])
        p = mm.predict(tt[cols]); yy = tt[f'd_{tgt}']
        out.append(1 - ((yy - p) ** 2).sum() / ((yy - yy.mean()) ** 2).sum())
        if tgt == 'L': last = (mm, cols)
    print(f'{nm:36s} last400 {out[0]:.4f}  total {out[1]:.4f}', flush=True)
mm, cols = last
imp = pd.Series(mm.booster_.feature_importance('gain'), index=cols).sort_values(ascending=False)
print('top inputs (last variant, last 400m):'); print((100 * imp / imp.sum()).head(10).round(1).to_string())
