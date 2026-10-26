"""Third pass (26 Oct 2026): train the closing-stage model on ALL states and years, then use it on the VIC/SA GPS runs.
The GPS set is small (65k fit runs). TopRate's results files carry position/margin at 400m and the finish for every run (2019-2024, all states, ~75%
filled), so closing gain cg = margin at 400m minus finish margin (lengths, race-demeaned) is a proxy target with ~10x the data. Train before 2025 with
early stopping on 2024 H2, report R2 on 2025 on, then add the prediction to the GPS last-400m model (stacked, fit on 2025 H1, scored on 2025 H2).
  PYTHONPATH=. python research/last400_bigdata_study.py
"""
import glob, os, sys
import lightgbm as lgb, numpy as np, pandas as pd
sys.path.insert(0, os.path.dirname(__file__))
import closing_stage_study as CS
import last400_predictors_study as S
ROOT = CS.ROOT
cols = ['race_id', 'horse', 'horse_id', 'date', 'distance', 'going', 'wpr', 'weightCarried', 'barrier', 'margin400m', 'marginFinish', 'sect_i_l400', 'sect_i_l200',
        'sect_i_early', 'race_class', 'jockey', 'trainer', 'field_size', 'isBarrierTrial', 'is_jumpout', 'track', 'horse_age', 'positionFinish']
fs = sorted(glob.glob(os.path.join(ROOT, 'race_results_20[12]?.csv.gz')))
r = pd.concat([pd.read_csv(f, usecols=lambda c: c in cols, low_memory=False) for f in fs], ignore_index=True)
r = r[~r.isBarrierTrial.astype(bool) & ~r.is_jumpout.fillna(False).astype(bool)]
r['date'] = pd.to_datetime(r.date)
r = r[r.date >= '2020-01-01'].drop_duplicates(['race_id', 'horse_id']).sort_values(['horse_id', 'date', 'race_id']).reset_index(drop=True)
r['hk'] = CS.clean(r.horse)
r['cg'] = r.margin400m.clip(0, 40) - r.marginFinish.clip(0, 40)
r['gs'] = pd.to_numeric(r.going.astype(str).str.extract(r'(\d+)')[0], errors='coerce')
for c in ('wpr', 'cg', 'sect_i_l400', 'sect_i_l200', 'sect_i_early', 'weightCarried'):
    r[c + '_r'] = r[c] - r.groupby('race_id')[c].transform('mean')
r['nr'] = r.groupby('race_id').horse_id.transform('size')
r = r[r.nr >= 8].copy()
r['barfrac'] = (r.barrier - 1) / (r.nr - 1)
g = r.groupby('horse_id')
F = {}
for c in ('cg_r', 'sect_i_l400_r', 'sect_i_l200_r', 'sect_i_early_r', 'wpr_r', 'marginFinish'):
    lg = pd.concat([g[c].shift(k) for k in range(1, 9)], axis=1)
    F['p1_' + c] = lg.iloc[:, 0]; F['m4_' + c] = lg.iloc[:, :4].mean(axis=1); F['m8_' + c] = lg.mean(axis=1); F['s8_' + c] = lg.std(axis=1)
F['days'] = g.date.diff().dt.days
F['wchg'] = r.weightCarried - g.weightCarried.shift(1)
F['dchg'] = r.distance - g.distance.shift(1)
F['n_runs'] = g.cumcount().astype(float)
F = pd.DataFrame(F)
d = pd.concat([r, F], axis=1)
d['trk'] = d.track.astype('category')
hist = list(F.columns)
rel = {}
gk = d.groupby('race_id')
for c in [x for x in hist if x.startswith(('m4_', 'm8_', 'p1_'))]:
    rel['r_' + c] = d[c] - gk[c].transform('mean')
    rel['k_' + c] = gk[c].rank(pct=True)
d = pd.concat([d, pd.DataFrame(rel)], axis=1)
# as-of jockey/trainer closing effect
d['cgj'], _ = S.asof_rate(d.assign(kj=d.jockey.astype(str)), 'kj', None, prior=0.0, k=50, value='cg_r')
d['cgt'], _ = S.asof_rate(d.assign(kt=d.trainer.astype(str)), 'kt', None, prior=0.0, k=50, value='cg_r')
feats = hist + list(rel) + ['cgj', 'cgt', 'distance', 'barfrac', 'nr', 'gs', 'weightCarried', 'horse_age']
d = d.sort_values(['date', 'race_id']).reset_index(drop=True)
P = dict(learning_rate=0.05, num_leaves=63, min_child_samples=200, subsample=0.7, subsample_freq=1, colsample_bytree=0.5, reg_lambda=10, verbose=-1, n_estimators=1500)
ok = d.cg_r.notna() & d.m4_cg_r.notna()
tr = d[ok & (d.date < '2024-07-01')]; va = d[ok & (d.date >= '2024-07-01') & (d.date < '2025-01-01')]; te = d[ok & (d.date >= '2025-01-01')]
print(f'closing-gain proxy: fit {len(tr):,} val {len(va):,} test {len(te):,}; sd {te.cg_r.std():.2f} lengths', flush=True)
Xc = feats + ['trk']
m = lgb.LGBMRegressor(**P).fit(tr[Xc], tr.cg_r, eval_set=[(va[Xc], va.cg_r)], callbacks=[lgb.early_stopping(50, verbose=False)])
pr = m.predict(te[Xc])
print(f'R2 closing gain (all states, 2025 on): {1 - ((te.cg_r - pr) ** 2).sum() / ((te.cg_r - te.cg_r.mean()) ** 2).sum():.3f}', flush=True)
d['pred_cg'] = np.nan
d.loc[d.date >= '2025-01-01', 'pred_cg'] = m.predict(d.loc[d.date >= '2025-01-01', Xc])
# stack onto the GPS model, evaluated inside 2025 only (H1 fit, H2 score) so the proxy prediction is out of sample for every row used
G, base, fam = S.build()
G = G.merge(d[['hk', 'date', 'pred_cg']].drop_duplicates(['hk', 'date']), on=['hk', 'date'], how='left')
G25 = G[(G.date >= '2025-01-01') & G.h_E.notna() & G.pred_cg.notna()].copy()
G25['r_pred_cg'] = G25.pred_cg - G25.groupby('key').pred_cg.transform('mean')
print(f'GPS rows in 2025 with proxy prediction: {len(G25):,}; corr(d_L, pred_cg) = {G25.d_L.corr(G25.pred_cg):+.3f}, field-relative {G25.d_L.corr(G25.r_pred_cg):+.3f}')
cut = G25.date.quantile(0.5)
a = G25[G25.date <= cut]; b = G25[G25.date > cut]
allc = [c for c in dict.fromkeys(base + [x for v in fam.values() for x in v]) if c != 'trk']
Q = dict(learning_rate=0.05, num_leaves=15, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=10, verbose=-1, n_estimators=200)
for nm, cc in (('GPS-only inputs', allc), ('+ all-state closing proxy', allc + ['pred_cg', 'r_pred_cg']), ('proxy only', ['pred_cg', 'r_pred_cg'])):
    mm = lgb.LGBMRegressor(**Q).fit(a[cc], a.d_L); p = mm.predict(b[cc])
    print(f'{nm:30s} R2 last400 on 2025 H2: {1 - ((b.d_L - p) ** 2).sum() / ((b.d_L - b.d_L.mean()) ** 2).sum():.3f}')
