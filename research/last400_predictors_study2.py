"""Second pass at predicting the last 400m before the race (26 Oct 2026): owner doubts the ceiling, so push the pre-race model.
Adds to last400_predictors_study.build(): (R) every numeric input also as the runner minus the field mean and the rank in the field (the target is
a deficit against the race mean, so ability and history relative to the field should matter more than absolute levels); (H) longer history
(8 lags, EWM of E/M/L/T deficits, EWM of TopRate sectionals); (F) fade sensitivity (shrunk as-of slope of the horse's L on its own E) and the
field's expected tempo; then early stopping on a 2024 validation slice. R2 on 2025 on.
  PYTHONPATH=. python research/last400_predictors_study2.py
"""
import os, sys
import lightgbm as lgb, numpy as np, pandas as pd
sys.path.insert(0, os.path.dirname(__file__))
import last400_predictors_study as S

d, base, fam = S.build()
allc = base + [x for v in fam.values() for x in v]
allc = [c for c in dict.fromkeys(allc) if c != 'trk']
d['trk'] = d.venue.astype('category')
g = d.groupby('hk')
# H: longer history
new = {}
for c in ('E', 'M', 'L', 'T'):
    x = g[f'd_{c}']
    new[f'e8_{c}'] = x.transform(lambda s: s.shift(1).ewm(halflife=3, min_periods=1).mean())
    new[f'm8_{c}'] = pd.concat([x.shift(k) for k in range(1, 9)], axis=1).mean(axis=1)
    new[f's8_{c}'] = pd.concat([x.shift(k) for k in range(1, 9)], axis=1).std(axis=1)
for c in ('sect_i_l400', 'sect_i_l200', 'wpr', 'cg'):
    src = d.groupby('hk')[f'm4_{c}'] if False else None
# F: fade sensitivity as-of: slope of L on E over earlier runs, shrunk
xy = (d.d_E * d.d_L); xx = d.d_E ** 2
cxy = d.assign(v=xy).groupby('hk').v.cumsum() - xy
cxx = d.assign(v=xx).groupby('hk').v.cumsum() - xx
new['fade_slope'] = cxy / (cxx + 0.5)
new['h_E_pred_fade'] = new['fade_slope'] * d.h_E
d = pd.concat([d, pd.DataFrame(new)], axis=1)
d['f_tempo'] = d.groupby('key').h_E.transform('mean')
d['E_vs_tempo'] = d.h_E - d.f_tempo
d['fade_x_tempo'] = d.fade_slope * d.f_tempo
Hc = list(new) + ['f_tempo', 'E_vs_tempo', 'fade_x_tempo']
# R: relative-to-field versions
num = [c for c in allc + Hc if c in d.columns and pd.api.types.is_numeric_dtype(d[c]) and c not in ('dist', 'nr', 'barfrac')]
rel = {}
gk = d.groupby('key')
for c in num:
    m = gk[c].transform('mean')
    rel['r_' + c] = d[c] - m
    rel['k_' + c] = gk[c].rank(pct=True)
d = pd.concat([d, pd.DataFrame(rel)], axis=1)
Rc = list(rel)
P = dict(learning_rate=0.03, num_leaves=31, min_child_samples=150, subsample=0.8, subsample_freq=1, colsample_bytree=0.5, reg_lambda=10, verbose=-1, n_estimators=3000)
tr = d[(d.date < '2024-07-01') & d.h_E.notna()]
va = d[(d.date >= '2024-07-01') & (d.date < '2025-01-01') & d.h_E.notna()]
te = d[(d.date >= '2025-01-01') & d.h_E.notna()]
print(f'fit {len(tr):,} val {len(va):,} test {len(te):,}')


def run(cols, c):
    m = lgb.LGBMRegressor(**P).fit(tr[cols], tr[f'd_{c}'], eval_set=[(va[cols], va[f'd_{c}'])], callbacks=[lgb.early_stopping(100, verbose=False)])
    pr = m.predict(te[cols]); y = te[f'd_{c}']
    return 1 - ((y - pr) ** 2).sum() / ((y - y.mean()) ** 2).sum(), m
sets = [('A  study-1 inputs, tuned', allc), ('B  + relative to field', allc + Rc), ('C  + long history, fade, tempo', allc + Hc), ('D  everything', allc + Hc + Rc)]
print(f'{"inputs":34s} {"R2 last400":>10s} {"R2 total":>9s}')
last = None
for nm, cols in sets:
    a, m = run(cols, 'L'); b, _ = run(cols, 'T')
    print(f'{nm:34s} {a:10.4f} {b:9.4f}', flush=True)
    last = (m, cols)
imp = pd.Series(last[0].booster_.feature_importance('gain'), index=last[1]).sort_values(ascending=False)
print('\ntop inputs (D, last 400m):'); print((100 * imp / imp.sum()).head(15).round(1).to_string())
