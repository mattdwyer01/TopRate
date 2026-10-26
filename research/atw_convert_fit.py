"""Fit the ATW offset (runner-page rating minus plain results wpr, constant per horse) from the conditions of the race it was struck for.
Offset c_h comes from /tmp/atw_explore.pkl (atw_convert_explore.py). The target race of a horse's latest scrape = its first live runners.csv row after its latest page run.
Run with PYTHONPATH=."""
import numpy as np, pandas as pd, lightgbm as lgb
import runners_io
M = pd.read_pickle('/tmp/atw_explore.pkl')
last = M.groupby('horse_id').agg(c=('off', 'median'), last=('date', 'max'), n=('off', 'size')).reset_index()
rn = runners_io.read_runners()
rn = rn[rn.scratched.fillna(0) != 1].copy()
rn['date'] = rn.date.astype(str).str[:10]
rn['horse_id'] = pd.to_numeric(rn.horse_id, errors='coerce')
print([c for c in rn.columns if 'weight' in c or 'age' in c or 'sex' in c])
rn = rn.sort_values(['horse_id', 'date'])
T = last.merge(rn, on='horse_id')
T = T[T.date > T['last']].drop_duplicates('horse_id')
print(len(last), len(T))
T['wt'] = pd.to_numeric(T.weight_carried, errors='coerce')
T['age'] = pd.to_numeric(T.horse_age, errors='coerce')
T['sex'] = T.horse_sex.astype(str).str.upper().str[:1].map({'C': 0, 'G': 1, 'H': 2, 'F': 3, 'M': 4, 'R': 5}).fillna(-1)
T['month'] = pd.to_datetime(T.date).dt.month
T['dist'] = pd.to_numeric(T.distance, errors='coerce')
T['doy'] = pd.to_datetime(T.date).dt.dayofyear
print(T[['wt', 'age', 'sex', 'dist']].notna().mean())
D = T.dropna(subset=['wt', 'age']).copy()
print(len(D), D.c.describe())
for cols in (['wt'], ['wt', 'age', 'sex'], ['wt', 'age', 'sex', 'doy', 'dist']):
    rng = np.random.RandomState(0); idx = rng.permutation(len(D)); tr, te = D.iloc[idx[:int(.7*len(D))]], D.iloc[idx[int(.7*len(D)):]]
    m = lgb.LGBMRegressor(n_estimators=400, learning_rate=0.05, num_leaves=31, min_child_samples=20, verbose=-1).fit(tr[cols], tr.c)
    e = te.c - m.predict(te[cols])
    print(cols, 'rmse', round(float(np.sqrt((e**2).mean())), 3), 'mae', round(float(e.abs().mean()), 3), 'sd of c', round(float(te.c.std()), 3))
D.to_pickle('/tmp/atw_offsets.pkl')
