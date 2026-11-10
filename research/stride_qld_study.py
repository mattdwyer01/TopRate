"""Does Racing Queensland stride data (stride length / frequency per 200m) add
anything to a rating forecast? (10 Nov 2026)

The earlier stride test (research/stride_profile_test.py) only had 727 Racing
Victoria PDF races. RQ GPS sections carry stride_m / stride_hz for about 13,000
races from Oct 2022, so this re-tests it at scale.

Target: a run's rating (results-file wpr) minus its race mean, races of 5+.
Baseline: the horse's rating history and today's conditions (LightGBM).
Candidate: baseline + the horse's stride history from earlier QLD runs
(field-relative and own-history stride length, frequency, late fade, max) and
interactions with today's going and distance.
Fit on targets before 2025-07-01, early stop 2025-01..06 inside, test 2025-07+.
Rows = targets whose horse has at least one earlier QLD stride run.
Also: which stride measures go with the run's own rating after the fact.

Run: PYTHONPATH=. python research/stride_qld_study.py
"""
import glob, re
import numpy as np, pandas as pd, lightgbm as lgb

def norm(s):
    s = re.sub(r'\(.*?\)', '', str(s).lower())
    return re.sub(r'[^a-z0-9]', '', s)

# ---------- results ----------
cols = ['race_id', 'date', 'horse', 'track', 'distance', 'going', 'wpr', 'weightCarried', 'barrier',
        'field_size', 'isBarrierTrial', 'race_class', 'marginFinish', 'raceNumber', 'positionFinish']
R = pd.concat([pd.read_csv(f, usecols=cols, low_memory=False)
               for f in sorted(glob.glob('race_results_20*.csv.gz')) if f[-10:-7] in ('021', '022', '023', '024', '025', '026')])
R = R[(R.isBarrierTrial != True) & R.wpr.notna()]
R = R[~R.race_class.astype(str).str.contains('Hurdle|Steeple', na=False)]
R['date'] = pd.to_datetime(R.date).dt.tz_localize(None).dt.normalize()
n = R.groupby('race_id').wpr.transform('size'); R = R[n >= 5]
R['w'] = R.wpr - R.groupby('race_id').wpr.transform('mean')
R['h'] = R.horse.map(norm)
R['wet'] = R.going.astype(str).str.contains('Soft|Heavy', case=False).astype(float)
R['bfrac'] = (R.barrier - 1) / (R.field_size - 1).clip(lower=1)
R = R.sort_values(['h', 'date']).reset_index(drop=True)
print('results runs', len(R))

# ---------- QLD stride per run ----------
S = pd.concat([pd.read_parquet(f) for f in sorted(glob.glob('data/gps/rq_gps_sections_*.parquet'))])
S = S.dropna(subset=['stride_m', 'stride_hz'])
S = S[(S.stride_m.between(4, 9.5)) & (S.stride_hz.between(1.5, 3.2))]
S = S.sort_values(['race_code', 'tab_no', 'cum_dist_m'])
g = S.groupby(['race_code', 'tab_no'])
S['k'] = g.cumcount(); S['nk'] = g.cum_dist_m.transform('size')
body = S[(S.k >= 1)]                       # skip the first 200m (standing start)
late = S[S.k >= S.nk - 2]                  # last 400m
mid = S[(S.k >= 1) & (S.k < S.nk - 2)]
F = pd.DataFrame({
    'sl_mean': body.groupby(['race_code', 'tab_no']).stride_m.mean(),
    'sf_mean': body.groupby(['race_code', 'tab_no']).stride_hz.mean(),
    'sl_max': body.groupby(['race_code', 'tab_no']).stride_m.max(),
    'sl_late': late.groupby(['race_code', 'tab_no']).stride_m.mean(),
    'sf_late': late.groupby(['race_code', 'tab_no']).stride_hz.mean(),
    'sl_mid': mid.groupby(['race_code', 'tab_no']).stride_m.mean(),
    'sf_mid': mid.groupby(['race_code', 'tab_no']).stride_hz.mean(),
}).reset_index()
F['sl_fade'] = F.sl_late - F.sl_mid; F['sf_fade'] = F.sf_late - F.sf_mid
for c in ['sl_mean', 'sf_mean', 'sl_max', 'sl_late', 'sf_late', 'sl_fade', 'sf_fade']:
    F[c + '_r'] = F[c] - F.groupby('race_code')[c].transform('mean')
runs = pd.concat([pd.read_parquet(f, columns=['race_code', 'race_date', 'horse', 'tab_no', 'course'])
                  for f in sorted(glob.glob('data/gps/rq_gps_runs_*.parquet'))])
F = F.merge(runs, on=['race_code', 'tab_no'])
F['date'] = pd.to_datetime(F.race_date).dt.normalize(); F['h'] = F.horse.map(norm)
F = F.drop_duplicates(['h', 'date'])
print('QLD stride runs', len(F), 'races', F.race_code.nunique())

R = R.merge(F.drop(columns=['race_code', 'race_date', 'horse', 'tab_no', 'course']), on=['h', 'date'], how='left')
R['has_s'] = R.sl_mean.notna()
print('stride runs matched to results', int(R.has_s.sum()), 'of', len(F))

# ---------- ex post: stride vs the run's own rating ----------
E = R[R.has_s].copy()
print('\nEx post, within-race corr with the run rating w (n=%d):' % len(E))
for c in ['sl_mean_r', 'sf_mean_r', 'sl_max_r', 'sl_late_r', 'sf_late_r', 'sl_fade_r', 'sf_fade_r']:
    print('  %-10s %+.3f' % (c, np.corrcoef(E[c], E.w)[0, 1]))

# ---------- history features ----------
gh = R.groupby('h')
for k in range(1, 5):
    R[f'w{k}'] = gh.w.shift(k)
R['mean3'] = R[['w1', 'w2', 'w3']].mean(axis=1)
R['nruns'] = gh.cumcount()
R['days'] = (R.date - gh.date.shift(1)).dt.days
R['dchg'] = R.distance - gh.distance.shift(1)
R['wtchg'] = R.weightCarried - gh.weightCarried.shift(1)
# stride history: last earlier stride run (forward-filled), EWM over earlier stride runs, own-history change
SC = ['sl_mean_r', 'sf_mean_r', 'sl_max_r', 'sl_late_r', 'sf_late_r', 'sl_fade_r', 'sf_fade_r', 'sl_mean', 'sf_mean']
for c in SC:
    R['p_' + c] = gh[c].shift(1)
    R['p_' + c] = R.groupby('h')['p_' + c].ffill()
    R['e_' + c] = gh[c].transform(lambda s: s.shift(1).ewm(halflife=3, ignore_na=True).mean())
R['p_dist_s'] = R.distance.where(R.has_s); R['p_dist_s'] = gh.p_dist_s.shift(1) if False else R.groupby('h').p_dist_s.transform(lambda s: s.shift(1).ffill())
R['n_s'] = R.groupby('h').has_s.cumsum() - R.has_s.astype(int)
# interactions with today's conditions
R['x_sl_wet'] = R.e_sl_mean_r * R.wet
R['x_sl_dist'] = R.e_sl_mean_r * (R.distance - 1400) / 400
R['x_sf_dist'] = R.e_sf_mean_r * (R.distance - 1400) / 400
R['x_fade_dchg'] = R.e_sl_fade_r * R.dchg.fillna(0) / 200
R['d_from_sdist'] = R.distance - R.p_dist_s

BASE = ['w1', 'w2', 'w3', 'w4', 'mean3', 'nruns', 'days', 'distance', 'dchg', 'wtchg', 'weightCarried',
        'wet', 'bfrac', 'field_size']
STR = ['p_' + c for c in SC] + ['e_' + c for c in SC] + ['n_s', 'x_sl_wet', 'x_sl_dist', 'x_sf_dist', 'x_fade_dchg', 'd_from_sdist']

D = R[(R.n_s >= 1) & R.w1.notna()].copy()
print('\ntarget rows with earlier QLD stride:', len(D))
fit = D.date < '2025-07-01'; te = ~fit
es = fit & (D.date >= '2025-01-01'); tr = fit & ~es
P = dict(objective='huber', alpha=4.0, learning_rate=0.03, num_leaves=31, min_data_in_leaf=200,
         feature_fraction=0.8, bagging_fraction=0.8, bagging_freq=1, verbose=-1, seed=1)
def run(feats):
    m = lgb.train(P, lgb.Dataset(D.loc[tr, feats], D.loc[tr, 'w']), 3000,
                  valid_sets=[lgb.Dataset(D.loc[es, feats], D.loc[es, 'w'])],
                  callbacks=[lgb.early_stopping(100, verbose=False)])
    m2 = lgb.train(P, lgb.Dataset(D.loc[fit, feats], D.loc[fit, 'w']), m.best_iteration)
    return m2.predict(D.loc[te, feats]), m2
pb, _ = run(BASE); ps, ms = run(BASE + STR)
y = D.loc[te, 'w'].values; rid = D.loc[te, 'race_id'].values
def stats(p):
    e = y - p; ed = e - pd.Series(e).groupby(rid).transform('mean').values
    return np.sqrt((e ** 2).mean()), np.median(np.abs(e)), np.sqrt((ed ** 2).mean())
print('test rows', len(y), 'races', len(set(rid)))
for nm, p in (('baseline', pb), ('+ stride', ps)):
    print('  %-9s RMSE %.4f  median|e| %.3f  within-race RMSE %.4f' % ((nm,) + stats(p)))
d = (y - pb) ** 2 - (y - ps) ** 2
print('  paired sq-error gain %.3f (se %.3f)' % (d.mean(), d.std() / np.sqrt(len(d))))
imp = pd.Series(ms.feature_importance('gain'), index=BASE + STR); imp /= imp.sum()
print('  stride share of gain %.1f%%; top stride inputs:' % (100 * imp[STR].sum()))
print(imp[STR].sort_values(ascending=False).head(8).round(3).to_string())

# winner test in test races where 80%+ of the field has a prediction
T = D.loc[te, ['race_id', 'positionFinish']].copy(); T['pb'] = pb; T['ps'] = ps
full = R.groupby('race_id').size()
cov = T.groupby('race_id').size() / full.reindex(T.race_id.unique())
T = T[T.race_id.isin(cov[cov >= 0.8].index)]
T['won'] = (pd.to_numeric(T.positionFinish, errors='coerce') == 1).astype(int)
T = T[T.groupby('race_id').won.transform('sum') == 1]
def ll(col, beta):
    z = beta * (T[col] - T.groupby('race_id')[col].transform('max'))
    e = np.exp(z); p = e / e.groupby(T.race_id).transform('sum')
    return np.log(p[T.won == 1]).values
best = {c: max(np.arange(0.05, 0.6, 0.01), key=lambda b: ll(c, b).mean()) for c in ('pb', 'ps')}
lb, ls = ll('pb', best['pb']), ll('ps', best['ps'])
print('\nwinner test, %d races with 80%%+ covered:' % T.race_id.nunique())
print('  baseline %.4f  + stride %.4f  gain %+.4f (se %.4f)' % (lb.mean(), ls.mean(), (ls - lb).mean(), (ls - lb).std() / np.sqrt(len(lb))))
