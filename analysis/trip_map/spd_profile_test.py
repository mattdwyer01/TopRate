"""GPS running profile for the SPEED figure target (23 Oct 2026). The time-based figure is physically tied to the sectional speeds the GPS measures, so profile history (early / mid /
finishing speed, kick, fade, peak speed, stride) may predict the next figure better than the figure history alone. Next-figure GBM: last 4 figures + their mean and spread
(base) vs base + profile history (pf3_ / pf8_, as of the race). Fit on 2025 targets, scored on 2026, runs where the horse has profile history. Model only.
Run after gps_profile.py: PYTHONPATH=. python analysis/trip_map/spd_profile_test.py"""
import os, sys
import numpy as np, pandas as pd, lightgbm as lgb
sys.path.insert(0, os.path.dirname(__file__)); sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..'))
import build_trip_map as B
import speed_rating as SR
ft = SR.figure_table(2019); ft['hn'] = B.clean_name(ft.key); ft['date'] = ft.date.astype('datetime64[ns]')
ft = ft.sort_values(['hn', 'date']).reset_index(drop=True)
g = ft.groupby('hn')
for a in range(1, 5): ft[f'sp{a}'] = g.sp.shift(a)
ft['sp_mean4'] = ft[['sp1', 'sp2', 'sp3', 'sp4']].mean(axis=1); ft['sp_sd4'] = ft[['sp1', 'sp2', 'sp3', 'sp4']].std(axis=1)
ft['n_prev'] = g.cumcount(); ft['days'] = (ft.date - g.date.shift(1)).dt.days
H = pd.read_parquet('/tmp/gps_profile_hist.parquet'); H['hdate'] = H.hdate.astype('datetime64[ns]'); H = H.sort_values('hdate')
PF = [c for c in H.columns if c.startswith(('pf3_', 'pf8_'))] + ['pf_n']
ft = ft.sort_values('date')
ft = pd.merge_asof(ft, H, left_on='date', right_on='hdate', by='hn', allow_exact_matches=False, tolerance=pd.Timedelta(days=900))
BASE = ['sp1', 'sp2', 'sp3', 'sp4', 'sp_mean4', 'sp_sd4', 'n_prev', 'days']
tr = ft[(ft.date >= '2022-01-01') & (ft.date < '2026-01-01') & ft.sp1.notna() & ft.pf_n.notna()]
te = ft[(ft.date >= '2026-01-01') & ft.sp1.notna() & ft.pf_n.notna()]
print('runs with profile history: train', len(tr), 'test', len(te), flush=True)
P = dict(objective='regression', learning_rate=0.04, num_leaves=31, min_data_in_leaf=100, feature_fraction=0.8, bagging_fraction=0.8, bagging_freq=1, lambda_l2=5, verbose=-1, num_threads=4)
res = {}
for lab, f in (('figure history only', BASE), ('+ profile history', BASE + PF)):
    mdl = lgb.train(P, lgb.Dataset(tr[f], tr.sp), 500); p = mdl.predict(te[f]); res[lab] = p
    e = te.sp.values - p; print(f'  {lab:22s} RMSE {np.sqrt((e ** 2).mean()):.4f} lengths, MAE {np.abs(e).mean():.4f}, corr {np.corrcoef(p, te.sp)[0, 1]:.4f}')
d = (te.sp.values - res['figure history only']) ** 2 - (te.sp.values - res['+ profile history']) ** 2
print(f'  squared-error gain {d.mean():+.4f} (se {d.std() / np.sqrt(len(d)):.4f}), RMSE {100 * (1 - np.sqrt(((te.sp.values - res["+ profile history"]) ** 2).mean() / ((te.sp.values - res["figure history only"]) ** 2).mean())):.2f}% lower')
imp = pd.Series(lgb.train(P, lgb.Dataset(tr[BASE + PF], tr.sp), 500).feature_importance('gain'), index=BASE + PF).sort_values(ascending=False)
print('  top inputs by gain:', ', '.join(f'{i} {100 * v / imp.sum():.1f}%' for i, v in imp.head(8).items()))

# ---- does it carry to winners? full fields from the results files (every runner has a figure history), model only
import glob
from scipy.optimize import minimize_scalar
res_ids = B.load_results()[['race_id', 'horse_id', 'hn', 'date']].drop_duplicates(['race_id', 'hn'])
fin = pd.concat([pd.read_csv(f, usecols=['race_id', 'horse_id', 'positionFinish'], low_memory=False) for f in sorted(glob.glob(os.path.join(B.ROOT, 'race_results_20*.csv.gz')))]).drop_duplicates(['race_id', 'horse_id'])
res_ids = res_ids.merge(fin, on=['race_id', 'horse_id'], how='left'); res_ids['date'] = res_ids.date.astype('datetime64[ns]')
te2 = te[['hn', 'date']].copy().reset_index(drop=True)
for k, v in res.items(): te2[k] = v
w = te2.merge(res_ids, on=['hn', 'date'], how='inner')
tot = res_ids.groupby('race_id').size(); w['full'] = w.race_id.map(tot)
cnt = w.groupby('race_id').size(); w['cover'] = w.race_id.map(cnt) / w.full
w = w[(w.cover >= 0.8) & (w.full >= 6)].copy(); w['win'] = (w.positionFinish == 1).astype(int)
gb = w.groupby('race_id'); w = w[gb.win.transform('sum') == 1].copy()
print(f'\nWINNERS (full fields, >= 80% of runners with a figure history, model only): races {w.race_id.nunique()}, runners {len(w)}')
d0 = w.date.sort_values().iloc[len(w) // 2]
def ll(df, col, beta):
    s = beta * (df[col] - df.groupby('race_id')[col].transform('mean')); mx = s.groupby(df.race_id).transform('max'); ex = np.exp(s - mx); den = ex.groupby(df.race_id).transform('sum')
    return np.log(ex / den)[df.win == 1]
out = {}
for col in res:
    parts = []
    for a, b in ((w[w.date < d0], w[w.date >= d0]), (w[w.date >= d0], w[w.date < d0])):
        beta = minimize_scalar(lambda x: -ll(a, col, x).sum(), bounds=(0.001, 1), method='bounded').x; parts.append(ll(b, col, beta))
    out[col] = pd.concat(parts)
    top = w[w.groupby('race_id')[col].rank(ascending=False, method='first') == 1]
    print(f'  {col:22s} winner LL {out[col].mean():.4f}, top pick wins {100 * top.win.mean():.1f}%')
dd = (out['+ profile history'] - out['figure history only']).dropna()
print(f'  gain from profile history {dd.mean():+.4f} (se {dd.std() / np.sqrt(len(dd)):.4f}) over {len(dd)} races')
