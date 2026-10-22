"""Does ATC (NSW metro Swiss Timing) sectional history improve the trip-map gap forecast at Sydney metro tracks?
Target gap800 (margin at 800m, results). Baseline = nongps-style results history; candidate adds ATC history
(early speed first 400m, ground vs winner, last 600m). Train before 2025, score 2025+, fields of 8+."""
import glob, os, sys
import numpy as np, pandas as pd, lightgbm as lgb
sys.path.insert(0, os.path.dirname(__file__))
import build_trip_map as B
ROOT = B.ROOT
res = B.load_results()
res = B.add_result_features(res)
a = pd.concat([pd.read_parquet(f) for f in glob.glob(os.path.join(ROOT, 'data/gps/atc_gps_runs_*.parquet'))])
a['date'] = pd.to_datetime(a.race_date); a['hn'] = B.clean_name(a.horse)
a['rg'] = a.groupby('meet_code').race_no.transform('size')
g = ['meet_code', 'race_no']
a['early'] = -(a.first400_s - a.groupby(g).first400_s.transform('mean'))
a['late'] = -(a.last600_s - a.groupby(g).last600_s.transform('mean'))
# extra ground: older templates give dist_travelled, newer give dist_vs_winner; use vs-winner in metres, demeaned in race
a['extra'] = a.dist_vs_winner_m
a['extra'] = a.extra - a.groupby(g).extra.transform('mean')
a['ntop'] = a.top_speed_kmh - a.groupby(g).top_speed_kmh.transform('mean')
a = a[['date', 'hn', 'distance', 'early', 'late', 'extra', 'ntop']]
a = a[~a.duplicated(['date', 'hn', 'distance'], keep=False)]
res = res[res.field_size >= 5].copy()
m = res.merge(a, on=['date', 'hn', 'distance'], how='left')
syd = m[m.early.notna() | m.late.notna()]
metro = set(res.merge(a[['date', 'hn', 'distance']], on=['date', 'hn', 'distance']).track)
print('ATC-matched tracks', sorted(metro), 'matched runs', int(m.early.notna().sum()), flush=True)
m = m[m.track.isin(metro)].sort_values(['horse_id', 'date', 'race_id']).reset_index(drop=True)
m['trk'] = m.track.astype('category')
T = ['gap800', 'settle']; X = ['early', 'late', 'extra', 'ntop']
gh = m.groupby('horse_id')
for t in T + X:
    m[t + '_h3'] = gh[t].transform(lambda s: s.shift(1).rolling(3, min_periods=1).mean())
    m[t + '_h8'] = gh[t].transform(lambda s: s.shift(1).rolling(8, min_periods=2).mean())
m['n_lead'] = m.groupby('race_id').settle_h3.transform(lambda s: (s <= 0.25).sum())
m['own_rel'] = m.settle_h3 - m.groupby('race_id').settle_h3.transform('mean')
m['n_atc'] = gh['early'].transform(lambda s: s.notna().shift(1).fillna(False).astype(int).cumsum())
m['early_rel'] = m.early_h3 - m.groupby('race_id').early_h3.transform('mean')
m['n_fast'] = m.groupby('race_id').early_h3.transform(lambda s: (s > s.quantile(.75)).sum() if s.notna().sum() > 3 else np.nan)
base = ['trk', 'distance', 'barrier', 'barfrac', 'fs', 'rail_m', 'going_s'] + [t + s for t in T for s in ('_h3', '_h8')] + ['n_lead', 'own_rel']
atc = [x + s for x in X for s in ('_h3', '_h8')] + ['n_atc', 'early_rel', 'n_fast']
tr = m[(m.date < '2025-01-01') & m.gap800.notna() & (m.date >= '2019-01-01')]
te = m[(m.date >= '2025-01-01') & (m.fs >= 8) & m.gap800.notna()]
te = te[te.race_id.map(te.groupby('race_id').size()) >= 6]
print('train', len(tr), 'test', len(te), 'races', te.race_id.nunique(), flush=True)
def fit(feats, y='gap800'):
    ps = []
    for seed in range(3):
        P = dict(B.PARAMS, seed=seed, bagging_seed=seed, feature_fraction_seed=seed)
        mod = lgb.train(P, lgb.Dataset(tr[feats], tr[y]), B.ROUNDS); ps.append(mod.predict(te[feats]))
    return np.mean(ps, 0)
def score(p, y='gap800'):
    d = te.assign(p=p)
    pc = d.p - d.groupby('race_id').p.transform('mean'); yc = d[y] - d.groupby('race_id')[y].transform('mean')
    ok = yc.notna()
    # per-race correlation mean + pooled rmse of centred
    r = d.assign(pc=pc, yc=yc)[ok].groupby('race_id').apply(lambda z: np.corrcoef(z.pc, z.yc)[0, 1] if z.pc.std() > 0 else np.nan)
    return dict(pooled_corr=round(float(np.corrcoef(pc[ok], yc[ok])[0, 1]), 4), race_corr=round(float(r.mean()), 4), rmse=round(float(np.sqrt(((pc - yc)[ok] ** 2).mean())), 4))
pb = fit(base); pa = fit(base + atc)
print('baseline', score(pb)); print('+ATC   ', score(pa))
# paired bootstrap by race on squared error
d = te.assign(pb=pb, pa=pa)
for c in ('pb', 'pa'): d[c] = d[c] - d.groupby('race_id')[c].transform('mean')
d['yc'] = d.gap800 - d.groupby('race_id').gap800.transform('mean')
d['dse'] = (d.pb - d.yc) ** 2 - (d.pa - d.yc) ** 2
rs = d.groupby('race_id').dse.mean().values
print('mean sq-error gain', round(rs.mean(), 4), 'se', round(rs.std() / np.sqrt(len(rs)), 4))
# coverage subgroup: runners with >=2 earlier ATC runs
for lab, msk in (('>=2 ATC runs', te.n_atc >= 2), ('<2 ATC runs', te.n_atc < 2)):
    s = d[msk.values]
    print(lab, len(s), 'sq-err gain', round(s.dse.mean(), 4))
# secondary: ground vs winner (extra) predictability
te2 = te[te.extra.notna()]
trx = tr[tr.extra.notna()]
for lab, f in (('extra base', base), ('extra +ATC', base + atc)):
    mod = lgb.train(B.PARAMS, lgb.Dataset(trx[f], trx.extra), B.ROUNDS)
    p = mod.predict(te2[f]); pc = p - pd.Series(p, index=te2.index).groupby(te2.race_id).transform('mean')
    print(lab, 'corr with ground-vs-winner (race-centred)', round(float(np.corrcoef(pc, te2.extra)[0, 1]), 3), 'n', len(te2))
