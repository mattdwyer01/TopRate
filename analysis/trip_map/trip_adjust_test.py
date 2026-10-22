"""Trip-adjusted rating test. Part A (explainers): what about a run's trip explains it being rated above or below the horse's own level?
dev = run wpr minus the mean of the horse's 2 runs before and 2 after (ability at the time, hindsight allowed). Regress dev on trip descriptors:
context only, + steward/video comment flags, + GPS (ground lost, lane, early speed). Part B: does adding back the estimated trip effect
improve the next-start rating forecast, judged on the top half of each field by prior rating. Sources: racing.com VIC/SA, RQ QLD, ATC NSW metro."""
import glob, os, re, sys
import numpy as np, pandas as pd, lightgbm as lgb
sys.path.insert(0, os.path.dirname(__file__))
import build_trip_map as B
ROOT = B.ROOT
cols = ['race_id', 'horse_id', 'comments_steward', 'comments_video', 'position600m', 'position400m', 'margin600m', 'margin400m', 'positionFinish', 'marginFinish', 'wpr', 'weightCarried']
ex = pd.concat([pd.read_csv(f, usecols=lambda c: c in cols, low_memory=False) for f in sorted(glob.glob(os.path.join(ROOT, 'race_results_20*.csv.gz')))]).drop_duplicates(['race_id', 'horse_id'])
res = B.add_result_features(B.load_results())
res = res.merge(ex.drop(columns=['wpr']), on=['race_id', 'horse_id'], how='left')
res = res[res.wpr.notna()].sort_values(['horse_id', 'date', 'race_id']).reset_index(drop=True)
g = res.groupby('horse_id').wpr
res['prior2'] = g.transform(lambda s: s.shift(1).rolling(2, min_periods=2).mean())
res['next2'] = g.transform(lambda s: s[::-1].shift(1).rolling(2, min_periods=2).mean()[::-1])
res['prior3'] = g.transform(lambda s: s.shift(1).rolling(3, min_periods=2).mean())
res['next1'] = g.shift(-1)
res['dev'] = res.wpr - 0.5 * (res.prior2 + res.next2)
# ---- comment flags
txt = (res.comments_steward.fillna('') + ' ' + res.comments_video.fillna('')).str.lower()
FL = {'f_wide': r'\b(wide|three wide|four wide|five wide|outside|without cover|exposed|no cover)\b',
      'f_blocked': r'(held up|blocked|checked|not clear|no clear|hampered|bumped|interfer|shifted in|clipp|steadied|inside|crowded|squeezed|trapped|shut in)',
      'f_slow': r'(slow(ly)? away|began awkward|missed the start|fumbled|dwelt|stumbled|reared|lost ground at the start)',
      'f_keen': r'(keen|pulled|over ?raced|fought|rolled|laid out|laid in|hung)',
      'f_vet': r'(vet|lame|bled|bleed|arrhythm|sore|injur|tailed|distress|heart|cardiac)',
      'f_soft': r'(sit ?out|eased|not persevered|not knocked|dropped out|weak)'}
for k, p in FL.items(): res[k] = txt.str.contains(p, regex=True).astype(int)
# ---- GPS (+ ATC) trip descriptors
v = B.vicsa_runs(res); q = B.qld_runs(res)
v['src'] = 0; q['src'] = 1
gp = pd.concat([v, q], ignore_index=True)[['race_id', 'horse_id', 'src', 'extra', 'lane', 'early']]
gp['extra_rel'] = gp.extra - gp.groupby('race_id').extra.transform('median')
gp['lane_rel'] = gp.lane - gp.groupby('race_id').lane.transform('median')
gp['early_z'] = gp.early / gp.groupby('src').early.transform('std')
a = pd.concat([pd.read_parquet(f) for f in glob.glob(os.path.join(ROOT, 'data/gps/atc_gps_runs_*.parquet'))])
a['date'] = pd.to_datetime(a.race_date); a['hn'] = B.clean_name(a.horse)
gg = ['meet_code', 'race_no']
a['extra_rel'] = a.dist_vs_winner_m - a.groupby(gg).dist_vs_winner_m.transform('median')
e = -(a.first400_s - a.groupby(gg).first400_s.transform('mean')); a['early_z'] = e / e.std()
a = a[['date', 'hn', 'distance', 'extra_rel', 'early_z']]; a = a[~a.duplicated(['date', 'hn', 'distance'], keep=False)]
at = res.merge(a, on=['date', 'hn', 'distance'])[['race_id', 'horse_id', 'extra_rel', 'early_z']]; at['src'] = 2
d = res.merge(pd.concat([gp[['race_id', 'horse_id', 'src', 'extra_rel', 'lane_rel', 'early_z']], at], ignore_index=True).drop_duplicates(['race_id', 'horse_id']), on=['race_id', 'horse_id'], how='left')
d['gps'] = d.src.notna()
d['pace'] = d.groupby('race_id').early_z.transform(lambda s: s.nlargest(3).mean())
d['early_rel'] = d.early_z
d['d400'] = d.position400m - d.position600m
d['gap400'] = d.margin400m.clip(0, 30); d['gap600'] = d.margin600m.clip(0, 30)
d['rank_prior'] = d.groupby('race_id').prior3.rank(ascending=False, method='first')
d['half'] = d.rank_prior <= (d.fs / 2).round()
CTX = ['distance', 'barrier', 'barfrac', 'fs', 'rail_m', 'going_s', 'settle', 'gap800', 'gap600', 'gap400']
CMT = list(FL)
GPS = ['extra_rel', 'lane_rel', 'early_rel', 'pace']
print('runs', len(d), 'with GPS', int(d.gps.sum()), flush=True)
# ================= Part A
A = d[d.gps & d.dev.notna() & (d.fs >= 6)].copy()
tr = A[A.date < '2024-01-01']; te = A[A.date >= '2025-01-01']
print('A: train', len(tr), 'test', len(te), flush=True)
def r2(f, sub=None):
    m = lgb.train(dict(B.PARAMS, num_threads=4), lgb.Dataset(tr[f], tr.dev), 300)
    t = te if sub is None else te[sub(te)]
    p = m.predict(t[f]); return 1 - ((t.dev - p) ** 2).sum() / ((t.dev - tr.dev.mean()) ** 2).sum(), m
sets = {'context': CTX, '+comments': CTX + CMT, '+GPS': CTX + GPS, '+comments+GPS': CTX + CMT + GPS}
print('held-out R2 of run deviation (higher = trip explains more); all runs | top half by prior rating | top 4 by prior')
mods = {}
for k, f in sets.items():
    ra, mods[k] = r2(f); rh, _ = r2(f, lambda t: t.half); r4, _ = r2(f, lambda t: t.rank_prior <= 4)
    print(f'  {k:16s} {ra:.4f} | {rh:.4f} | {r4:.4f}')
print('effects (mean run deviation from the horse\'s own level, WPR), test period:')
def eff(lab, col, bins):
    c = pd.cut(te[col], bins); t = te.groupby(c, observed=True).dev.agg(['mean', 'size']); print(' ', lab, {str(i): (round(float(r['mean']), 2), int(r['size'])) for i, r in t.iterrows()})
eff('extra ground vs race median (m)', 'extra_rel', [-99, -5, -1, 1, 5, 10, 20, 99])
eff('lane vs race median (m)', 'lane_rel', [-99, -3, -1, 1, 3, 6, 99])
eff('early speed (z)', 'early_rel', [-9, -1, -.3, .3, 1, 9])
for k in CMT: print(' ', k, 'with', round(float(te[te[k] == 1].dev.mean()), 2), int((te[k] == 1).sum()), 'without', round(float(te[te[k] == 0].dev.mean()), 2))
# GPS-only explanation of runs with NO relevant comment flag (GPS finds trips the stewards never mentioned)
nf = te[(te[CMT[:3]].sum(axis=1) == 0)]
print('runs with no wide/blocked/slow comment: dev by extra_rel bin'); eff('  (no comment) extra', 'extra_rel', [-99, -5, 5, 10, 20, 99]) if False else None
c = pd.cut(nf.extra_rel, [-99, -5, 5, 10, 20, 99]); print(' ', {str(i): (round(float(r['mean']), 2), int(r['size'])) for i, r in nf.groupby(c, observed=True).dev.agg(['mean', 'size']).iterrows()})
# ================= Part B: next-start rating forecast
m_full = mods['+comments+GPS']; m_ctx = mods['+comments']
d['trip_eff'] = np.nan
ok = d.gps & (d.date >= '2024-01-01')
d.loc[ok, 'trip_eff'] = m_full.predict(d.loc[ok, CTX + CMT + GPS]) - m_ctx.predict(d.loc[ok, CTX + CMT])   # GPS-only part of the explained deviation
d.loc[ok, 'trip_all'] = m_full.predict(d.loc[ok, CTX + CMT + GPS]) - d[ok].dev.mean()
d = d.sort_values(['horse_id', 'date', 'race_id']).reset_index(drop=True)
gh = d.groupby('horse_id')
d['gps_sum3'] = gh.trip_eff.transform(lambda s: s.shift(0).rolling(3, min_periods=1).sum())   # includes this run: used for the NEXT start
d['gps_last'] = d.trip_eff
d['raw3'] = gh.wpr.transform(lambda s: s.rolling(3, min_periods=2).mean())
d['y_next'] = d.next1
B_ = d[(d.date >= '2025-01-01') & False]   # placeholder to keep the layout readable
# target = a later run; predictors come from the run BEFORE it. Build rows indexed by the earlier run.
P = d[(d.date >= '2024-07-01') & d.y_next.notna() & d.raw3.notna() & d.trip_eff.notna()].copy()
P['gap_days'] = (gh.date.shift(-1).reindex(P.index) - P.date).dt.days
P = P[(P.gap_days <= 120)]
P['err_raw'] = P.y_next - P.raw3
P['trip_c'] = P.trip_eff
print('B: rows (last run has GPS, next run within 120 days)', len(P), 'races', P.race_id.nunique())
nxt = d.groupby('horse_id').race_id.shift(-1).reindex(P.index)
P['rank_prior_next'] = d.groupby('race_id').rank_prior.transform('first').reindex(P.index)  # prior rank in the LAST race (proxy for class standing)
for lab, sub in (('all', P), ('top half by prior in that race', P[P.half]), ('top 4 by prior in that race', P[P.rank_prior <= 4])):
    s_ = sub.dropna(subset=['err_raw', 'trip_c'])
    X = np.c_[np.ones(len(s_)), s_.trip_c]; coef = np.linalg.lstsq(X, s_.err_raw, rcond=None)[0]
    resid = s_.err_raw - X @ coef
    se = np.sqrt(resid.var() / (len(s_) * s_.trip_c.var()))
    print(f"  {lab:32s} n={len(s_):6d} slope of next-start miss on GPS trip effect {coef[1]:+.2f} (se {se:.2f}); rmse intercept-only {s_.err_raw.std():.3f} -> with trip {resid.std():.3f}")
q = P.dropna(subset=['trip_c']); lo, hi = q.trip_c.quantile([.1, .9])
print(f"trip effect (WPR, GPS part only) spread: sd {q.trip_c.std():.2f}, 5% {q.trip_c.quantile(.05):.2f}, 10% {lo:.2f}, 90% {hi:.2f}, 95% {q.trip_c.quantile(.95):.2f}")
print(f"next-start rating minus last-3 average: after the hardest-trip tenth {q[q.trip_c <= lo].err_raw.mean():+.2f} | easiest tenth {q[q.trip_c >= hi].err_raw.mean():+.2f} | middle {q[(q.trip_c > lo) & (q.trip_c < hi)].err_raw.mean():+.2f}")
# the full explained deviation (comments + GPS + context) for context
q2 = P.dropna(subset=['trip_all'])
X = np.c_[np.ones(len(q2)), q2.trip_all]; c2 = np.linalg.lstsq(X, q2.err_raw, rcond=None)[0]
print(f"full explained deviation (context+comments+GPS): sd {q2.trip_all.std():.2f}, slope of next-start miss {c2[1]:+.2f}")
