"""Does feeding past actuals back into Proj help? Adds to the live ctx model, strictly as-of:
 day_eff : shrunk mean formula-residual of EARLIER races at the same meeting-day (runs in the runner-page store only)
 ven_eff : shrunk mean formula-residual of the venue's runs before the day (recent 180 days)
Fit before 2026-01 (early stop 2025-10..12), score 2026-01+, race-clustered bootstrap for the paired gain.
Run: PYTHONPATH=. python research/proj_feedback_test.py"""
import sys, glob, gzip, json, numpy as np, pandas as pd, lightgbm as lgb
sys.path.insert(0, 'projection')
import ctx as C
rp = C.training_frame()
x = []
for f in sorted(glob.glob('data/tr_form/*.json.gz')):
    for r in json.load(gzip.open(f, 'rt')).get('runs', {}).values():
        x.append((r['horse_id'], r['date'], r.get('raceId'), r.get('meetingId'), r.get('raceNumber'), r.get('venue')))
X = pd.DataFrame(x, columns=['horse_id', 'date', 'raceId', 'meetingId', 'raceNumber', 'venue'])
X['horse_id'] = pd.to_numeric(X.horse_id, errors='coerce'); X['date'] = pd.to_datetime(X.date)
rp = rp.merge(X.drop_duplicates(['horse_id', 'date']), on=['horse_id', 'date'], how='left')
rp = rp[rp.raceId.notna()].copy()
rp['cls_c'] = C._cls(rp.cls, sorted(rp.cls.dropna().unique().tolist()))
rp['rid'] = rp.resid                                  # formula residual (NaN for first runs)
# day_eff: earlier races same meetingId
K_DAY = 15.0
rr = rp[rp.rid.notna()].groupby(['meetingId', 'raceNumber']).rid.agg(['sum', 'count']).reset_index().sort_values(['meetingId', 'raceNumber'])
rr['cs'] = rr.groupby('meetingId')['sum'].cumsum() - rr['sum']; rr['cn'] = rr.groupby('meetingId')['count'].cumsum() - rr['count']
rp = rp.merge(rr[['meetingId', 'raceNumber', 'cs', 'cn']].rename(columns={'cs': 'dcs', 'cn': 'dcn'}), on=['meetingId', 'raceNumber'], how='left')
rp['dcn'] = rp.dcn.fillna(0); rp['dcs'] = rp.dcs.fillna(0)
rp['day_eff'] = rp.dcs / (rp.dcn + K_DAY)
rp['day_n'] = rp.dcn
# ven_eff: trailing 180 days strictly before the date
K_V = 100.0
v = rp[rp.rid.notna()].groupby(['venue', 'date']).rid.agg(['sum', 'count']).reset_index().sort_values(['venue', 'date'])
out = []
for ven, d in v.groupby('venue'):
    dd = d.date.values; s = d['sum'].values; c = d['count'].values
    cs, cc = np.concatenate([[0], np.cumsum(s)]), np.concatenate([[0], np.cumsum(c)])
    hi = np.searchsorted(dd, dd, side='left')                     # strictly before
    lo = np.searchsorted(dd, dd - np.timedelta64(180, 'D'), side='left')
    out.append(pd.DataFrame({'venue': ven, 'date': dd, 'vs': cs[hi] - cs[lo], 'vn': cc[hi] - cc[lo]}))
rp = rp.merge(pd.concat(out), on=['venue', 'date'], how='left')
rp['vn'] = rp.vn.fillna(0); rp['vs'] = rp.vs.fillna(0)
rp['ven_eff'] = rp.vs / (rp.vn + K_V)
pg = rp[rp.f.notna()].copy()
cut, es = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')
tr, va, te = pg[pg.date < es], pg[(pg.date >= es) & (pg.date < cut)], pg[pg.date >= cut].copy()
P = dict(n_estimators=3000, learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1)
def run(feats):
    ps = []
    for s in range(3):
        m = lgb.LGBMRegressor(**P, random_state=s).fit(tr[feats], tr.resid, eval_set=[(va[feats], va.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
        ps.append(m.predict(te[feats]))
    return np.mean(ps, axis=0)
base = run(C.FEATS)
sets = {'+day_eff': C.FEATS + ['day_eff', 'day_n'], '+ven_eff': C.FEATS + ['ven_eff'], '+both': C.FEATS + ['day_eff', 'day_n', 'ven_eff']}
e0 = (te.resid - base).values
print('baseline RMSE', round(float(np.sqrt((e0**2).mean())), 4), 'n', len(te))
rid = te.raceId.values; codes, uniq = pd.factorize(rid)
rng = np.random.default_rng(0)
def boot(d):
    s = np.bincount(codes, weights=d); n = np.bincount(codes)
    idx = rng.integers(0, len(uniq), (400, len(uniq)))
    return s[idx].sum(1) / n[idx].sum(1)
late = (te.day_n >= 8).values
for k, feats in sets.items():
    e1 = (te.resid - run(feats)).values
    d = e0**2 - e1**2; b = boot(d)
    print(f"{k:9s} RMSE {np.sqrt((e1**2).mean()):.4f}  paired MSE gain {d.mean():+.3f}  95% [{np.percentile(b,2.5):+.3f},{np.percentile(b,97.5):+.3f}]   "
          f"runs with 8+ earlier same-day runs (n={late.sum()}): {np.sqrt((e0[late]**2).mean()):.4f} -> {np.sqrt((e1[late]**2).mean()):.4f}")
