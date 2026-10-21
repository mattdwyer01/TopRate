"""Post-race review of the live Proj (formula + context, ATW runner-page ratings only): where does the miss come from, and does feeding actuals back help?
1) split each miss into a race-level part (field mean miss) and a within-race part; 2) bias tables by segment; 3) same meeting-day feedback: do earlier races' mean
misses predict later races' mean miss (track/going drift), and does applying a shrunk correction cut RMSE; 4) same track, previous days.
Run: PYTHONPATH=. python research/proj_error_review.py"""
import sys, numpy as np, pandas as pd, lightgbm as lgb, glob, gzip, json
sys.path.insert(0, 'projection')
import ctx as C
rp = C.training_frame()
x = []
for f in sorted(glob.glob('data/tr_form/2025-*.json.gz') + glob.glob('data/tr_form/2026-*.json.gz')):
    for r in json.load(gzip.open(f, 'rt')).get('runs', {}).values():
        x.append((r['horse_id'], r['date'], r.get('raceId'), r.get('meetingId'), r.get('raceNumber'), r.get('track'), r.get('venue'), r.get('startTime')))
X = pd.DataFrame(x, columns=['horse_id', 'date', 'raceId', 'meetingId', 'raceNumber', 'trk', 'venue', 'st'])
X['horse_id'] = pd.to_numeric(X.horse_id, errors='coerce'); X['date'] = pd.to_datetime(X.date)
rp = rp.merge(X.drop_duplicates(['horse_id', 'date']), on=['horse_id', 'date'], how='left')
classes = sorted(rp.cls.dropna().unique().tolist()); rp['cls_c'] = C._cls(rp.cls, classes)
pg = rp[rp.f.notna()].copy()
cut, es = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')
tr, va, te = pg[pg.date < es], pg[(pg.date >= es) & (pg.date < cut)], pg[pg.date >= cut].copy()
P = dict(n_estimators=3000, learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1)
m = lgb.LGBMRegressor(**P).fit(tr[C.FEATS], tr.resid, eval_set=[(va[C.FEATS], va.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
te['miss'] = te.resid - m.predict(te[C.FEATS])          # actual - live Proj
te = te[te.raceId.notna()].copy()
print('held-out runs', len(te), 'races', te.raceId.nunique(), 'RMSE', round(float(np.sqrt((te.miss**2).mean())), 3))
g = te.groupby('raceId').miss
te['rmean'] = g.transform('mean'); te['rn'] = g.transform('count')
te['within'] = te.miss - te.rmean
big = te[te.rn >= 4]
print(f"\n(1) variance split, races with 4+ runners in store (n={len(big)}): total {big.miss.var():.1f}  race-level {big.rmean.var():.1f} ({big.rmean.var()/big.miss.var():.0%})  within {big.within.var():.1f}")
# leave-one-out race mean is the honest race-level estimate
big = big.assign(loo=(big.rmean * big.rn - big.miss) / (big.rn - 1))
print('   corr(miss, mean of the OTHER runners miss in race) =', round(big[['miss', 'loo']].corr().iloc[0, 1], 3), ' slope', round(np.polyfit(big.loo, big.miss, 1)[0], 3))
print('\n(2) bias by segment (mean miss, held-out 2026; +ve = ran better than Proj):')
te['dband'] = pd.cut(te.distance, [0, 1100, 1400, 1700, 2100, 9999], labels=['<=1100', '1101-1400', '1401-1700', '1701-2100', '2100+'])
te['gband'] = pd.cut(te.going_n, [0, 3, 4, 5, 7, 99], labels=['Firm', 'Good', 'Soft5', 'Soft6-7', 'Heavy'])
te['nband'] = pd.cut(te.n, [-1, 2, 5, 9, 99], labels=['0-2', '3-5', '6-9', '10+'])
te['fband'] = pd.cut(te.field_size, [0, 8, 11, 14, 99], labels=['<=8', '9-11', '12-14', '15+'])
te['pband'] = pd.cut(te.f, [0, 60, 70, 80, 90, 200], labels=['<60', '60-70', '70-80', '80-90', '90+'])
for c in ['dband', 'gband', 'nband', 'fband', 'pband', 'cls']:
    t = te.groupby(c, observed=True).miss.agg(['mean', 'count', 'std']); t['se'] = t['std'] / np.sqrt(t['count'])
    t = t[t['count'] >= 300]
    print(c, ' '.join(f"{i}:{r['mean']:+.2f}±{r['se']:.2f}(n{int(r['count'])})" for i, r in t.iterrows()))
tt = te.groupby('venue').miss.agg(['mean', 'count']); tt = tt[tt['count'] >= 400].sort_values('mean')
print('venues (n>=400) lowest/highest mean miss:', ' | '.join(f"{i} {r['mean']:+.2f}" for i, r in pd.concat([tt.head(4), tt.tail(4)]).iterrows()))
# (3) same meeting-day feedback
rm = te.groupby(['meetingId', 'raceNumber', 'raceId'], as_index=False).agg(rmean=('miss', 'mean'), rn=('miss', 'count'), date=('date', 'first'), venue=('venue', 'first'))
rm = rm[rm.rn >= 3].sort_values(['meetingId', 'raceNumber'])
rm['w'] = rm.rn
cs = rm.groupby('meetingId').apply(lambda d: pd.DataFrame({'sw': (d.rmean * d.w).cumsum() - d.rmean * d.w, 'sn': d.w.cumsum() - d.w}, index=d.index)).reset_index(level=0, drop=True)
rm = rm.join(cs)
ok = rm[rm.sn >= 8].copy(); ok['prior'] = ok.sw / ok.sn
print(f"\n(3) same meeting-day: later races with 8+ earlier runners in store n={len(ok)}")
print('   corr(race mean miss, mean miss of earlier races same day) =', round(ok[['rmean', 'prior']].corr().iloc[0, 1], 3), ' slope', round(np.polyfit(ok.prior, ok.rmean, 1)[0], 3))
te = te.merge(ok[['raceId', 'prior', 'sn']], on='raceId', how='left')
sub = te[te.prior.notna()]
for k in (0.0, 0.1, 0.2, 0.3, 0.5):
    print(f'   apply {k:.1f} x earlier-race mean miss: RMSE {np.sqrt(((sub.miss - k*sub.prior)**2).mean()):.4f}  (n={len(sub)})')
# by split-halves slope
h1, h2 = sub[sub.date < '2026-07-01'], sub[sub.date >= '2026-07-01']
for lab, h in (('Jan-Jun', h1), ('Jul-Oct', h2)):
    print('   ', lab, 'runs', len(h), 'slope of miss on earlier-race mean', round(np.polyfit(h.prior, h.miss, 1)[0], 3))
# (4) same venue previous day(s)
dm = te.groupby(['venue', 'date']).miss.mean().reset_index().sort_values(['venue', 'date'])
dm['prev'] = dm.groupby('venue').miss.shift(1); dm['gap'] = (dm.date - dm.groupby('venue').date.shift(1)).dt.days
d2 = dm[(dm.gap <= 7)].dropna()
print(f"\n(4) same venue, previous meeting within 7 days: n={len(d2)} corr of day-mean miss with previous meeting's day-mean miss = {d2[['miss','prev']].corr().iloc[0,1]:+.3f}")
