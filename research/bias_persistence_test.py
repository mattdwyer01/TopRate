"""Can track bias (leaders vs closers, draw) be known BEFORE a race from earlier actuals? Runner-page store (data/tr_form, ATW ratings, positions at 800m, barrier, finish).
Part 1, persistence: per race, bias = Spearman(position at 800m fraction, finish) (leaders) and Spearman(barrier fraction, finish) (draw), from the stored runners of that race
(5+ with the data). Share of variance that is venue-level, meeting-day level, or race noise (one-way ANOVA ICCs), and the correlation of a meeting's bias with (a) the venue's
earlier meetings and (b) the earlier races on the same day.
Part 2, usefulness: add as-of bias features to the live Proj context model (ATW only): the venue's trailing bias (earlier meetings only), the day's earlier-race bias (earlier races
of the same meeting only), and their interactions with what is KNOWN pre-race (barrier fraction, the horse's own earlier settling style). Paired out-of-sample test on 2026.
Run: PYTHONPATH=. python research/bias_persistence_test.py"""
import glob, gzip, json, sys
import numpy as np, pandas as pd, lightgbm as lgb
sys.path.insert(0, 'projection')
import ctx as C

rows = []
for f in sorted(glob.glob('data/tr_form/*.json.gz')):
    for r in json.load(gzip.open(f, 'rt')).get('runs', {}).values():
        if r.get('isBarrierTrial') or r.get('isJumpout') or r.get('wpr') is None:
            continue
        rows.append(dict(horse_id=r['horse_id'], date=r['date'], raceId=r.get('raceId'), meetingId=r.get('meetingId'), rno=r.get('raceNumber'), venue=r.get('venue'),
                         p800=r.get('position800m'), fin=r.get('positionFinish'), st=r.get('starters'), barr=r.get('barrier')))
X = pd.DataFrame(rows); X['horse_id'] = pd.to_numeric(X.horse_id, errors='coerce'); X['date'] = pd.to_datetime(X.date)
X = X.drop_duplicates(['horse_id', 'date'], keep='last')
X['sf'] = X.p800 / X.st; X['bf'] = X.barr / X.st
def sp(a, b):
    ok = a.notna() & b.notna()
    return float(a[ok].rank().corr(b[ok].rank())) if ok.sum() >= 5 and a[ok].nunique() > 1 and b[ok].nunique() > 1 else np.nan
R = X.groupby('raceId').apply(lambda g: pd.Series(dict(lead=sp(g.sf, g.fin), draw=sp(g.bf, g.fin), n=len(g), date=g.date.iloc[0], venue=g.venue.iloc[0], meetingId=g.meetingId.iloc[0], rno=g.rno.iloc[0]))).reset_index()
R = R[(R.n >= 6) & R.lead.notna() & (R.date >= '2024-07-01')].copy()
R['date'] = pd.to_datetime(R.date)
print('races with bias stats', len(R), 'meetings', R.meetingId.nunique(), 'venues', R.venue.nunique())
def icc(df, col, grp):
    g = df.groupby(grp)[col]; k = g.size(); k = k[k >= 2].index
    d = df[df[grp].isin(k)]; g = d.groupby(grp)[col]
    n = g.size(); m = g.mean(); grand = d[col].mean()
    msb = (n * (m - grand) ** 2).sum() / (len(m) - 1); msw = ((d[col] - g.transform('mean')) ** 2).sum() / (len(d) - len(m)); n0 = (n.sum() - (n ** 2).sum() / n.sum()) / (len(m) - 1)
    return max(0.0, (msb - msw) / (msb + (n0 - 1) * msw))
print('\nPart 1: share of race-to-race variance in the bias that is persistent')
for c, lab in (('lead', 'leaders vs closers'), ('draw', 'draw (wide = worse)')):
    R['mk'] = R.meetingId.astype(str)
    print(f'  {lab:22s} mean {R[c].mean():+.3f} sd {R[c].std():.3f} | same meeting-day ICC {icc(R, c, "mk"):.2f} | same venue ICC {icc(R, c, "venue"):.2f}')
M = R.groupby(['venue', 'date', 'meetingId']).agg(lead=('lead', 'mean'), draw=('draw', 'mean'), nr=('lead', 'size')).reset_index().sort_values(['venue', 'date'])
M = M[M.nr >= 4]
for c in ('lead', 'draw'):
    M['prev'] = M.groupby('venue')[c].shift(1); M['prev5'] = M.groupby('venue')[c].transform(lambda s: s.shift(1).rolling(5, min_periods=3).mean())
    a = M.dropna(subset=['prev']); b = M.dropna(subset=['prev5'])
    print(f'  meeting {c}: corr with previous meeting at the venue {a[[c, "prev"]].corr().iloc[0, 1]:+.2f} (n={len(a)}), with the venue\'s last-5 mean {b[[c, "prev5"]].corr().iloc[0, 1]:+.2f} (n={len(b)})')
# within-day: mean of earlier races vs this race
R = R.sort_values(['meetingId', 'rno'])
for c in ('lead', 'draw'):
    cs = R.groupby('meetingId')[c].cumsum() - R[c]; cn = R.groupby('meetingId').cumcount()
    R['e_' + c] = (cs / cn.replace(0, np.nan)).where(cn >= 3)
    d = R.dropna(subset=['e_' + c])
    print(f'  race {c}: corr with the mean of the 3+ earlier races the same day {d[[c, "e_" + c]].corr().iloc[0, 1]:+.2f} (n={len(d)})')

# ---- Part 2: as-of features into the live Proj context model
R = R.sort_values('date')
def asof_venue(c, k=100.0):
    out = {}
    for ven, g in R.groupby('venue'):
        g = g.sort_values('date'); d = g.date.values; v = g[c].values
        cs = np.concatenate([[0], np.cumsum(v)]); cnt = np.arange(len(v) + 1)
        hi = np.searchsorted(d, d, side='left'); lo = np.searchsorted(d, d - np.timedelta64(365, 'D'), side='left')
        s = cs[hi] - cs[lo]; n = hi - lo
        for i, rid in enumerate(g.raceId.values): out[rid] = (s[i] / (n[i] + 15.0), n[i])
    return out
vl, vd = asof_venue('lead'), asof_venue('draw')
R['vb_lead'] = R.raceId.map(lambda r: vl[r][0]); R['vb_draw'] = R.raceId.map(lambda r: vd[r][0])
R['db_lead'] = (R.e_lead.fillna(0) * 3 / (3 + 5)); R['db_draw'] = (R.e_draw.fillna(0) * 3 / (3 + 5))
rp = C.training_frame().merge(X[['horse_id', 'date', 'raceId', 'sf', 'bf']], on=['horse_id', 'date'], how='left')
rp = rp.merge(R[['raceId', 'vb_lead', 'vb_draw', 'db_lead', 'db_draw']], on='raceId', how='left')
rp = rp.sort_values(['horse_id', 'date']).reset_index(drop=True); g = rp.groupby('horse_id')
rp['h_sf'] = g.sf.transform(lambda s: s.shift(1).rolling(3, min_periods=1).mean())
rp['x_draw_v'] = rp.vb_draw * (rp.barr_f - 0.5); rp['x_draw_d'] = rp.db_draw * (rp.barr_f - 0.5)
rp['x_lead_v'] = rp.vb_lead * (0.5 - rp.h_sf); rp['x_lead_d'] = rp.db_lead * (0.5 - rp.h_sf)
NEW = ['vb_lead', 'vb_draw', 'db_lead', 'db_draw', 'x_draw_v', 'x_draw_d', 'x_lead_v', 'x_lead_d', 'h_sf']
rp['cls_c'] = C._cls(rp.cls, sorted(rp.cls.dropna().unique().tolist()))
pg = rp[rp.f.notna() & rp.vb_lead.notna()].copy()
cut, es = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')
tr, va, te = pg[pg.date < es], pg[(pg.date >= es) & (pg.date < cut)], pg[pg.date >= cut]
P = dict(n_estimators=3000, learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1)
def fit(feats):
    p = []
    for s in range(3):
        m = lgb.LGBMRegressor(**P, random_state=s).fit(tr[feats], tr.resid, eval_set=[(va[feats], va.resid)], callbacks=[lgb.early_stopping(100, verbose=False)]); p.append(m.predict(te[feats]))
    return np.mean(p, axis=0)
print(f'\nPart 2: runs with as-of bias: train {len(tr)} valid {len(va)} test {len(te)}')
e0 = te.resid.values - fit(C.FEATS); rm = lambda e: float(np.sqrt((e ** 2).mean()))
print(f'  baseline live Proj context model RMSE {rm(e0):.4f}')
for name, feats in (('venue bias + draw interaction', ['vb_draw', 'x_draw_v']), ('venue bias + leader interaction', ['vb_lead', 'x_lead_v', 'h_sf']), ('same-day earlier-race bias', ['db_lead', 'db_draw', 'x_draw_d', 'x_lead_d', 'h_sf']), ('all as-of bias', NEW)):
    e1 = te.resid.values - fit(C.FEATS + feats); d = e0 ** 2 - e1 ** 2
    print(f'  {name:32s} RMSE {rm(e1):.4f}  paired MSE gain {d.mean():+.3f} +-{1.96 * d.std() / np.sqrt(len(d)):.3f}')
