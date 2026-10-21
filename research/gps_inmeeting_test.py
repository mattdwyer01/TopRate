"""Could racing.com GPS (published 15-20 min after a race, if so) help IN the meeting? From earlier races of the SAME meeting, using only what GPS gives that TAB's finishing order does not:
  speed : the race time against the venue/distance par (seconds as % of par), the classic track-speed variant
  lane  : whether runners further off the rail finished worse (rail line vs finishing order)
  early : whether early speed (first 400m) was rewarded (early speed vs finishing order)
  lead  : position after 400m vs finishing order (what finishing order alone could also give)
Part 1 persistence: meeting-day ICC and the correlation of a race with the mean of the 2+ earlier races the same day.
Part 2 usefulness: (a) the race-level shared miss of the live Proj (mean over the race's stored runners of rating minus formula, after the context model) against the earlier races' speed variant;
(b) paired out-of-sample test adding the as-of in-meeting features to the context model. ATW ratings only (data/tr_form). Run: PYTHONPATH=. python research/gps_inmeeting_test.py"""
import glob, gzip, json, sys
import numpy as np, pandas as pd, lightgbm as lgb
sys.path.insert(0, 'projection'); sys.path.insert(0, 'research')
import ctx as C, gps_counterfactual as G
g = G.gps_runs()
def sp(a, b):
    ok = a.notna() & b.notna()
    return float(a[ok].rank().corr(b[ok].rank())) if ok.sum() >= 6 and a[ok].nunique() > 1 and b[ok].nunique() > 1 else np.nan
R = g.groupby('rk').apply(lambda x: pd.Series(dict(lead=sp(x.ep_f, x.finish), lane=sp(x.rail_rel, x.finish), early=sp(x.es_rel, x.finish), n=len(x), date=x.date.iloc[0], venue=x.venue_k.iloc[0],
                                                   meet=x.meet_.iloc[0], rno=x.race_no_.iloc[0], dist=x.dist.iloc[0], t=x.race_time_s.iloc[0]))).reset_index()
R['date'] = pd.to_datetime(R.date); R = R[(R.n >= 8) & R.t.notna() & (R.t > 30)].copy()
R['dg'] = (R.dist / 100).round()
R = R.sort_values('date')
# par: mean race time of EARLIER meetings at the same venue and distance (needs 5+), as % of par
def par_for(df):
    out = pd.Series(np.nan, index=df.index)
    for (v, d), grp in df.groupby(['venue', 'dg']):
        grp = grp.sort_values('date'); t = grp.t.values; dts = grp.date.values
        for i in range(len(grp)):
            prior = t[dts < dts[i]]
            if len(prior) >= 5: out.loc[grp.index[i]] = prior[-40:].mean()
    return out
R['par'] = par_for(R); R['speed'] = (R.t / R.par - 1) * 100       # + = slower than par
print('races', len(R), 'with a speed variant', R.speed.notna().sum(), 'meetings', R.meet.nunique())
R['md'] = R.meet
def icc(df, col):
    d = df.dropna(subset=[col]); k = d.groupby('md').size(); d = d[d.md.isin(k[k >= 2].index)]
    g_ = d.groupby('md')[col]; n = g_.size(); m = g_.mean(); grand = d[col].mean()
    msb = (n * (m - grand) ** 2).sum() / (len(m) - 1); msw = ((d[col] - g_.transform('mean')) ** 2).sum() / (len(d) - len(m)); n0 = (n.sum() - (n ** 2).sum() / n.sum()) / (len(m) - 1)
    return max(0.0, (msb - msw) / (msb + (n0 - 1) * msw))
R = R.sort_values(['md', 'rno'])
print('\nPart 1: in-meeting persistence (same meeting-day)')
for c in ('speed', 'lead', 'lane', 'early'):
    d = R.dropna(subset=[c]).copy(); d['i'] = d.groupby('md').cumcount()
    cs = d.groupby('md')[c].cumsum() - d[c]; d['e'] = (cs / d.i.replace(0, np.nan)).where(d.i >= 2)
    a = d.dropna(subset=['e'])
    print(f'  {c:6s} races {len(d):6d} sd {d[c].std():.3f} | meeting-day ICC {icc(d, c):.2f} | race vs mean of 2+ earlier races same day: corr {a[[c, "e"]].corr().iloc[0, 1]:+.2f} slope {np.polyfit(a.e, a[c], 1)[0]:+.2f} (n={len(a)})')
# as-of features per race (earlier races of the same meeting only), shrunk
for c, k in (('speed', 2.0), ('lead', 3.0), ('lane', 3.0), ('early', 3.0)):
    s = R.groupby('md')[c].transform(lambda x: x.fillna(0).cumsum().shift(1).fillna(0)); n = R.groupby('md')[c].transform(lambda x: x.notna().cumsum().shift(1).fillna(0))
    R['d_' + c] = np.where(n >= 1, s / (n + k), np.nan)
# ---- Part 2: usefulness for the Proj
rows = []
for f in sorted(glob.glob('data/tr_form/*.json.gz')):
    for r in json.load(gzip.open(f, 'rt')).get('runs', {}).values():
        if r.get('isBarrierTrial') or r.get('isJumpout') or r.get('wpr') is None: continue
        rows.append(dict(horse_id=r['horse_id'], date=r['date'], hname=r.get('horse')))
X = pd.DataFrame(rows); X['horse_id'] = pd.to_numeric(X.horse_id, errors='coerce'); X['date'] = pd.to_datetime(X.date); X['hn'] = G.norm(X.hname)
rp = C.training_frame().merge(X.drop_duplicates(['horse_id', 'date'], keep='last'), on=['horse_id', 'date'], how='left')
rp = rp.merge(g[['date', 'hn', 'rk']].drop_duplicates(['date', 'hn']), on=['date', 'hn'], how='left').merge(R[['rk', 'd_speed', 'd_lead', 'd_lane', 'd_early']], on='rk', how='left')
rp['cls_c'] = C._cls(rp.cls, sorted(rp.cls.dropna().unique().tolist()))
pg = rp[rp.f.notna() & rp.d_speed.notna()].copy()
cut, es = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')
tr, va, te = pg[pg.date < es], pg[(pg.date >= es) & (pg.date < cut)], pg[pg.date >= cut].copy()
print(f'\nPart 2: runs with in-meeting GPS features (2nd race of the meeting onward): train {len(tr)} valid {len(va)} test {len(te)}')
P = dict(n_estimators=3000, learning_rate=0.03, num_leaves=31, min_child_samples=60, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1)
def fit(feats):
    p = []
    for s in range(3):
        m = lgb.LGBMRegressor(**P, random_state=s).fit(tr[feats], tr.resid, eval_set=[(va[feats], va.resid)], callbacks=[lgb.early_stopping(100, verbose=False)]); p.append(m.predict(te[feats]))
    return np.mean(p, axis=0)
rm = lambda e: float(np.sqrt((e ** 2).mean()))
base = fit(C.FEATS); e0 = te.resid.values - base; te['miss'] = e0
print(f'  baseline live Proj context model RMSE {rm(e0):.4f}')
# race-level shared miss against the earlier races' speed variant
rl = te.groupby('rk').agg(miss=('miss', 'mean'), k=('miss', 'size'), spd=('d_speed', 'first')).query('k >= 3')
print(f'  race-level mean miss ({len(rl)} races, 3+ stored runners) vs earlier races\' speed variant (+ = slower): corr {rl[["miss", "spd"]].corr().iloc[0, 1]:+.3f}, slope {np.polyfit(rl.spd, rl.miss, 1)[0]:+.2f} rating pts per 1% of par')
for name, feats in (('in-meeting speed variant', ['d_speed']), ('in-meeting lane bias', ['d_lane']), ('in-meeting early-speed bias', ['d_early']), ('in-meeting position bias', ['d_lead']), ('all four', ['d_speed', 'd_lane', 'd_early', 'd_lead'])):
    e1 = te.resid.values - fit(C.FEATS + feats); d = e0 ** 2 - e1 ** 2
    print(f'  {name:30s} RMSE {rm(e1):.4f}  paired MSE gain {d.mean():+.3f} +-{1.96 * d.std() / np.sqrt(len(d)):.3f}')
