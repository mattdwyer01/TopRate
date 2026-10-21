"""Does a pre-race leader/closer bias (venue's earlier meetings, same day's earlier races) improve the live Proj? GPS subset (VIC/SA/QLD, 45% of runs, full-field race bias).
Race bias lead = Spearman(position after 400m, finish) from the GPS fields. As-of features per race, using ONLY earlier information:
  vb  = shrunk mean of the venue's previous 10 meetings' mean lead (earlier dates only)
  db  = shrunk mean of the same meeting's earlier races (race number lower)
Horse style (known pre-race) = mean position-after-400m fraction over its earlier GPS runs (h_ep, 0 = leads). The bias only helps a horse through its style, so the feature is bias x (0.5 - h_ep).
Baseline includes h_ep itself, so the gain is from the bias information. Target = ATW rating minus formula, baseline = live Proj context model (ctx.FEATS). Paired out-of-sample, 2026.
Run: PYTHONPATH=. python research/bias_usefulness_gps.py"""
import glob, gzip, json, sys
import numpy as np, pandas as pd, lightgbm as lgb
sys.path.insert(0, 'projection'); sys.path.insert(0, 'research')
import ctx as C, gps_counterfactual as G
g = G.gps_runs()
def sp(a, b):
    ok = a.notna() & b.notna()
    return float(a[ok].rank().corr(b[ok].rank())) if ok.sum() >= 6 and a[ok].nunique() > 1 and b[ok].nunique() > 1 else np.nan
R = g.groupby('rk').apply(lambda x: pd.Series(dict(lead=sp(x.ep_f, x.finish), n=len(x), date=x.date.iloc[0], venue=x.venue_k.iloc[0], meet=x.meet_.iloc[0], rno=x.race_no_.iloc[0]))).reset_index()
R = R[(R.n >= 8) & R.lead.notna()].copy(); R['date'] = pd.to_datetime(R.date)
M = R.groupby(['venue', 'date', 'meet']).lead.mean().reset_index().sort_values(['venue', 'date'])
M['prior'] = M.groupby('venue').lead.transform(lambda s: s.shift(1).rolling(10, min_periods=3).mean())
R = R.merge(M[['meet', 'prior']], on='meet', how='left').rename(columns={'prior': 'vb'})
R = R.sort_values(['meet', 'rno'])
cs = R.groupby('meet').lead.cumsum() - R.lead; cn = R.groupby('meet').cumcount()
R['db'] = (cs / (cn + 3.0)).where(cn >= 1)          # shrunk toward 0 (3 pseudo races)
# horse style from earlier GPS runs
g = g.sort_values(['hn', 'date']).reset_index(drop=True)
g['h_ep'] = g.groupby('hn').ep_f.transform(lambda s: s.shift(1).rolling(4, min_periods=1).mean())
rows = []
for f in sorted(glob.glob('data/tr_form/*.json.gz')):
    for r in json.load(gzip.open(f, 'rt')).get('runs', {}).values():
        if r.get('isBarrierTrial') or r.get('isJumpout') or r.get('wpr') is None: continue
        rows.append(dict(horse_id=r['horse_id'], date=r['date'], hname=r.get('horse')))
X = pd.DataFrame(rows); X['horse_id'] = pd.to_numeric(X.horse_id, errors='coerce'); X['date'] = pd.to_datetime(X.date); X['hn'] = G.norm(X.hname)
rp = C.training_frame().merge(X.drop_duplicates(['horse_id', 'date'], keep='last'), on=['horse_id', 'date'], how='left')
gk = g[['date', 'hn', 'rk', 'h_ep', 'ep_f']].drop_duplicates(['date', 'hn'])
rp = rp.merge(gk, on=['date', 'hn'], how='left').merge(R[['rk', 'vb', 'db']], on='rk', how='left')
rp['sty'] = 0.5 - rp.h_ep
rp['x_v'] = rp.vb * rp.sty; rp['x_d'] = rp.db * rp.sty; rp['x_both'] = (rp.vb.fillna(0) + 0.73 * rp.db.fillna(0)) * rp.sty
rp['cls_c'] = C._cls(rp.cls, sorted(rp.cls.dropna().unique().tolist()))
pg = rp[rp.f.notna() & rp.h_ep.notna() & rp.vb.notna()].copy()
cut, es = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')
tr, va, te = pg[pg.date < es], pg[(pg.date >= es) & (pg.date < cut)], pg[pg.date >= cut]
print(f'runs with GPS style + venue bias: train {len(tr)} valid {len(va)} test {len(te)}; share of test with same-day earlier races: {te.db.notna().mean():.0%}')
P = dict(n_estimators=3000, learning_rate=0.03, num_leaves=31, min_child_samples=60, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1)
def fit(feats):
    p = []
    for s in range(3):
        m = lgb.LGBMRegressor(**P, random_state=s).fit(tr[feats], tr.resid, eval_set=[(va[feats], va.resid)], callbacks=[lgb.early_stopping(100, verbose=False)]); p.append(m.predict(te[feats]))
    return np.mean(p, axis=0)
rm = lambda e: float(np.sqrt((e ** 2).mean()))
base_feats = C.FEATS + ['h_ep']
e0 = te.resid.values - fit(base_feats)
print(f'baseline (live Proj context model + the horse\'s own style) RMSE {rm(e0):.4f}')
for name, feats in (('venue leader bias x style', ['vb', 'x_v']), ('same-day earlier-race bias x style', ['db', 'x_d']), ('venue + same-day', ['vb', 'db', 'x_v', 'x_d', 'x_both'])):
    e1 = te.resid.values - fit(base_feats + feats); d = e0 ** 2 - e1 ** 2
    print(f'  {name:36s} RMSE {rm(e1):.4f}  paired MSE gain {d.mean():+.3f} +-{1.96 * d.std() / np.sqrt(len(d)):.3f}')
# simple direct check: does bias x style predict the miss after the baseline?
t = te.assign(e0=e0); a = t.dropna(subset=['x_both'])
print(f'\ncorr of the miss (after baseline) with (venue + day bias) x style: {a[["e0", "x_both"]].corr().iloc[0, 1]:+.3f}, slope {np.polyfit(a.x_both, a.e0, 1)[0]:+.2f} rating pts per unit (n={len(a)})')
for lab, m in (('strong leader bias day (bias>+0.3), front runners (sty>0.15)', (a.vb + 0.73 * a.db.fillna(0) > 0.3) & (a.sty > 0.15)), ('strong closer bias day (bias<-0.3), front runners', (a.vb + 0.73 * a.db.fillna(0) < -0.3) & (a.sty > 0.15)),
               ('strong leader bias day, backmarkers (sty<-0.15)', (a.vb + 0.73 * a.db.fillna(0) > 0.3) & (a.sty < -0.15)), ('strong closer bias day, backmarkers', (a.vb + 0.73 * a.db.fillna(0) < -0.3) & (a.sty < -0.15))):
    b = a[m]; print(f'  {lab:62s} n={len(b):5d} mean miss {b.e0.mean():+.2f} +-{1.96 * b.e0.std() / np.sqrt(max(len(b), 1)):.2f}')

# ---------------- Does bias x style predict how a horse FINISHES, beyond its rating? (ratings are margin based and likely bias adjusted; finishing order is not)
print('\n--- finishing order instead of rating (y = finish / field size, lower is better) ---')
fin = g[['date', 'hn', 'finish', 'n']].rename(columns={'n': 'gn'}).drop_duplicates(['date', 'hn']); rp2 = rp.merge(fin, on=['date', 'hn'], how='left')
rp2['y'] = (rp2.finish / rp2.gn).where((rp2.finish >= 1) & (rp2.finish <= rp2.gn))   # drop sentinel finishes (did not finish)
rp2['f_dm'] = rp2.f - rp2.groupby('rk').f.transform('mean')          # strength vs the stored runners of the race (partial field, noisy control)
rp2['cnt'] = rp2.groupby('rk').f.transform('count')
d = rp2[rp2.f.notna() & rp2.h_ep.notna() & rp2.vb.notna() & rp2.y.notna() & (rp2.cnt >= 5)].copy()
d['bias'] = d.vb + 0.73 * d.db.fillna(0)
d['x'] = d.bias * d.sty
tr2, te2 = d[d.date < cut], d[d.date >= cut]
import numpy.linalg as LA
def ols(df, cols):
    A = np.column_stack([np.ones(len(df))] + [df[c].values for c in cols]); b, *_ = LA.lstsq(A, df.y.values, rcond=None); return b
def pred(df, cols, b): return np.column_stack([np.ones(len(df))] + [df[c].values for c in cols]) @ b
for cols, lab in ((['f_dm', 'sty'], 'rating + style'), (['f_dm', 'sty', 'x'], 'rating + style + bias x style'), (['f_dm', 'sty', 'bias', 'x'], '+ bias alone')):
    b = ols(tr2, cols); e = te2.y.values - pred(te2, cols, b)
    print(f'  {lab:32s} test MSE {np.mean(e ** 2):.5f}   coefs ' + ' '.join(f'{c}={v:+.4f}' for c, v in zip(['int'] + cols, b)))
b0, b1 = ols(tr2, ['f_dm', 'sty']), ols(tr2, ['f_dm', 'sty', 'x'])
e0f = te2.y.values - pred(te2, ['f_dm', 'sty'], b0); e1f = te2.y.values - pred(te2, ['f_dm', 'sty', 'x'], b1); dd = e0f ** 2 - e1f ** 2
print(f'  paired MSE gain from bias x style (finish fraction): {dd.mean():+.6f} +-{1.96 * dd.std() / np.sqrt(len(dd)):.6f}  (n={len(te2)}, base MSE {np.mean(e0f ** 2):.5f}, so {dd.mean() / np.mean(e0f ** 2):+.2%})')
print('  mean finish fraction by situation (test set; 0.5 = field average, lower is better):')
for lab, m in (('leader-bias day, front runners (style>+0.15)', (te2.bias > 0.3) & (te2.sty > 0.15)), ('leader-bias day, backmarkers', (te2.bias > 0.3) & (te2.sty < -0.15)),
               ('closer-bias day, front runners', (te2.bias < -0.3) & (te2.sty > 0.15)), ('closer-bias day, backmarkers', (te2.bias < -0.3) & (te2.sty < -0.15)), ('no clear bias (|bias|<0.1), front runners', (te2.bias.abs() < 0.1) & (te2.sty > 0.15)), ('no clear bias, backmarkers', (te2.bias.abs() < 0.1) & (te2.sty < -0.15))):
    b = te2[m]; print(f'    {lab:48s} n={len(b):5d} finish fraction {b.y.mean():.3f} +-{1.96 * b.y.std() / np.sqrt(max(len(b), 1)):.3f}   rating z {b.f_dm.mean():+.2f}')
