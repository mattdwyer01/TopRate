"""Energy-burn test. Hindsight ceiling first: when a horse is faster early than it usually is (or the race pace is hot), does
it finish worse than its prior rating says? Judged on CONTENDERS (top 4 by prior rating in the race) and on winner / top-4 finish,
not on the whole field. GPS early speed: VIC/SA (racing.com first two sections) and QLD (RQ first two 200m sections)."""
import os, sys
import numpy as np, pandas as pd, lightgbm as lgb
sys.path.insert(0, os.path.dirname(__file__))
import build_trip_map as B
res = B.load_results()
full = pd.concat([pd.read_csv(f, usecols=['race_id', 'horse_id', 'positionFinish', 'marginFinish', 'wpr'], low_memory=False) for f in sorted(__import__('glob').glob(os.path.join(B.ROOT, 'race_results_20*.csv.gz')))]).drop_duplicates(['race_id', 'horse_id'])
res = B.add_result_features(res).merge(full[['race_id', 'horse_id', 'positionFinish', 'marginFinish']], on=['race_id', 'horse_id'], how='left')
res = res.sort_values(['horse_id', 'date', 'race_id'])
gh = res.groupby('horse_id')
res['prior3'] = gh.wpr.transform(lambda s: s.shift(1).rolling(3, min_periods=2).mean())
a = pd.concat([B.vicsa_runs(res), B.qld_runs(res)], ignore_index=True)
a = a.merge(res[['race_id', 'horse_id', 'prior3', 'wpr', 'positionFinish', 'marginFinish']], on=['race_id', 'horse_id'], how='left')
a = a[(a.fs >= 8) & a.prior3.notna() & a.wpr.notna() & a.early.notna()].sort_values(['horse_id', 'date', 'race_id']).reset_index(drop=True)
g = a.groupby('horse_id')
a['early_h8'] = g.early.transform(lambda s: s.shift(1).rolling(8, min_periods=2).mean())
a['settle_h8'] = g.settle.transform(lambda s: s.shift(1).rolling(8, min_periods=2).mean())
a['burn'] = a.early - a.early_h8                      # faster early than usual (hindsight, in-race early speed demeaned)
rc = ['race_id']
a['pace'] = a.groupby(rc).early.transform(lambda s: s.nlargest(3).mean())   # how hot the front end was (m/s above field mean)
a['y'] = a.wpr - a.prior3
a['yc'] = a.y - a.groupby(rc).y.transform('mean')
a['rank_prior'] = a.groupby(rc).prior3.rank(ascending=False, method='first')
a['cont'] = a.rank_prior <= 4
a['top4'] = (a.positionFinish <= 4).astype(float); a['win'] = (a.positionFinish == 1).astype(float)
a = a[a.burn.notna()]
print('runs', len(a), 'races', a.race_id.nunique(), 'contenders', int(a.cont.sum()), flush=True)
def slope(d, x, lab):
    X = d[x] - d.groupby(rc)[x].transform('mean') if x != 'pace' else d[x]
    c = np.polyfit(X, d.yc, 1) if x != 'pace' else np.polyfit(d[x], d.yc, 1)
    r = np.corrcoef(X, d.yc)[0, 1]
    print(f'  {lab:46s} n={len(d):6d} WPR per +1 m/s {c[0]:+6.2f} corr {r:+.3f}')
for nm, d in (('ALL', a), ('CONTENDERS (top 4 by prior)', a[a.cont]), ('contenders who burned (top third burn)', a[a.cont & (a.burn > a.burn.quantile(.67))])):
    print(nm)
    slope(d, 'burn', 'finish residual vs early burn (hindsight)')
    slope(d, 'early', 'finish residual vs absolute early speed')
# interaction: burn at hot pace vs slow pace, and forward vs back horses
c = a[a.cont].copy()
c['hot'] = c.pace > a.pace.quantile(.67); c['slow'] = c.pace < a.pace.quantile(.33)
c['fwd'] = c.settle_h8 < 0.3
print('contenders by pace x style: mean finish residual (WPR) for burners (burn>0.3 m/s) vs not')
for lab, m in (('hot pace', c.hot), ('slow pace', c.slow)):
    for lab2, m2 in (('forward types', c.fwd), ('midfield/back', ~c.fwd)):
        s = c[m & m2]; b = s[s.burn > 0.3]; n = s[s.burn <= 0.3]
        print(f'  {lab:10s} {lab2:14s} burners n={len(b):5d} resid {b.yc.mean():+.2f}  others n={len(n):5d} resid {n.yc.mean():+.2f}  diff {b.yc.mean()-n.yc.mean():+.2f}')
# does it move top-4 / win rates among contenders, holding prior rank
for y in ('top4', 'win'):
    b = c[c.burn > 0.3]; n = c[c.burn <= 0.3]
    print(f'contenders {y}: burners {b[y].mean():.3f} (n={len(b)}) vs others {n[y].mean():.3f} (n={len(n)}); by prior rank 1-2 burners {c[(c.rank_prior<=2)&(c.burn>0.3)][y].mean():.3f} vs {c[(c.rank_prior<=2)&(c.burn<=0.3)][y].mean():.3f}')
# model ceiling: finish residual from hindsight burn/pace features vs without, judged on contenders
tr = a[a.date < '2025-01-01']; te = a[(a.date >= '2025-01-01') & a.cont]
fb = ['distance', 'barrier', 'barfrac', 'fs', 'rail_m', 'going_s', 'settle', 'rank_prior', 'prior3']
fh = fb + ['burn', 'early', 'pace', 'early_h8']
for lab, f in (('no early info', fb), ('+ hindsight early speed', fh)):
    m = lgb.train(dict(B.PARAMS, num_threads=4), lgb.Dataset(tr[f], tr.yc), 300)
    p = m.predict(te[f]); print(f'{lab:28s} contender residual rmse {np.sqrt(((p - te.yc) ** 2).mean()):.3f} (null {te.yc.std():.3f})')
