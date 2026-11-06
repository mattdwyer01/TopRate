"""6 Nov 2026 (owner, after Point Of Law: Geelong Cup 91.6 Proj -> 101.8, Melbourne Cup 97.1 -> 108.5). What predicts the upside tail (a run 10+ above the live formula) for horses coming to Australia with overseas
form? Page store, target = an Australian run whose last 3 earlier runs include an overseas or Hong Kong run, 2018 on. Tail = actual page rating minus the live formula figure (outlier trim as live) of +10 or more.
Univariate tail rates by as-of features, then a 5-fold cross-validated logistic regression and a small LightGBM on the same features (AUC, lift of the top fifth).
Run: PYTHONPATH=. python research/import_upside_test.py"""
import gzip, json, glob, re, numpy as np, pandas as pd
from sklearn.linear_model import LogisticRegression
from sklearn.model_selection import StratifiedKFold, cross_val_predict
from sklearn.metrics import roc_auc_score
from sklearn.pipeline import make_pipeline
from sklearn.preprocessing import StandardScaler
import lightgbm as lgb
co = json.load(open('projection/models_tr/formula.json'))['coef']
def form(l):
    l = np.array(l, float); n = min(len(l), 8); l = l[:n]
    if n >= 2:
        med = np.median(l[:6]); l = np.maximum(l, med - 10)
    c = co[str(n)]; return c[0] + np.dot(c[1:], l)
rn = pd.read_csv('runners.csv', usecols=['venue', 'state'], low_memory=False)
hk_pat = r'sha tin|happy valley'
aus = set(rn[rn.state != 'HK'].venue.str.lower().unique())
for _f in sorted(glob.glob('race_results_20*.csv.gz')) + ['runners_archive.csv.gz']:
    try:
        _x = pd.read_csv(_f, usecols=lambda c: c in ('track', 'venue'), compression='gzip', low_memory=False)
        for _c in _x.columns: aus |= set(_x[_c].dropna().astype(str).str.lower().unique())
    except Exception: pass
aus = {a for a in aus if not re.search(hk_pat, a)}
rows = []
for f in sorted(glob.glob('data/tr_form/*.json.gz')):
    for k, v in json.load(gzip.open(f))['runs'].items():
        if v.get('wpr') is None or v.get('isBarrierTrial') or v.get('isJumpout'): continue
        rows.append((v['horse_id'], v['date'], v['wpr'], str(v.get('track')), str(v.get('going')), v.get('weightCarried'), v.get('distance'), v.get('starters'), v.get('positionFinish'), v.get('marginFinish'), v.get('prizeMoney')))
d = pd.DataFrame(rows, columns=['h', 'date', 'r', 'track', 'going', 'wt', 'dist', 'field', 'pos', 'mgn', 'prize']).drop_duplicates(['h', 'date']).sort_values(['h', 'date'])
t = d.track.str.lower(); g = d.going.str.lower()
word = g.str.match(r'^(firm|fast|good|sand|dead|slow|soft|heavy|yielding)\b') & ~g.str.contains(r'\d')
d['os'] = (word & ~t.isin(aus)) | t.str.contains(hk_pat)
out = []
for h, x in d.groupby('h'):
    r = x.r.values; os_ = x.os.values; dt = x.date.values
    wt, di, fi, po, mg, pz = (x[c].values.astype(float) for c in ('wt', 'dist', 'field', 'pos', 'mgn', 'prize'))
    for i in range(3, len(r)):
        if dt[i] < '2018-01-01' or os_[i]: continue
        if not os_[i - 3:i].any(): continue
        l = r[max(0, i - 8):i][::-1]
        days = (pd.Timestamp(dt[i]) - pd.Timestamp(dt[i - 1])).days
        out.append(dict(res=r[i] - form(l), m3=l[:3].mean(), r1=l[0], rise3=l[0] - l[2], up3=float(l[0] > l[1] > l[2]), nrun=len(l), days=days,
                        os_n3=float(os_[i - 3:i].sum()), last_os=float(os_[i - 1]), wt_chg=wt[i] - wt[i - 1], dist_chg=di[i] - di[i - 1], lprize=np.log1p(np.nan_to_num(pz[i])),
                        prize_chg=np.log1p(np.nan_to_num(pz[i])) - np.log1p(np.nan_to_num(pz[i - 1])), field=fi[i], last_win=float(po[i - 1] == 1), last_wins2=float((po[i - 1] == 1) + (po[i - 2] == 1)),
                        last_field=fi[i - 1], last_mgn=mg[i - 1], dist=di[i], wt=wt[i], old_gap=l[:3].mean() - (l[3:].mean() if len(l) > 3 else np.nan)))
o = pd.DataFrame(out)
o['tail'] = (o.res >= 10).astype(int)
print(f'population: n={len(o)}  mean resid {o.res.mean():+.2f} median {o.res.median():+.2f}  tail rate (resid >= +10): {100*o['tail'].mean():.1f}%  | resid <= -10: {100*(o.res<=-10).mean():.1f}%')
base = o['tail'].mean()
def rate(name, m):
    a = o[m]
    if len(a) >= 25: print(f'  {name:46s} n={len(a):5d} tail {100*a['tail'].mean():5.1f}% (x{a['tail'].mean()/base:.2f}) mean resid {a.res.mean():+5.2f} median {a.res.median():+5.2f}')
print('\nunivariate tail rates:')
rate('last run overseas', o.last_os == 1); rate('last run in Australia (second/third start)', o.last_os == 0)
for lo, hi in ((-99, 0), (0, 4), (4, 8), (8, 99)): rate(f'rise over last 3 runs in [{lo},{hi})', o.rise3.between(lo, hi, inclusive='left'))
rate('three straight rises', o.up3 == 1); rate('not three straight rises', o.up3 == 0)
for lo, hi in ((0, 85), (85, 92), (92, 98), (98, 130)): rate(f'last-3 average in [{lo},{hi})', o.m3.between(lo, hi, inclusive='left'))
rate('won last start', o.last_win == 1); rate('did not win last start', o.last_win == 0)
rate('won last two', o.last_wins2 == 2)
for lo, hi in ((-99, 0), (0, 4), (4, 8), (8, 99)): rate(f'last-3 above runs 4-8 by [{lo},{hi})', o.old_gap.between(lo, hi, inclusive='left'))
for lo, hi in ((0, 50), (50, 120), (120, 400), (400, 9999)): rate(f'days since last run [{lo},{hi})', o.days.between(lo, hi, inclusive='left'))
rate('weight down 1kg+ vs last run', o.wt_chg <= -1); rate('weight up 1kg+', o.wt_chg >= 1)
rate('distance drop 400m+', o.dist_chg <= -400); rate('distance up 400m+', o.dist_chg >= 400)
for lo, hi in ((0, 10), (10, 12), (12, 13), (13, 99)): rate(f'log prize today in [{lo},{hi})', o.lprize.between(lo, hi, inclusive='left'))
rate('prize up vs last run (log +0.5)', o.prize_chg >= 0.5); rate('prize down vs last run', o.prize_chg <= -0.5)
for lo, hi in ((0, 8), (8, 12), (12, 99)): rate(f'field today in [{lo},{hi})', o.field.between(lo, hi, inclusive='left'))
rate('3 of last 3 overseas', o.os_n3 == 3); rate('1 of last 3 overseas', o.os_n3 == 1)
F = ['m3', 'r1', 'rise3', 'up3', 'nrun', 'days', 'os_n3', 'last_os', 'wt_chg', 'dist_chg', 'lprize', 'prize_chg', 'field', 'last_win', 'last_wins2', 'last_field', 'last_mgn', 'dist', 'wt', 'old_gap']
X = o[F].copy(); X = X.fillna(X.median()); y = o['tail'].values
cv = StratifiedKFold(5, shuffle=True, random_state=1)
for nm, mdl in (('logistic', make_pipeline(StandardScaler(), LogisticRegression(C=0.3, max_iter=2000))),
                ('lightgbm', lgb.LGBMClassifier(n_estimators=150, learning_rate=0.03, num_leaves=4, min_child_samples=40, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, verbose=-1))):
    p = cross_val_predict(mdl, X, y, cv=cv, method='predict_proba')[:, 1]
    top = p >= np.quantile(p, 0.8)
    print(f'\n{nm}: 5-fold AUC {roc_auc_score(y, p):.3f}  | top fifth by predicted tail: {100*y[top].mean():.1f}% vs {100*y[~top].mean():.1f}% for the rest (base {100*base:.1f}%)')
lr = make_pipeline(StandardScaler(), LogisticRegression(C=0.3, max_iter=2000)).fit(X, y)
print('logistic coefficients (per sd):', {f: round(c, 2) for f, c in sorted(zip(F, lr[-1].coef_[0]), key=lambda z: -abs(z[1]))[:8]})
