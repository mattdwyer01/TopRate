"""Anticipating Proj misses before the run (23 Oct 2026). Base: out-of-sample Huber-4 Proj for 2025 (models fit before 2025) and 2026 (before 2026), cached by
analysis/trip_map/train_ctx_gps.py in /tmp/train_ctx_gps_oos.parquet (run that first). miss = actual ATW rating - Proj.
Second stage fitted on 2025 and scored on 2026, pre-race inputs only: the Proj context and relevance features, the horse's own earlier misses against this Proj,
excuses on its last run, bounce signals (last run vs career best), and (variant) the starting price.
Targets: bad run (miss < -12), big beat (miss > +12), size of the miss, and the miss itself. Reported on all runs, the top half by prior rating and the top 4.
Then: does knowing the risk help pick winners? (partial fields, conditional logit with and without the price.) Run: PYTHONPATH=. python research/miss_anticipation.py"""
import os, sys
import numpy as np, pandas as pd, lightgbm as lgb
from sklearn.metrics import roc_auc_score
from scipy.optimize import minimize
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'projection'))
import ctx as C

pg = pd.read_parquet('/tmp/train_ctx_gps_oos.parquet')
pg['date'] = pd.to_datetime(pg.date)
pg = pg.sort_values(['horse_id', 'date']).reset_index(drop=True)
pg['miss'] = pg.wpr - pg.proj0
g = pg.groupby('horse_id')
# the horse's own earlier misses against this Proj (only runs inside 2025-26 have one, so early rows are blank)
pg['pm1'] = g.miss.shift(1)
pg['pm_mean3'] = g.miss.transform(lambda s: s.shift(1).rolling(3, min_periods=1).mean())
pg['pm_bad4'] = g.miss.transform(lambda s: (s < -12).astype(float).shift(1).rolling(4, min_periods=1).sum())
pg['pm_good4'] = g.miss.transform(lambda s: (s > 12).astype(float).shift(1).rolling(4, min_periods=1).sum())
pg['pm_abs3'] = g.miss.transform(lambda s: s.abs().shift(1).rolling(3, min_periods=1).mean())
# excuse words on the previous run
txt = pg.comments_steward.fillna('').str.lower()
for k, p in {'ex_vet': r'(?:vet\b|lame|bled|bleed|arrhythm|cardiac|sore|injur|distress|respirat)', 'ex_eased': r'(?:eased|not persevered|dropped out|tailed off|failed to)',
             'ex_slow': r'(?:slow(?:ly)? away|began awkward|missed the start|fumbled|dwelt|stumbled|reared)', 'ex_block': r'(?:held up|blocked|checked|hampered|bumped|interfer|steadied|crowded|shut in|not clear)',
             'ex_keen': r'(?:resented|over ?raced|raced keenly|pulled hard|fought)'}.items():
    pg[k] = g[k].shift(1) if False else txt.str.contains(p, regex=True).astype(float)
    pg[k + '_prev'] = pg.groupby('horse_id')[k].shift(1)
pg['bounce'] = pg.r1 - pg.cmax_vs_f if 'cmax_vs_f' in pg else np.nan
pg['last_vs_mean3'] = pg.r1 - pg.mean3
pg['proj_minus_max4'] = pg.proj0 - pg.max4
pg['proj_minus_mean3'] = pg.proj0 - pg.mean3
pg['lp'] = -np.log(pg.priceStarting.where(pg.priceStarting > 1))
pg['race_key'] = pg.date.astype(str) + '|' + pg.vn.astype(str) + '|' + pg.distance.astype(str)
pg['days_log'] = np.log1p(pg.ldays)
pg['bad'] = (pg.miss < -12).astype(int); pg['beat'] = (pg.miss > 12).astype(int); pg['absm'] = pg.miss.abs()
BASEF = ['proj0'] + [c for c in C.FEATS if c in pg.columns] + [c for c in C.REL_FEATS if c in pg.columns]
OWN = ['pm1', 'pm_mean3', 'pm_bad4', 'pm_good4', 'pm_abs3']
EXC = [k + '_prev' for k in ('ex_vet', 'ex_eased', 'ex_slow', 'ex_block', 'ex_keen')]
BNC = ['bounce', 'last_vs_mean3', 'proj_minus_max4', 'proj_minus_mean3', 'days_log']
SETS = {'context only': BASEF, '+ own earlier misses': BASEF + OWN, '+ excuses, bounce': BASEF + OWN + EXC + BNC, '+ price': BASEF + OWN + EXC + BNC + ['lp']}
tr = pg[(pg.date < '2026-01-01') & (pg.n >= 3)]
te = pg[(pg.date >= '2026-01-01') & (pg.n >= 3)].copy()
print('train (2025)', len(tr), 'test (2026)', len(te), '| base rates in test: bad %.1f%%, big beat %.1f%%' % (100 * te.bad.mean(), 100 * te.beat.mean()), flush=True)
P = dict(objective='binary', learning_rate=0.03, num_leaves=15, min_data_in_leaf=200, feature_fraction=0.7, bagging_fraction=0.8, bagging_freq=1, lambda_l2=10, verbose=-1, num_threads=4)
def fitc(feats, y, rounds=300):
    return lgb.train(P, lgb.Dataset(tr[feats], tr[y]), rounds)
sub = {'all runs': np.ones(len(te), bool), 'top half by prior': (te.half == True).values, 'runs with 3+ earlier misses': (te.pm_abs3.notna() & te.pm1.notna()).values}
res = {}
for tgt in ('bad', 'beat'):
    print(f'\n== {tgt.upper()} ({"miss below -12" if tgt == "bad" else "miss above +12"}) ==')
    for k, f in SETS.items():
        m = fitc(f, tgt); p = m.predict(te[f]); res[(tgt, k)] = p
        out = [f'{k:24s}']
        for lab, msk in sub.items():
            y = te[tgt].values[msk]; out.append(f'{lab}: AUC {roc_auc_score(y, p[msk]):.3f}')
        print('  ' + ' | '.join(out))
    p = res[(tgt, '+ excuses, bounce')]
    q = pd.qcut(pd.Series(p), 5, labels=False, duplicates='drop').values
    print('  calibration by predicted-risk quintile (no price): predicted / actual', [(round(float(p[q == i].mean()), 3), round(float(te[tgt].values[q == i].mean()), 3)) for i in range(5)])
    top = p >= np.quantile(p, .9)
    print('  top-decile risk: actual rate %.1f%% vs %.1f%% overall (lift %.2f), share of all such runs captured %.1f%%' % (100 * te[tgt].values[top].mean(), 100 * te[tgt].mean(), te[tgt].values[top].mean() / te[tgt].mean(), 100 * te[tgt].values[top].sum() / te[tgt].sum()))
    m = fitc(SETS['+ excuses, bounce'], tgt)
    imp = pd.Series(m.feature_importance('gain'), index=SETS['+ excuses, bounce']).sort_values(ascending=False)
    print('  top inputs by gain:', ', '.join(f'{i} {100 * v / imp.sum():.0f}%' for i, v in imp.head(8).items()))
# size of the miss
print('\n== SIZE OF THE MISS (|miss|) ==')
PR = dict(objective='regression', learning_rate=0.03, num_leaves=15, min_data_in_leaf=200, feature_fraction=0.7, bagging_fraction=0.8, bagging_freq=1, lambda_l2=10, verbose=-1, num_threads=4)
for k, f in SETS.items():
    m = lgb.train(PR, lgb.Dataset(tr[f], tr.absm), 300); p = m.predict(te[f])
    r = np.corrcoef(p, te.absm)[0, 1]
    qs = pd.qcut(pd.Series(p), 5, labels=False)
    print(f'  {k:24s} corr {r:.3f} | RMSE of the miss by predicted-size quintile', [round(float(np.sqrt((te.miss.values[qs.values == i] ** 2).mean())), 2) for i in range(5)])
# direction: second-stage Huber miss
print('\n== DIRECTION (the miss itself, Huber 4 second stage) ==')
PH = dict(PR, objective='huber', alpha=4.0)
def st(e): return f'MAE {np.abs(e).mean():.3f} within3 {100 * (np.abs(e) <= 3).mean():.1f}% rmse {np.sqrt((e ** 2).mean()):.3f}'
for lab, msk in sub.items():
    print('  ', lab, '| Proj as is:', st(te.miss.values[msk]))
for k, f in SETS.items():
    m = lgb.train(PH, lgb.Dataset(tr[f], tr.miss), 300); pm = m.predict(te[f]); te['pm_' + k] = pm
    print(f'   {k:24s}' + ' | '.join(f'{lab}: {st(te.miss.values[msk] - pm[msk])}' for lab, msk in list(sub.items())[:2]))
# winners: does knowing the risk help? partial fields, conditional logit, cross-fitted on date halves of 2026
print('\n== WINNERS (races with >= 6 Proj runners and the winner among them; cross-fit by date halves) ==')
te['p_bad'] = res[('bad', '+ excuses, bounce')]; te['p_beat'] = res[('beat', '+ excuses, bounce')]
te['p_bad_px'] = res[('bad', '+ price')]
w = te[te.rid.notna() & te.priceStarting.notna() & (te.priceStarting > 1)].copy()
w['win'] = (w.positionFinish == 1).astype(int)
gb = w.groupby('rid')
w = w[(gb.win.transform('sum') == 1) & (gb.win.transform('size') >= 6)].copy()
def cen(c): return w[c] - w.groupby('rid')[c].transform('mean')
w['x_proj'] = cen('proj0'); w['x_dir'] = cen('pm_+ excuses, bounce'); w['x_bad'] = cen('p_bad'); w['x_beat'] = cen('p_beat'); w['x_lp'] = cen('lp')
w['x_projdir'] = w.x_proj + w.x_dir
d0 = w.date.sort_values().iloc[len(w) // 2]
def nll(par, d, cols):
    s = sum(p * d[c].values for p, c in zip(par, cols)); e = pd.Series(s, index=d.index)
    mx = e.groupby(d.rid).transform('max'); ex = np.exp(e - mx); den = ex.groupby(d.rid).transform('sum')
    return -np.log(ex / den)[d.win == 1].sum(), np.log(ex / den)[d.win == 1]
def cross(cols):
    ll = []
    for a, b in ((w[w.date < d0], w[w.date >= d0]), (w[w.date >= d0], w[w.date < d0])):
        r = minimize(lambda p: nll(p, a, cols)[0], np.full(len(cols), 0.05), method='Nelder-Mead')
        ll.append(nll(r.x, b, cols)[1])
    return pd.concat(ll)
print('races', w.rid.nunique(), 'runners', len(w))
base_p = cross(['x_proj']); base_m = cross(['x_lp', 'x_proj'])
for lab, cols in (('Proj + direction (second stage)', ['x_projdir']), ('Proj + bad-run risk', ['x_proj', 'x_bad']), ('Proj + risk + big-beat chance', ['x_proj', 'x_bad', 'x_beat']), ('Proj + direction + risk', ['x_projdir', 'x_bad', 'x_beat'])):
    l = cross(cols); d = (l - base_p).dropna()
    print(f'  {lab:34s} winner LL {l.mean():.4f} vs Proj alone {base_p.mean():.4f}: gain {d.mean():+.4f} (se {d.std() / np.sqrt(len(d)):.4f})')
for lab, cols in (('market + Proj + risk', ['x_lp', 'x_proj', 'x_bad', 'x_beat']), ('market + Proj + direction + risk', ['x_lp', 'x_projdir', 'x_bad', 'x_beat'])):
    l = cross(cols); d = (l - base_m).dropna()
    print(f'  {lab:34s} winner LL {l.mean():.4f} vs market + Proj {base_m.mean():.4f}: gain {d.mean():+.4f} (se {d.std() / np.sqrt(len(d)):.4f})')
