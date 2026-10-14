"""STANDALONE speed model (14 Oct 2026). Part 1 found speed features add nothing to the market-residual bet model; this tests them as their OWN model:\nno market input, no own WPR, only speed figure (raw and weight-adjusted), early speed, closing speed and basic race context.\nCompared with a ratings-only (own WPR) model built the same way, and judged on value (strike rate vs price, flat ROI at SP by model rank and by EV).\nOlder docstring follows.
Does a time-based, track-variant-corrected, weight-adjusted speed figure add anything to the bet model? (read-only analysis, 14 Oct 2026)
Figure: runner speed = distance / (winner's time + 0.146 s x margin), divided by the expected winner speed for track x distance x going
(fitted on races before 2021 only) and by the day's track variant (shrunk mean of the meeting's winner ratios), in per mille above par.
Weight adjusted by a within-horse slope fitted on pre-2022 runs. Features are as-of (shifted within horse). Walk-forward exactly as
betsignal/backtest.py, with and without the speed features, 3 seeds. usage: python wpr_speed_fig_betsignal_test.py [seeds]"""
import glob, os, sys
import numpy as np, pandas as pd, lightgbm as lgb
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from betsignal import features as F
from betsignal.score import tier
from betsignal.train import PARAMS, logit

SEEDS = tuple(range(1, int(sys.argv[1]) + 1)) if len(sys.argv) > 1 else (1, 2, 3)
ROOT = F.ROOT
S_PER_LEN = 0.146
F.USECOLS = F.USECOLS + ['winners_time', 'margin800m', 'margin600m', 'margin400m', 'margin200m']

# ---- race level table, all non-trial races (baseline needs history before 2018-06 too)
files = sorted(glob.glob(os.path.join(ROOT, 'race_results_20*.csv.gz')))
R = pd.concat([pd.read_csv(f, usecols=lambda c: c in ('race_id', 'date', 'track', 'distance', 'going', 'winners_time', 'isBarrierTrial', 'is_jumpout'), low_memory=False) for f in files])
R = R[(R.isBarrierTrial != True) & (R.is_jumpout != True)].drop_duplicates('race_id')
R['date'] = pd.to_datetime(R.date)
R['wt'] = pd.to_numeric(R.winners_time, errors='coerce')
R['spd'] = R.distance / R.wt
R = R[(R.spd > 10) & (R.spd < 20)].copy()
R['db'] = (R.distance / 100).round()
R['gb'] = pd.cut(R.going.map(F.going_number), [-1, 4, 7, 20], labels=['dry', 'soft', 'heavy']).astype(str)
tr = R[R.date < '2021-01-01']
E0 = tr.groupby('db').spd.mean()


def hier(df, keys, parent, k=15):
    a = tr.groupby(keys).spd.agg(['sum', 'count']).reset_index()
    m = df[keys].merge(a, on=keys, how='left')
    n = m['count'].fillna(0).values
    cell = (m['sum'] / m['count']).values
    w = n / (n + k)
    return np.where(np.isfinite(cell), w * cell + (1 - w) * parent, parent)


p0 = R.db.map(E0).fillna(E0.mean()).values
R['E'] = hier(R, ['track', 'db', 'gb'], hier(R, ['track', 'db'], p0))
R['rr'] = R.spd / R.E
g = R.groupby(['track', 'date']).rr.agg(['sum', 'count'])
R = R.merge(g, left_on=['track', 'date'], right_index=True)
R['var'] = (R['sum'] + 3 * 1.0) / (R['count'] + 3)          # shrunk toward par, 3 pseudo races
print('races with a speed baseline', len(R), 'meetings', len(g))

# ---- runner level
H = F.load_history()
H = H.merge(R[['race_id', 'wt', 'E', 'var', 'spd']], on='race_id', how='left')
H['rspeed'] = H.distance / (H.wt + S_PER_LEN * H.marginFinish.clip(lower=0).fillna(0))
H['fig0'] = ((H.rspeed / H.E) / H['var'] - 1) * 1000
H.loc[(H.fig0 < -60) | (H.fig0 > 40), 'fig0'] = np.nan      # bad times / extreme margins
print('runner rows with figure', H.fig0.notna().mean().round(3))

# weight slope: within horse, pre-2022, per mille per kg
fit = H[(H.date < '2022-01-01') & H.fig0.notna()].copy()
fit['fd'] = fit.fig0 - fit.groupby('horse_id').fig0.transform('mean')
fit['wd'] = fit.weightCarried - fit.groupby('horse_id').weightCarried.transform('mean')
fit['distb'] = (fit.distance / 200).round()
kw = {}
for b, s in fit.groupby('distb'):
    if len(s) > 500:
        kw[b] = (s.fd * s.wd).sum() / (s.wd ** 2).sum()
K = (fit.fd * fit.wd).sum() / (fit.wd ** 2).sum()
print(f'weight slope overall {K:+.3f} per mille per kg (negative = heavier is slower)  by distance:', {int(b * 200): round(v, 2) for b, v in sorted(kw.items())})
H['fig'] = H.fig0 - K * (H.weightCarried - 56.0)               # figure at 56kg

# ---- check how the figure relates to our rating
print('corr(fig, wpr) same run', H[['fig', 'wpr']].corr().iloc[0, 1].round(3))

# ---- as-of features
H = H.sort_values(['horse_id', 'date', 'raceNumber'])
h = H.groupby('horse_id')
for k in (1, 2, 3):
    H[f's{k}'] = h.fig.shift(k)
H['savg3'] = H[['s1', 's2', 's3']].mean(axis=1)
H['sbest'] = h.fig.transform(lambda s: s.shift(1).expanding().max())
H['sraw1'] = h.fig0.shift(1)
H['s_vs_w'] = H.s1 - h.wpr.shift(1)
r = H.groupby('race_id')
H['savg3_rel'] = H.savg3 - r.savg3.transform('max')
H['savg3_mean'] = H.savg3 - r.savg3.transform('mean')
SPEED = ['s1', 's2', 's3', 'savg3', 'sbest', 'savg3_rel', 'savg3_mean']
print('corr(savg3, wpr avg of same 3 runs) as of', pd.concat([H.savg3, pd.concat([h.wpr.shift(k) for k in (1, 2, 3)], axis=1).mean(axis=1)], axis=1).corr().iloc[0, 1].round(3))

# ---- non-weight-adjusted twin of the speed features (same figure, no weight correction), for the raw vs adjusted comparison
for k in (2, 3):
    H[f'raw{k}'] = h.fig0.shift(k)
H['raw1'] = H.sraw1
H['ravg3'] = H[['raw1', 'raw2', 'raw3']].mean(axis=1)
H['rbest'] = h.fig0.transform(lambda s: s.shift(1).expanding().max())
H['ravg3_rel'] = H.ravg3 - H.groupby('race_id').ravg3.transform('max')
H['ravg3_mean'] = H.ravg3 - H.groupby('race_id').ravg3.transform('mean')
SPEED_RAW = ['raw1', 'raw2', 'raw3', 'ravg3', 'rbest', 'ravg3_rel', 'ravg3_mean']
print('corr raw vs weight-adjusted avg3', H[['ravg3', 'savg3']].corr().iloc[0, 1].round(3))

# ---- early speed and closing speed from the race-call margins (lengths behind the leader at each call; not TopRate-authored)
KLEN = (-K / 1000) * 84.0 / S_PER_LEN      # lengths per kg over a ~84s race
for c in ('margin800m', 'margin600m', 'margin400m', 'margin200m', 'marginFinish'):
    H[c] = pd.to_numeric(H[c], errors='coerce').clip(0, 40)
H['fin_m'] = H.marginFinish
H.loc[H.positionFinish == 1, 'fin_m'] = 0.0
wadj = lambda leg: KLEN * (H.weightCarried - 56.0) * leg / H.distance          # extra lengths a heavier horse gives away over `leg` metres
H['g400'] = H.margin400m - H.fin_m + wadj(400)       # lengths gained on the leader over the last 400m (weight adjusted)
H['g200'] = H.margin200m - H.fin_m + wadj(200)
H['g600'] = H.margin600m - H.fin_m + wadj(600)
H['e800'] = -H.margin800m                              # lengths ahead of the leader-relative position at the 800m (early)
for c in ('g400', 'g200', 'g600', 'e800'):
    H[c + '_r'] = H[c] - H.groupby('race_id')[c].transform('median')     # relative to the field in the same race
H = H.sort_values(['horse_id', 'date', 'raceNumber'])
h = H.groupby('horse_id')
for c in ('g400_r', 'g200_r', 'g600_r', 'e800_r'):
    H[c + '_1'] = h[c].shift(1)
    H[c + '_a3'] = h[c].transform(lambda s: s.shift(1).rolling(3, min_periods=1).mean())
H['g400_best'] = h.g400_r.transform(lambda s: s.shift(1).rolling(5, min_periods=1).max())
H['g200_best'] = h.g200_r.transform(lambda s: s.shift(1).rolling(5, min_periods=1).max())
r = H.groupby('race_id')
H['e_rel'] = H.e800_r_a3 - r.e800_r_a3.transform('mean')
H['g_rel'] = H.g400_r_a3 - r.g400_r_a3.transform('mean')
H['n_early'] = r.e800_r_a3.transform(lambda s: (s > 1.5).sum())                # runners that usually jump to the front or close to it
H['early_top3'] = r.e800_r_a3.transform(lambda s: s.nlargest(3).mean())
H['e_x_pressure'] = H.e800_r_a3 * H.n_early
PACE = ['g400_r_1', 'g400_r_a3', 'g200_r_1', 'g200_r_a3', 'g600_r_a3', 'g400_best', 'g200_best', 'e800_r_1', 'e800_r_a3',
        'e_rel', 'g_rel', 'n_early', 'early_top3', 'e_x_pressure']
print('pace feature coverage', H[PACE[:9]].notna().mean().round(2).to_dict())
print('corr closing a3 vs early a3', H[['g400_r_a3', 'e800_r_a3']].corr().iloc[0, 1].round(3), ' closing vs speed fig', H[['g400_r_a3', 'savg3']].corr().iloc[0, 1].round(3))

D = F.batch_features(H.drop(columns=['wt', 'E', 'var', 'spd', 'rspeed', 'fig0']), F.categories(H))
D['dow'] = D.date.dt.dayofweek
D['ret'] = np.where(D.win == 1, D.sp, 0.0)
print('rows', len(D), 'speed coverage in test years', D[D.year >= 2022].s1.notna().mean().round(3))


CTX = ['field_size', 'distance', 'going_n', 'weightCarried', 'wt_rel', 'barrier', 'bar_rel', 'nruns', 'days', 'horse_age', 'sex']
RATING = ['w1', 'w2', 'w3', 'wavg3', 'wbest', 'wavg_all', 'wavg3_rel', 'wavg3_mean']
MODELS = {'speed (wt adj) + early/closing': CTX + SPEED + PACE,
          'ratings only (own WPR)': CTX + RATING}
P2 = dict(PARAMS, num_threads=4)


def walk(feats, label):
    out = []
    for ty in range(2022, 2027):
        trn, va, te = D[D.year <= ty - 2], D[D.year == ty - 1], D[D.year == ty].copy()
        raw = 0
        for sd in SEEDS:
            m = lgb.train(dict(P2, seed=sd), lgb.Dataset(trn[feats], trn.win), 2000, valid_sets=[lgb.Dataset(va[feats], va.win)],
                          callbacks=[lgb.early_stopping(80, verbose=False)])
            raw = raw + m.predict(te[feats], raw_score=True) / len(SEEDS)
        e = np.exp(raw - pd.Series(raw, index=te.index).groupby(te.race_id).transform('max').values)
        te['p'] = e / pd.Series(e, index=te.index).groupby(te.race_id).transform('sum').values
        out.append(te)
        print(label, 'done', ty, flush=True)
    T = pd.concat(out)
    T['ev'] = T.p * T.sp
    T['rk'] = T.groupby('race_id').p.rank(ascending=False, method='first')
    return T


def line(name, x):
    if len(x) == 0:
        print(f'  {name:34} n=0'); return
    ex10 = x.drop(x[x.win == 1].nlargest(10, 'sp').index)
    yrs = ' '.join(f"{(x[x.year == y].ret.mean() - 1) * 100:+4.0f}" for y in range(2022, 2027))
    print(f'  {name:34} n={len(x):6} /yr {len(x)/5:5.0f} win {x.win.mean()*100:5.1f}% mkt-implied {x.pm.mean()*100:5.1f}% avg ${x.sp.mean():6.2f} '
          f'ROI {(x.ret.mean()-1)*100:+6.1f}% ex10 {(ex10.ret.mean()-1)*100:+6.1f}% yrs {yrs}')


results = {}
for label, feats in MODELS.items():
    T = walk(feats, label)
    results[label] = T
    ll = -np.log(T.p[T.win == 1]).mean()
    print(f'\n=== {label}: race log-loss {ll:.4f} (market {-np.log(T.pm[T.win == 1]).mean():.4f}, uniform {np.log(T.field_size[T.win == 1]).mean():.4f})')
    top1 = T[T.rk == 1]
    print(f'  model #1 is the market favourite in {(top1.rank_m == 1).mean()*100:.1f}% of races; market favourite wins {T[T.rank_m == 1].win.mean()*100:.1f}%')
    line('model #1', top1)
    line('model #2', T[T.rk == 2])
    line('model #1 and not mkt fav', top1[top1.rank_m > 1])
    line('model top2, mkt rank >= 3', T[(T.rk <= 2) & (T.rank_m >= 3)])
    line('model top3, mkt rank >= 4', T[(T.rk <= 3) & (T.rank_m >= 4)])
    line('model #1, price >= $5', top1[top1.sp >= 5])
    for th in (1.0, 1.1, 1.2, 1.3, 1.5):
        line(f'EV > {th}', T[T.ev > th])
    line('EV > 1.2 and model top 3', T[(T.ev > 1.2) & (T.rk <= 3)])
    line('EV > 1.2, $3-$15', T[(T.ev > 1.2) & T.sp.between(3, 15)])
    line('all runners (reference)', T)

import pickle
pickle.dump({k: v[['race_id', 'horse_id', 'date', 'year', 'p', 'sp', 'pm', 'win', 'rank_m', 'field_size', 'g400_r_a3']] for k, v in results.items()},
            open(os.environ.get('PRED_OUT', 'speed_preds.pkl'), 'wb'))

# closing speed: is the best closer in the field underpriced?
T = results['speed (wt adj) + early/closing']
C = T[T.g400_r_a3.notna()].copy()
C['cq'] = C.groupby('race_id').g400_r_a3.rank(ascending=False, method='min')
print('\nwin rate / market-implied / flat ROI by closing-speed rank within race (as-of average of the last 3 runs)')
for q, g in C.groupby(C.cq.clip(upper=5)):
    line(f'closing rank {int(q)}', g)
a, b = results['speed (wt adj) + early/closing'], results['ratings only (own WPR)']
m = a[['race_id', 'horse_id', 'p', 'ev', 'rk', 'win', 'sp', 'pm', 'year', 'ret']].merge(b[['race_id', 'horse_id', 'p', 'ev', 'rk']], on=['race_id', 'horse_id'], suffixes=('', '_r'))
print('\ncorrelation of speed-model and ratings-model win probability', m[['p', 'p_r']].corr().iloc[0, 1].round(3))
line('speed #1 and ratings #1 agree', m[(m.rk == 1) & (m.rk_r == 1)])
line('speed #1, ratings NOT #1', m[(m.rk == 1) & (m.rk_r != 1)])
line('speed EV>1.2 and ratings EV>1.2', m[(m.ev > 1.2) & (m.ev_r > 1.2)])
line('speed EV>1.2, ratings EV<1', m[(m.ev > 1.2) & (m.ev_r < 1)])
