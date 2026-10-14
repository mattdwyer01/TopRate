"""PART 2 (early speed and closing speed / turn of foot added on top of the speed figure). Part 1 docstring follows.
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


def walk(feats, label):
    out = []
    for ty in range(2022, 2027):
        trn, va, te = D[D.year <= ty - 2], D[D.year == ty - 1], D[D.year == ty].copy()
        raw = 0
        for sd in SEEDS:
            m = lgb.train(dict(PARAMS, seed=sd, num_threads=4), lgb.Dataset(trn[feats], trn.win, init_score=logit(trn.pm)), 2000,
                          valid_sets=[lgb.Dataset(va[feats], va.win, init_score=logit(va.pm))], callbacks=[lgb.early_stopping(80, verbose=False)])
            raw = raw + m.predict(te[feats], raw_score=True) / len(SEEDS)
        s = raw + logit(te.pm).values
        e = np.exp(s - pd.Series(s, index=te.index).groupby(te.race_id).transform('max').values)
        te['pmod'] = e / pd.Series(e, index=te.index).groupby(te.race_id).transform('sum').values
        te['ev'] = te.pmod * te.sp
        te['tier'] = [tier(a, b, c) for a, b, c in zip(te.ev, te.sp, te.rank_m)]
        out.append(te)
        print(label, 'done', ty, flush=True)
    T = pd.concat(out)
    ll = -np.log(T.pmod[T.win == 1]).mean()
    print(f'\n== {label}: log-loss model {ll:.4f} market {-np.log(T.pm[T.win == 1]).mean():.4f}')
    for name, msk in (('Select', T.tier == 'S'), ('Volume incl S', T.tier != ''), ('Volume only', T.tier == 'V')):
        x = T[msk]
        ex10 = x.drop(x[x.win == 1].nlargest(10, 'sp').index)
        print(f'{name:14} n={len(x):6} /yr {len(x)/5:5.0f} win {x.win.mean()*100:4.1f}% ${x.sp.mean():5.2f} ROI {(x.ret.mean()-1)*100:+6.1f}% ex10 {(ex10.ret.mean()-1)*100:+5.1f}% '
              'yrs ' + ' '.join(f"{(x[x.year==y].ret.mean()-1)*100:+4.0f}" for y in range(2022, 2027)))
    return T


R0 = walk(F.FEATURES + SPEED_RAW, 'speed NOT weight adjusted')
A = walk(F.FEATURES + SPEED, 'speed weight adjusted')
B = walk(F.FEATURES + SPEED + PACE, 'speed + early/closing')
mk = A.win == 1
print('\nlog-loss: raw', round(float(-np.log(R0.pmod[R0.win == 1]).mean()), 4), ' adjusted', round(float(-np.log(A.pmod[mk]).mean()), 4))
print('\nper-year log-loss gain (speed - speed+pace):', {int(y): round(float(-np.log(A.pmod[mk & (A.year == y)]).mean() + np.log(B.pmod[(B.win == 1) & (B.year == y)]).mean()), 4) for y in range(2022, 2027)})
# does closing speed matter: runner level win rate vs market by closing rank
T = B[B.g400_r_a3.notna()].copy()
T['cq'] = T.groupby('race_id').g400_r_a3.rank(ascending=False, method='min')
print('\nwin rate / market-implied / flat ROI by closing-speed rank within race (as-of avg of last 3)')
for q, g in T.groupby(T.cq.clip(upper=5)):
    print(f'rank {int(q)}: n={len(g)} win {g.win.mean()*100:.1f}% market {g.pm.mean()*100:.1f}% ROI {(g.ret.mean()-1)*100:+.1f}%')
