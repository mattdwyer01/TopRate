"""Does a time-based, track-variant-corrected, weight-adjusted speed figure add anything to the bet model? (read-only analysis, 14 Oct 2026)
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
F.USECOLS = F.USECOLS + ['winners_time']

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
SPEED = ['s1', 's2', 's3', 'savg3', 'sbest', 'sraw1', 'savg3_rel', 'savg3_mean']
print('corr(savg3, wpr avg of same 3 runs) as of', pd.concat([H.savg3, pd.concat([h.wpr.shift(k) for k in (1, 2, 3)], axis=1).mean(axis=1)], axis=1).corr().iloc[0, 1].round(3))

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


A = walk(F.FEATURES, 'baseline')
B = walk(F.FEATURES + SPEED, 'with speed')
mk = A.win == 1
print('\nper-year log-loss gain (baseline - speed):', {int(y): round(float(-np.log(A.pmod[mk & (A.year == y)]).mean() + np.log(B.pmod[(B.win == 1) & (B.year == y)]).mean()), 4) for y in range(2022, 2027)})
