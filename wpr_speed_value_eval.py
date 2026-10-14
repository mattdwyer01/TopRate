"""Selective value test for the standalone speed model (14 Oct 2026). Reads the walk-forward predictions saved by wpr_speed_standalone_test.py
(PRED_OUT pickle). The speed model and a ratings-only model are market-free, so they are used as independent opinions: for each test year the
blend  score = c*log(market) + a_r*log(ratings p) + a_s*log(speed p)  is fitted on EARLIER test years only (grid search on race log-loss),
then bets are selected on the blended EV = p x SP, with price and "readable race" filters. Test years 2023 to 2026 (2022 has no earlier year).
usage: python wpr_speed_value_eval.py preds.pkl"""
import sys
import numpy as np, pandas as pd

P = pd.read_pickle(sys.argv[1])
S, R = P['speed (wt adj) + early/closing'], P['ratings only (own WPR)']
D = S.rename(columns={'p': 'ps'}).merge(R[['race_id', 'horse_id', 'p']].rename(columns={'p': 'pr'}), on=['race_id', 'horse_id'])
D = D.sort_values(['race_id', 'horse_id']).reset_index(drop=True)
D['ret'] = np.where(D.win == 1, D.sp, 0.0)
codes, uniq = pd.factorize(D.race_id)
starts = np.r_[0, np.flatnonzero(np.diff(codes)) + 1]
cnt = np.diff(np.r_[starts, len(D)])
lpm, lpr, lps = (np.log(D[c].clip(lower=1e-6)).values for c in ('pm', 'pr', 'ps'))
win = D.win.values == 1
yr = D.year.values


def softmax(score):
    mx = np.repeat(np.maximum.reduceat(score, starts), cnt)
    e = np.exp(score - mx)
    return e / np.repeat(np.add.reduceat(e, starts), cnt)


def fit(mask, use_r, use_s):
    best = (9, None)
    for c in np.arange(0.5, 1.31, 0.1):
        for ar in (np.arange(0, 0.81, 0.1) if use_r else [0]):
            for as_ in (np.arange(0, 0.81, 0.1) if use_s else [0]):
                p = softmax(c * lpm + ar * lpr + as_ * lps)
                ll = -np.log(p[win & mask]).mean()
                if ll < best[0]:
                    best = (ll, (c, ar, as_))
    return best[1]


def line(name, x):
    if len(x) == 0:
        print(f'  {name:40} n=0'); return
    ex10 = x.drop(x[x.win == 1].nlargest(10, 'sp').index)
    yrs = ' '.join(f"{(x[x.year == y].ret.mean() - 1) * 100:+4.0f}" for y in range(2023, 2027))
    print(f'  {name:40} n={len(x):6} /yr {len(x)/4:5.0f} win {x.win.mean()*100:5.1f}% (mkt {x.pm.mean()*100:5.1f}%, blend {x.pb.mean()*100:5.1f}%) avg ${x.sp.mean():6.2f} '
          f'ROI {(x.ret.mean()-1)*100:+6.1f}% ex10 {(ex10.ret.mean()-1)*100:+6.1f}% yrs {yrs}')


VARIANTS = {'market + ratings': (True, False), 'market + speed': (False, True), 'market + ratings + speed': (True, True)}
for name, (ur, us) in VARIANTS.items():
    D['pb'] = np.nan
    ws = {}
    for ty in range(2023, 2027):
        w = fit(yr < ty, ur, us)
        ws[ty] = tuple(round(float(v), 2) for v in w)
        p = softmax(w[0] * lpm + w[1] * lpr + w[2] * lps)
        D.loc[yr == ty, 'pb'] = p[yr == ty]
    T = D[D.year >= 2023].copy()
    T['ev'] = T.pb * T.sp
    T['rkb'] = T.groupby('race_id').pb.rank(ascending=False, method='first')
    T['topb'] = T.groupby('race_id').pb.transform('max')
    ll = -np.log(T.pb[T.win == 1]).mean()
    print(f'\n=== {name}: weights (market c, ratings, speed) by test year {ws}')
    print(f'    race log-loss {ll:.4f} vs market {-np.log(T.pm[T.win == 1]).mean():.4f}')
    for th in (1.05, 1.10, 1.20, 1.30):
        line(f'EV > {th}', T[T.ev > th])
    for th in (1.10, 1.20):
        line(f'EV > {th}, $3+', T[(T.ev > th) & (T.sp >= 3)])
        line(f'EV > {th}, $3-$15', T[(T.ev > th) & T.sp.between(3, 15)])
        line(f'EV > {th}, readable race (top p>=.30)', T[(T.ev > th) & (T.topb >= .30)])
        line(f'EV > {th}, readable, $3-$15', T[(T.ev > th) & (T.topb >= .30) & T.sp.between(3, 15)])
        line(f'EV > {th}, blend top-2 only', T[(T.ev > th) & (T.rkb <= 2)])
        line(f'EV > {th}, field <= 10', T[(T.ev > th) & (T.field_size <= 10)])
    if name == 'market + ratings':
        base = T[['race_id', 'horse_id', 'ev']].rename(columns={'ev': 'ev_r'})
    elif name == 'market + ratings + speed':
        m = T.merge(base, on=['race_id', 'horse_id'])
        print('  -- bets that exist only because of speed (ev with speed > thr while market+ratings ev < 1.0):')
        for th in (1.10, 1.20):
            line(f'speed-only EV > {th}', m[(m.ev > th) & (m.ev_r < 1.0)])
            line(f'both EV > {th}', m[(m.ev > th) & (m.ev_r > th)])
