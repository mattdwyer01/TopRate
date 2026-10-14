"""Selective value rules, projection model vs speed model vs ratings-only model (14 Oct 2026). All market-free, calibrated (isotonic) without any
market blend, compared on the SAME races: complete races from 2025-07 where every runner has a projection (3+ prior rated runs).
Calibration + rule search on 2025-07..12 (calibration cross-fitted by month), rules frozen and judged on 2026-01 onward.
usage: python wpr_value_rules_three_models.py speed_preds.pkl proj_oos.pkl"""
import itertools, sys
import numpy as np, pandas as pd
from sklearn.isotonic import IsotonicRegression

P = pd.read_pickle(sys.argv[1])
PJ = pd.read_pickle(sys.argv[2])[['race_id', 'horse_id', 'proj']]
S, R = P['speed (wt adj) + early/closing'], P['ratings only (own WPR)']
T0 = S.rename(columns={'p': 'p_speed'}).merge(R[['race_id', 'horse_id', 'p']].rename(columns={'p': 'p_ratings'}), on=['race_id', 'horse_id'])
T0 = T0[T0.date >= '2025-07-01'].merge(PJ, on=['race_id', 'horse_id'], how='left')
ok = T0.groupby('race_id').proj.transform(lambda s: s.notna().all())
T0 = T0[ok].copy()
T0['ret'] = np.where(T0.win == 1, T0.sp, 0.0)
T0['ym'] = pd.to_datetime(T0.date).dt.to_period('M').astype(str)
T0['period'] = np.where(T0.date < '2026-01-01', 'dev', 'hold')
print('complete races', T0.race_id.nunique(), 'runners', len(T0), ' dev races', T0[T0.period == 'dev'].race_id.nunique(), ' hold races', T0[T0.period == 'hold'].race_id.nunique())


def norm(df, col):
    return df[col] / df.groupby('race_id')[col].transform('sum')


# projection -> win probability: softmax(beta x proj), beta by max likelihood on the dev period
dev = T0[T0.period == 'dev']
best = None
for b in np.arange(0.05, 0.60, 0.025):
    e = np.exp(b * (dev.proj - dev.groupby('race_id').proj.transform('max')))
    p = e / e.groupby(dev.race_id).transform('sum')
    ll = -np.log(p[dev.win == 1]).mean()
    best = (ll, b) if best is None or ll < best[0] else best
BETA = best[1]
print(f'projection softmax beta {BETA:.3f} (dev log-loss {best[0]:.4f})')
e = np.exp(BETA * (T0.proj - T0.groupby('race_id').proj.transform('max')))
T0['p_proj'] = e / e.groupby(T0.race_id).transform('sum')
g = np.exp(0.5 * (np.log(T0.p_proj) + np.log(T0.p_speed)))
T0['p_projspeed'] = g / g.groupby(T0.race_id).transform('sum')
MODELS = {'projection': 'p_proj', 'speed': 'p_speed', 'ratings': 'p_ratings', 'projection+speed': 'p_projspeed'}


def calibrated(col):
    T = T0.copy()
    T['cp'] = np.nan
    d = T.period == 'dev'
    for m in T.ym[d].unique():                                    # leave-one-month-out within the dev period
        ir = IsotonicRegression(y_min=1e-4, y_max=1, out_of_bounds='clip').fit(T[col][d & (T.ym != m)], T.win[d & (T.ym != m)])
        T.loc[d & (T.ym == m), 'cp'] = ir.predict(T[col][d & (T.ym == m)])
    ir = IsotonicRegression(y_min=1e-4, y_max=1, out_of_bounds='clip').fit(T[col][d], T.win[d])
    T.loc[~d, 'cp'] = ir.predict(T[col][~d])
    T['ev'] = T.cp * T.sp
    gg = T.groupby('race_id')
    T['rk'] = gg.cp.rank(ascending=False, method='first')
    T['topcp'] = gg.cp.transform('max')
    return T


def trim_roi(x):
    return x.drop(x[x.win == 1].nlargest(max(3, len(x) // 150), 'sp').index).ret.mean() - 1


def fmt(x):
    if len(x) == 0:
        return 'n=0'
    return f'n={len(x):5} win {x.win.mean()*100:4.1f}% (mkt-implied {x.pm.mean()*100:4.1f}%) ${x.sp.mean():5.1f} ROI {(x.ret.mean()-1)*100:+6.1f}% trimmed {trim_roi(x)*100:+6.1f}%'


GRID = list(itertools.product((1.1, 1.2, 1.3, 1.5), ((1, 999), (3, 999), (3, 15), (3, 30), (5, 30)), (0, .25, .3, .35, .4), (99, 12, 10), (99, 3, 2), (1, 2, 3)))
for name, col in MODELS.items():
    T = calibrated(col)
    ll = -np.log(T[col][T.win == 1]).mean()
    arr = {c: T[c].values for c in ('ev', 'sp', 'topcp', 'field_size', 'rk', 'rank_m', 'win', 'ret')}
    isdev, ishold = (T.period == 'dev').values, (T.period == 'hold').values
    rows = []
    for evm, (lo, hi), tc, fs, rkm, mrk in GRID:
        m = (arr['ev'] > evm) & (arr['sp'] >= lo) & (arr['sp'] <= hi) & (arr['topcp'] >= tc) & (arr['field_size'] <= fs) & (arr['rk'] <= rkm) & (arr['rank_m'] >= mrk)
        d, h = m & isdev, m & ishold
        if d.sum() < 80 or h.sum() < 40:
            continue
        rows.append(((evm, lo, hi, tc, fs, rkm, mrk), d.sum(), trim_roi(T[d]) * 100, arr['ret'][d].mean() * 100 - 100, h.sum(), arr['ret'][h].mean() * 100 - 100))
    Rr = pd.DataFrame(rows, columns=['rule', 'n_dev', 'trim_dev', 'roi_dev', 'n_hold', 'roi_hold'])
    print(f'\n################ {name}: race log-loss {ll:.4f} over {T.race_id.nunique()} races; {len(Rr)} candidate rules')
    print(f'  average holdout ROI over all candidate rules {Rr.roi_hold.mean():+.1f}%   (random-rule baseline)')
    pos = Rr[Rr.trim_dev > 0]
    print(f'  rules with positive dev ROI after trimming: {len(pos)}' + (f'; holdout ROI > 0 for {(pos.roi_hold > 0).mean()*100:.0f}% of them, mean {pos.roi_hold.mean():+.1f}%' if len(pos) else ''))
    for _, r in Rr.sort_values('trim_dev', ascending=False).head(5).iterrows():
        evm, lo, hi, tc, fs, rkm, mrk = r.rule
        m = (T.ev > evm) & (T.sp >= lo) & (T.sp <= hi) & (T.topcp >= tc) & (T.field_size <= fs) & (T.rk <= rkm) & (T.rank_m >= mrk)
        print(f'  rule (EV>{evm}, ${lo}-{hi}, top p>={tc}, field<={fs}, model rank<={rkm}, market rank>={mrk})')
        print(f'      dev  2025H2: {fmt(T[m & (T.period == "dev")])}')
        print(f'      HOLD 2026  : {fmt(T[m & (T.period == "hold")])}')
