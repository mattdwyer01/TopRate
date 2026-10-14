"""Find selective value rules for the standalone speed model (and, for comparison, the ratings-only model), 14 Oct 2026.
Each market-free model's win probability is calibrated on EARLIER test years only (isotonic, no market blend). Rules (EV threshold, price band,
how clear the race is, field size, model rank, market rank) are searched on the dev years 2023-2024 and judged on 2025-2026, which the search never saw.
usage: python wpr_speed_rules_search.py preds.pkl"""
import itertools, sys
import numpy as np, pandas as pd
from sklearn.isotonic import IsotonicRegression

P = pd.read_pickle(sys.argv[1])
NAMES = {'speed': 'speed (wt adj) + early/closing', 'ratings': 'ratings only (own WPR)'}
DEV, HOLD = (2023, 2024), (2025, 2026)


def prep(key):
    T = P[NAMES[key]].copy()
    T['ret'] = np.where(T.win == 1, T.sp, 0.0)
    T['cp'] = np.nan
    for ty in range(2023, 2027):
        ir = IsotonicRegression(y_min=1e-4, y_max=1, out_of_bounds='clip').fit(T.p[T.year < ty], T.win[T.year < ty])
        T.loc[T.year == ty, 'cp'] = ir.predict(T.p[T.year == ty])
    T = T[T.year >= 2023].copy()
    T['ev'] = T.cp * T.sp
    g = T.groupby('race_id')
    T['rk'] = g.cp.rank(ascending=False, method='first')
    T['topcp'] = g.cp.transform('max')
    return T


def stats(x, yrs):
    x = x[x.year.isin(yrs)]
    if len(x) == 0:
        return None
    ex10 = x.drop(x[x.win == 1].nlargest(max(3, len(x) // 150), 'sp').index)      # drop the biggest ~0.7% of winners
    return len(x), (x.ret.mean() - 1) * 100, (ex10.ret.mean() - 1) * 100


def fmt(x, yrs):
    s = stats(x, yrs)
    if s is None:
        return 'n=0'
    byy = ' '.join(f"{(x[x.year == y].ret.mean() - 1) * 100:+4.0f}" for y in yrs)
    return f'n={s[0]:5} /yr {s[0]/len(yrs):4.0f} win {x[x.year.isin(yrs)].win.mean()*100:4.1f}% ${x[x.year.isin(yrs)].sp.mean():5.1f} ROI {s[1]:+6.1f}% trim {s[2]:+6.1f}% yrs {byy}'


GRID = list(itertools.product((1.1, 1.2, 1.3, 1.5), ((1, 999), (3, 999), (3, 15), (3, 30), (5, 30)), (0, .25, .3, .35), (99, 12, 10), (99, 3, 2), (1, 2, 3)))
for key in ('speed', 'ratings'):
    T = prep(key)
    ll = -np.log(T.p[T.win == 1]).mean()
    arr = {c: T[c].values for c in ('ev', 'sp', 'topcp', 'field_size', 'rk', 'rank_m', 'year', 'win', 'ret')}
    rows = []
    for evm, (lo, hi), tc, fs, rkm, mrk in GRID:
        m = (arr['ev'] > evm) & (arr['sp'] >= lo) & (arr['sp'] <= hi) & (arr['topcp'] >= tc) & (arr['field_size'] <= fs) & (arr['rk'] <= rkm) & (arr['rank_m'] >= mrk)
        d = m & np.isin(arr['year'], DEV)
        h = m & np.isin(arr['year'], HOLD)
        if d.sum() < 150 or h.sum() < 60:
            continue
        rd, rh = arr['ret'][d].mean() - 1, arr['ret'][h].mean() - 1
        # dev score: ROI after trimming the biggest ~0.7% of winners, so one longshot cannot make a rule
        xs = T[d]
        trim = xs.drop(xs[xs.win == 1].nlargest(max(3, len(xs) // 150), 'sp').index).ret.mean() - 1
        rows.append(((evm, lo, hi, tc, fs, rkm, mrk), d.sum(), rd * 100, trim * 100, h.sum(), rh * 100))
    R = pd.DataFrame(rows, columns=['rule', 'n_dev', 'roi_dev', 'trim_dev', 'n_hold', 'roi_hold'])
    print(f'\n################ {key} model: race log-loss {ll:.4f} (2023-26); {len(R)} candidate rules with enough bets')
    print(f'all candidate rules: mean holdout ROI {R.roi_hold.mean():+.1f}% (this is the baseline for a rule chosen at random)')
    ok = R[(R.trim_dev > 0)]
    print(f'rules with dev trimmed ROI > 0: {len(ok)}; of those, holdout ROI > 0 for {(ok.roi_hold > 0).mean()*100:.0f}%, mean holdout ROI {ok.roi_hold.mean():+.1f}%')
    best = R.sort_values('trim_dev', ascending=False).head(8)
    print('top 8 rules by dev trimmed ROI -> frozen, then judged on 2025-26:  (EV>, price lo-hi, top calibrated p >=, field <=, model rank <=, market rank >=)')
    for _, r in best.iterrows():
        evm, lo, hi, tc, fs, rkm, mrk = r.rule
        m = (T.ev > evm) & (T.sp >= lo) & (T.sp <= hi) & (T.topcp >= tc) & (T.field_size <= fs) & (T.rk <= rkm) & (T.rank_m >= mrk)
        print(f'  rule {r.rule}')
        print(f'     dev  2023-24: {fmt(T[m], DEV)}')
        print(f'     HOLD 2025-26: {fmt(T[m], HOLD)}')
