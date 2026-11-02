"""Melbourne Cup backtest (2 Nov 2026). Run with: PYTHONPATH=.:projection python research/cup_backtest.py

For each past Melbourne Cup in the results files (Flemington, 3200m, first Tuesday of November), score every runner as the live Proj's FORMULA part
would have before the race: the horse's last 8 earlier rated runs (results-file wpr, plain scale) put on the ATW scale of the Cup weight
(wfa_scale.atw_offset, AR 168, constant per horse) and fed through projection/models_tr/formula.json. Read-only: no model is fitted and nothing is written.
It is the formula only (no context correction, no overseas runs: the results files hold Australian races), so it shows how the base of the Proj behaves in a
Cup, not the full live Proj.

Reports: where the winner and placegetters ranked (formula, last-3 average, starting price); how many runners the formula could not rate (under 1 earlier
rated run); and whether the Cup's run-level miss (actual minus predicted, ATW scale) differs from other staying races.
"""
import glob
import os
import sys

import numpy as np
import pandas as pd

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
sys.path.insert(0, ROOT)
sys.path.insert(0, os.path.join(ROOT, 'projection'))
os.environ.setdefault('PROJECTION_RATINGS', 'toprate')
import ctx as C  # noqa: E402
import wfa_scale  # noqa: E402
import features as F  # noqa: E402

K = C.K
COLS = ['race_id', 'date', 'track', 'distance', 'wpr', 'weightCarried', 'positionFinish', 'priceStarting', 'horse_id', 'horse', 'horse_age', 'horse_sex',
        'isBarrierTrial', 'race_class', 'field_size', 'horse_country']


def load():
    fs = [f for f in sorted(glob.glob(os.path.join(ROOT, 'race_results_20*.csv.gz'))) if not f.endswith('_rc.csv.gz')]
    d = pd.concat([pd.read_csv(f, usecols=lambda c: c in COLS, low_memory=False) for f in fs], ignore_index=True)
    d['date'] = pd.to_datetime(d.date)
    d = d[d.isBarrierTrial.fillna(0) != 1]
    d = d[~F.is_jumps(d.race_class)]
    for c in ('wpr', 'weightCarried', 'positionFinish', 'priceStarting', 'distance', 'horse_age', 'field_size'):
        d[c] = pd.to_numeric(d[c], errors='coerce')
    d = d.dropna(subset=['horse_id', 'date']).drop_duplicates(['horse_id', 'date'], keep='last')
    return d.sort_values(['horse_id', 'date']).reset_index(drop=True)


def add_lags(d):
    """r1..r8: the horse's previous rated runs (plain wpr), newest first, strictly before the row's date; n = how many exist (capped at K)."""
    rated = d.wpr.notna().values
    g = d.horse_id.values
    cum = pd.Series(rated.astype(int)).groupby(g).cumsum().values       # rated runs up to and including the row
    prior = cum - rated                                                   # rated runs strictly before it
    idx = pd.Series(np.arange(len(d)))
    starts = pd.Series(idx.values).groupby(g).transform('min').values     # first row of the horse
    # row of the j-th rated run of each horse: build per horse from rated rows
    rr = np.flatnonzero(rated)
    ord_in_h = (cum[rr] - 1)
    key = {}
    for i, (h, o) in zip(rr, zip(g[rr], ord_in_h)):
        key[(h, o)] = d.wpr.values[i]
    W = np.full((len(d), K), np.nan)
    for k in range(1, K + 1):
        j = prior - k
        ok = j >= 0
        W[ok, k - 1] = [key.get((h, o), np.nan) for h, o in zip(g[ok], j[ok])]
    for k in range(K):
        d[f'r{k + 1}'] = W[:, k]
    d['n'] = np.minimum(prior, K)
    return d


def offset(row):
    try:
        return wfa_scale.atw_offset(int(row.horse_age), row.horse_sex, row.date.date().isoformat() if hasattr(row.date, 'date') else row.date, row.distance, row.weightCarried)
    except Exception:
        return None


def score(t, co):
    t = t.copy()
    off = [offset(r) for r in t.itertuples()]
    t['off'] = pd.to_numeric(pd.Series(off, index=t.index), errors='coerce')
    for k in range(1, K + 1):
        t[f'r{k}'] = t[f'r{k}'] + t.off
    t = t[t.off.notna()].copy()
    t['pred'] = C.formula_pred(t, co)
    t['l3'] = t[['r1', 'r2', 'r3']].mean(axis=1)
    t['act'] = t.wpr + t.off
    t['err'] = t.act - t.pred
    return t


def main():
    co = C.coefs()
    d = add_lags(load())
    print('results-file runs', len(d))
    cups = d[(d.track.astype(str).str.contains('Flemington')) & (d.distance == 3200) & (d.date.dt.month == 11) & (d.date.dt.weekday == 1) & (d.field_size >= 15)]
    cups = cups[cups.positionFinish.notna()]
    cs = score(cups, co)
    print('\nMelbourne Cups found:', sorted(cs.date.dt.strftime('%Y-%m-%d').unique()))
    rows = []
    for dt, g in cs.groupby('date'):
        g = g.copy()
        g['rk_f'] = g.pred.rank(ascending=False, method='min')
        g['rk_l3'] = g.l3.rank(ascending=False, method='min')
        g['rk_sp'] = g.priceStarting.rank(ascending=True, method='min')
        win = g[g.positionFinish == 1].iloc[0]
        top4 = g[g.positionFinish <= 4]
        rows.append(dict(date=dt.date(), field=len(g), unrated=int(g.pred.isna().sum()), winner=win.horse, w_n=int(win.n), w_ctry=win.horse_country,
                         w_rk_formula=win.rk_f, w_rk_l3=win.rk_l3, w_rk_sp=win.rk_sp, top4_mean_rk_formula=top4.rk_f.mean(), top4_mean_rk_l3=top4.rk_l3.mean(),
                         top4_mean_rk_sp=top4.rk_sp.mean(),
                         spearman_formula=g[['pred', 'positionFinish']].corr(method='spearman').iloc[0, 1] * -1,
                         spearman_sp=g[['priceStarting', 'positionFinish']].corr(method='spearman').iloc[0, 1],
                         mean_err=g.err.mean(), sd_err=g.err.std()))
    R = pd.DataFrame(rows)
    pd.set_option('display.width', 250)
    pd.set_option('display.max_columns', 30)
    print(R.round(2).to_string(index=False))
    print('\nPooled over Cups: winner rank formula %.1f  last3 %.1f  starting price %.1f ; top-4 mean rank formula %.1f last3 %.1f price %.1f ; runners with no rating %d of %d'
          % (R.w_rk_formula.mean(), R.w_rk_l3.mean(), R.w_rk_sp.mean(), R.top4_mean_rk_formula.mean(), R.top4_mean_rk_l3.mean(), R.top4_mean_rk_sp.mean(), R.unrated.sum(), R.field.sum()))
    print('Winners with under 3 earlier results-file runs:', int((R.w_n < 3).sum()), 'of', len(R), '| winners by horse_country:', R.w_ctry.value_counts().to_dict())
    print('Cup spearman (rating vs finish): formula %.2f   starting price %.2f' % (R.spearman_formula.mean(), R.spearman_sp.mean()))
    # Level miss: Cup vs other staying races, same method
    base = d[(d.date >= '2017-01-01') & d.wpr.notna() & (d.field_size >= 10)]
    sub = {'Melbourne Cups': cs[cs.wpr.notna() & (cs.n >= 3)]}
    stay = base[(base.distance >= 2800) & ~base.index.isin(cups.index)]
    mid = base[(base.distance >= 2000) & (base.distance < 2800)].pipe(lambda z: z.sample(min(60000, len(z)), random_state=1))
    sub['other 2800m+ races'] = score(stay[stay.n >= 3], co)
    sub['2000-2800m races (60k sample)'] = score(mid[mid.n >= 3], co)
    print('\nActual - predicted (ATW scale), runners with 3+ earlier rated runs:')
    for k, x in sub.items():
        x = x[x.n >= 3]
        print(f"  {k:32s} n={len(x):6d} mean {x.err.mean():+.2f} median {x.err.median():+.2f} sd {x.err.std():.2f}  MAE {x.err.abs().mean():.2f}")
    hi = cs[cs.n >= 3]
    for lo, hi_ in ((0, 95), (95, 200)):
        x = hi[(hi.pred >= lo) & (hi.pred < hi_)]
        print(f'  Cups, predicted {lo}-{hi_}: n={len(x)} mean {x.err.mean():+.2f} median {x.err.median():+.2f}')
    # by the horse's own situation in the Cup: weight
    cs['wt_band'] = pd.cut(cs.weightCarried, [0, 53, 55.5, 99])
    print('\nCup runners by carried weight: mean err / n'); print(cs[cs.n >= 3].groupby('wt_band', observed=True).err.agg(['mean', 'median', 'count']).round(2))


if __name__ == '__main__':
    main()
