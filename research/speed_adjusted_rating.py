"""Fold days since run, weight change and distance change into the speed rating (19 Oct 2026, owner's pick from speed_extras_study.py).
Fit (before 2025): target = the run's wpr minus the race mean, predictors demeaned in race: rating R (EWM halflife 4 of par v2 figures, lengths), log1p(days since last run),
weight change vs the last run (kg), distance change (m). Adjustment in LENGTHS = (c_days*ldays + c_w*wchg + c_dist*dchg) / c_R, written to speed_models/adjust.json.
Scored on 2025-07+ complete-case races: winner log-lik, top pick, gain over L3 (weight fitted 2025-07..12, scored 2026), shipped vs adjusted, plus each term alone.
usage: PYTHONPATH=. python research/speed_adjusted_rating.py"""
import json, os, sys
import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(__file__))
import speed_extras_study as ex
import speed_figure_study as sf
import speed_figure_study2 as s2

SEC = sf.SEC


def main():
    d = sf.load()
    r = s2.races_table(d)
    r['par'] = s2.fit_par(r)
    dev = r.winners_time - r.par
    r['fast'] = -(dev - ex.variant(r, dev)) / SEC
    d = d.merge(r[['race_id', 'fast']], on='race_id', how='left')
    d['sp'] = d.fast - d.marginFinish.clip(lower=0, upper=25)
    d = d.dropna(subset=['sp']).sort_values(['horse_id', 'date']).reset_index(drop=True)
    gg = d.groupby('horse_id', sort=False)
    d['R'] = gg['sp'].transform(lambda s: s.shift(1).ewm(halflife=4.0, min_periods=2).mean())
    d['L3'] = gg['wpr'].transform(lambda s: s.shift(1).rolling(3, min_periods=2).mean())
    d['days'] = (d.date - gg['date'].shift(1)).dt.days
    d['ldays'] = np.log1p(d.days.clip(upper=400))
    d['wchg'] = d.weightCarried - gg['weightCarried'].shift(1)
    d['dchg'] = d.distance - gg['distance'].shift(1)
    d['T'] = d.wpr - d.groupby('race_id').wpr.transform('mean')
    n = d.groupby('race_id').race_id.transform('size')
    use = d[(n >= 5) & d['T'].notna() & d.R.notna() & d.ldays.notna() & d.wchg.notna() & d.dchg.notna()].copy()
    for c in ('R', 'ldays', 'wchg', 'dchg'):
        use[c + '_d'] = use[c] - use.groupby('race_id')[c].transform('mean')
    tr = use[use.date < '2025-01-01']
    f = ['R_d', 'ldays_d', 'wchg_d', 'dchg_d']
    b = ex.ols(tr[f].values, tr['T'].values)
    cR, cd, cw, cx = b[1], b[2], b[3], b[4]
    print('coefficients (rating points): rating %.3f per length, ldays %.3f, weight %.3f per kg, distance %.5f per m' % (cR, cd, cw, cx))
    coef = {'per_length': float(cR), 'ldays': float(cd), 'wchg': float(cw), 'dchg': float(cx),
            'adj_lengths': {'ldays': float(cd / cR), 'wchg': float(cw / cR), 'dchg': float(cx / cR)}}
    print('adjustment in lengths: %.3f per log-day, %.4f per kg, %.6f per m' % (cd / cR, cw / cR, cx / cR))
    json.dump(coef, open('speed_models/adjust.json', 'w'), indent=1)
    # the adjustment is relative to the race, so use the raw (not demeaned) terms; the race mean shifts every runner alike and drops out of ranking
    ok = d.R.notna() & d.ldays.notna() & d.wchg.notna() & d.dchg.notna()
    d['R adj all'] = np.where(ok, d.R + (cd * d.ldays + cw * d.wchg + cx * d.dchg) / cR, np.nan)
    d['R adj days'] = np.where(ok, d.R + cd * d.ldays / cR, np.nan)
    d['R adj weight'] = np.where(ok, d.R + cw * d.wchg / cR, np.nan)
    d['R adj distance'] = np.where(ok, d.R + cx * d.dchg / cR, np.nan)
    d['R A shipped'] = np.where(ok, d.R, np.nan)
    rcols = ['R A shipped', 'R adj days', 'R adj weight', 'R adj distance', 'R adj all']
    t = d[d.date >= '2025-07-01'].copy()
    t['won'] = (t.positionFinish == 1).astype(int)
    okr = t.groupby('race_id').apply(lambda x: x[rcols + ['L3']].notna().all().all() and len(x) >= 5 and x.won.sum() == 1)
    t = t[t.race_id.isin(okr[okr].index)]
    print('\ncomplete-case races', t.race_id.nunique())
    ex.evaluate(t, rcols, rcols[0])


if __name__ == '__main__':
    main()
