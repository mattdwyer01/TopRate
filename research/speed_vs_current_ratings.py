"""Correlation of a speed rating (mean of a horse's last 3 time-based speed figures, lengths vs par) with Nett, L3 and Proj on the dashboard's recent races.
Runners: runners.csv, 20 Sep to 15 Oct 2026, not scratched, with Nett and Proj. L3 = mean of the last 3 rated results-file wpr before the race date.
Reports pooled Pearson, within-race (demeaned) Pearson and the mean per-race Spearman rank correlation.
usage: python research/speed_vs_current_ratings.py
"""
import os
import sys

import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(__file__))
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import speed_figure_study as sf  # noqa: E402
import runners_io  # noqa: E402

sf.USE = sf.USE + ['horse']


def main():
    d = sf.add_figure(sf.load())
    d['key'] = d.horse.astype(str).str.lower().str.strip()
    d = d.dropna(subset=['sp']).sort_values(['key', 'date'])
    g = d.groupby('key', sort=False)
    d['speed3'] = g.sp.transform(lambda s: s.rolling(3, min_periods=2).mean())
    d['l3'] = g.wpr.transform(lambda s: s.rolling(3, min_periods=2).mean())
    h = d[['key', 'date', 'speed3', 'l3']].dropna(subset=['speed3']).sort_values('date')
    r = runners_io.read_runners()
    r = r[(r.date >= '2026-09-20') & (r.date <= '2026-10-15') & (r.scratched.fillna(0) == 0)].copy()
    r['date'] = pd.to_datetime(r.date)
    r['key'] = r.horse.astype(str).str.lower().str.strip()
    r = r.rename(columns={'wpr_nett': 'nett', 'wprp_proj': 'proj'})
    r = r.dropna(subset=['nett', 'proj']).sort_values('date')
    m = pd.merge_asof(r, h, on='date', by='key', allow_exact_matches=False, tolerance=pd.Timedelta(days=400))
    m = m.dropna(subset=['speed3', 'l3'])
    m['rid'] = m.race_id
    n = m.groupby('rid').rid.transform('size')
    m = m[n >= 4].copy()
    print('runners', len(m), 'races', m.rid.nunique(), flush=True)
    cols = ['speed3', 'nett', 'l3', 'proj']
    for c in cols:
        m[c + '_dm'] = m[c] - m.groupby('rid')[c].transform('mean')
    pooled = m[cols].corr()
    within = m[[c + '_dm' for c in cols]].corr()
    within.index = within.columns = cols
    rk = []
    for _, gg in m.groupby('rid'):
        if gg[cols].nunique().min() < 3:
            continue
        rk.append(gg[cols].corr(method='spearman').values)
    rank = pd.DataFrame(np.nanmean(rk, axis=0), index=cols, columns=cols)
    pd.set_option('display.width', 120)
    print('\nPooled Pearson (all runners)\n', pooled.round(3))
    print('\nWithin-race Pearson (race mean removed)\n', within.round(3))
    print('\nMean per-race Spearman rank correlation (%d races)\n' % len(rk), rank.round(3))


if __name__ == '__main__':
    main()
