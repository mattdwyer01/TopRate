"""Speed rating rank vs Proj / Nett / L3 rank agreement, dashboard sample (20 Sep to 15 Oct 2026, complete cases, 5+ runners, one winner).
For a runner: its rank on speed (last-3 time-based speed figures, pre-race) and on each of Proj, Nett, L3 within the race. Reports runners, wins, win rate,
market-implied win rate (1/SP), average SP and flat ROI at SP for the agreement cuts.
usage: python research/speed_agreement.py
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


def build():
    d = sf.add_figure(sf.load())
    d['key'] = d.horse.astype(str).str.lower().str.strip()
    d = d.dropna(subset=['sp', 'wpr']).sort_values(['key', 'date'])
    g = d.groupby('key', sort=False)
    h = d[['key', 'date']].copy()
    h['speed3'] = g.sp.transform(lambda s: s.rolling(3, min_periods=2).mean())
    h['l3'] = g.wpr.transform(lambda s: s.rolling(3, min_periods=2).mean())
    h = h.dropna().sort_values('date')
    r = runners_io.read_runners()
    r = r[(r.date >= '2026-09-20') & (r.date <= '2026-10-15') & (r.scratched.fillna(0) == 0)].copy()
    r['date'] = pd.to_datetime(r.date)
    r['key'] = r.horse.astype(str).str.lower().str.strip()
    r = r.drop(columns=['race']).rename(columns={'wpr_nett': 'nett', 'wprp_proj': 'proj', 'race_id': 'race'}).sort_values('date')
    m = pd.merge_asof(r, h, on='date', by='key', allow_exact_matches=False, tolerance=pd.Timedelta(days=400))
    m['won'] = pd.to_numeric(m.won, errors='coerce').fillna(0)
    m['price'] = pd.to_numeric(m.get('starting_price_sp'), errors='coerce')
    m['price'] = m.price.fillna(pd.to_numeric(m.fixed_win_price, errors='coerce'))
    cols = ['speed3', 'nett', 'l3', 'proj']
    ok = m.groupby('race').apply(lambda x: x[cols].notna().all().all() and len(x) >= 5 and x.won.sum() == 1)
    m = m[m.race.isin(ok[ok].index)].reset_index(drop=True)
    for c in cols:
        m['r_' + c] = m.groupby('race')[c].rank(ascending=False, method='first')
    return m


def line(name, x, n_races):
    n = len(x)
    if n == 0:
        return {'cut': name, 'runners': 0}
    pr = x.price.where(x.price > 1)
    roi = ((x.won * pr).sum(skipna=True) - pr.notna().sum()) / pr.notna().sum() if pr.notna().sum() else np.nan
    return {'cut': name, 'runners': n, 'per race': round(n / n_races, 2), 'wins': int(x.won.sum()), 'win%': round(100 * x.won.mean(), 1),
            'implied%': round(100 * (1 / pr).mean(), 1), 'avg SP': round(pr.mean(), 2), 'flat ROI%': round(100 * roi, 1)}


def main():
    m = build()
    nr = m.race.nunique()
    print('races', nr, 'runners', len(m), flush=True)
    oth = ['r_nett', 'r_l3', 'r_proj']
    rows = []
    for k in (1, 2, 3):
        rows.append(line(f'speed rank {k} AND Proj, Nett, L3 all rank {k}', m[(m.r_speed3 == k) & (m[oth] == k).all(axis=1)], nr))
    for k in (1, 2, 3):
        rows.append(line(f'speed top {k} AND Proj, Nett, L3 all top {k}', m[(m.r_speed3 <= k) & (m[oth] <= k).all(axis=1)], nr))
    rows.append(line('Proj, Nett, L3 all top 3 (no speed)', m[(m[oth] <= 3).all(axis=1)], nr))
    rows.append(line('  of those: also speed top 3', m[(m[oth] <= 3).all(axis=1) & (m.r_speed3 <= 3)], nr))
    rows.append(line('  of those: speed NOT top 3', m[(m[oth] <= 3).all(axis=1) & (m.r_speed3 > 3)], nr))
    rows.append(line('speed top 3 AND at least 2 of Proj/Nett/L3 top 3', m[(m.r_speed3 <= 3) & ((m[oth] <= 3).sum(axis=1) >= 2)], nr))
    rows.append(line('Proj #1 only', m[m.r_proj == 1], nr))
    rows.append(line('Proj #1 AND speed top 3', m[(m.r_proj == 1) & (m.r_speed3 <= 3)], nr))
    rows.append(line('Proj #1 AND speed NOT top 3', m[(m.r_proj == 1) & (m.r_speed3 > 3)], nr))
    pd.set_option('display.width', 200)
    pd.set_option('display.max_colwidth', 60)
    print(pd.DataFrame(rows).set_index('cut').to_string())


if __name__ == '__main__':
    main()
