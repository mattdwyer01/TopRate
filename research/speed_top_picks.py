"""How often the top 1/2/3 pre-race speed-rated runners win. Speed rating = mean of the last 3 time-based speed figures (see speed_figure_study.py).
A: all results-file races 2025-07+ where every runner has a speed rating (vs L3 = mean of last 3 wpr, and the random baseline).
B: the dashboard sample (runners.csv, 20 Sep to 15 Oct 2026) with Nett and Proj too, complete cases.
usage: python research/speed_top_picks.py
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


def table(df, cols, label):
    rows = []
    n_races = df.race.nunique()
    base = df.groupby('race').apply(lambda g: pd.Series({k: min(k, len(g)) / len(g) for k in (1, 2, 3)})).mean()
    for c in cols:
        rk = df.groupby('race')[c].rank(ascending=False, method='first')
        w = df[df.won == 1]
        r = rk.loc[w.index]
        rows.append({'rating': c, 'top1 wins': (r == 1).sum() / n_races, 'winner in top2': (r <= 2).sum() / n_races, 'winner in top3': (r <= 3).sum() / n_races})
    rows.append({'rating': 'random', 'top1 wins': base[1], 'winner in top2': base[2], 'winner in top3': base[3]})
    out = pd.DataFrame(rows).set_index('rating')
    print(f'\n{label}: {n_races} races, {len(df)} runners, avg field {len(df) / n_races:.1f}')
    print((out * 100).round(1).astype(str) + '%')


def main():
    d = sf.add_figure(sf.load())
    d['key'] = d.horse.astype(str).str.lower().str.strip()
    d = d.dropna(subset=['sp', 'wpr']).sort_values(['key', 'date'])
    g = d.groupby('key', sort=False)
    d['speed3'] = g.sp.transform(lambda s: s.rolling(3, min_periods=2).mean().shift(1))
    d['l3'] = g.wpr.transform(lambda s: s.rolling(3, min_periods=2).mean().shift(1))
    a = d[(d.date >= '2025-07-01')].copy()
    a['race'] = a.race_id
    a['won'] = (a.positionFinish == 1).astype(int)
    ok = a.groupby('race').apply(lambda x: x.speed3.notna().all() and x.l3.notna().all() and len(x) >= 5 and x.won.sum() == 1)
    a = a[a.race.isin(ok[ok].index)]
    table(a, ['speed3', 'l3'], 'A. results-file races 2025-07+, every runner has speed and L3')
    # B
    h = d[['key', 'date', 'sp', 'wpr']].copy()
    g2 = h.groupby('key', sort=False)
    h['speed3'] = g2.sp.transform(lambda s: s.rolling(3, min_periods=2).mean())
    h['l3'] = g2.wpr.transform(lambda s: s.rolling(3, min_periods=2).mean())
    h = h[['key', 'date', 'speed3', 'l3']].dropna().sort_values('date')
    r = runners_io.read_runners()
    r = r[(r.date >= '2026-09-20') & (r.date <= '2026-10-15') & (r.scratched.fillna(0) == 0)].copy()
    r['date'] = pd.to_datetime(r.date)
    r['key'] = r.horse.astype(str).str.lower().str.strip()
    r = r.drop(columns=['race']).rename(columns={'wpr_nett': 'nett', 'wprp_proj': 'proj', 'race_id': 'race'}).sort_values('date')
    m = pd.merge_asof(r, h, on='date', by='key', allow_exact_matches=False, tolerance=pd.Timedelta(days=400))
    m['won'] = pd.to_numeric(m.won, errors='coerce').fillna(0)
    cols = ['speed3', 'nett', 'l3', 'proj']
    okb = m.groupby('race').apply(lambda x: x[cols].notna().all().all() and len(x) >= 5 and x.won.sum() == 1)
    b = m[m.race.isin(okb[okb].index)].reset_index(drop=True)
    table(b, cols, 'B. dashboard sample 20 Sep to 15 Oct, every runner has all four ratings')


if __name__ == '__main__':
    main()
