"""Overseas-form reliability (2 Nov 2026). Run with: PYTHONPATH=.:projection python research/overseas_form_test.py

Runner pages carry a horse's overseas runs with TopRate's rating, so the live Proj reads them like any other. Question: does the rating formula (the base of
the Proj, on the page ratings as given) predict a horse's NEXT Australian run as well when its recent form is overseas?  Targets: Australian runs from
2025-01-01 with 3+ earlier page runs; miss = actual page rating - formula (formula.json, outlier trim as live).  Grouped by how many of the 4 runs before
were overseas and by where the latest overseas run was (Hong Kong, New Zealand, Britain/Ireland/France/other).  Also lists the 2026 Melbourne Cup field
with its overseas share.  Formula only (no context correction), so it measures the base of the Proj.  Read-only.
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

K = C.K
NZ = ['ellerslie', 'te rapa', 'matamata', 'pukekohe', 'trentham', 'tauranga', 'wanganui', 'otaki', 'riccarton', 'arawa', 'te aroha', 'taupo', 'new plymouth', 'waverley',
      'hastings', 'cambridge', 'ruakaka', 'wingatui', 'tauherenikau', 'ascot park', 'woodville', 'avondale', 'hawera', 'ashburton', 'timaru', 'pharlap', 'awapuni',
      'te awamutu', 'rotorua', 'waipa', 'gore', 'oamaru', 'rangiora', 'hokitika', 'greymouth', 'omakau', 'wyndham', 'waimate', 'phar lap', 'otago', 'awapuni']
HK = ['sha tin', 'happy valley']


def region(t):
    t = str(t).lower()
    if any(h in t for h in HK):
        return 'Hong Kong'
    if any(n in t for n in NZ):
        return 'New Zealand'
    return 'Europe/other'


def main():
    au = set()
    for f in sorted(glob.glob(os.path.join(ROOT, 'race_results_20*.csv.gz'))):
        if f.endswith('_rc.csv.gz'):
            continue
        au |= set(pd.read_csv(f, usecols=['track'], low_memory=False).track.dropna().astype(str).str.lower())
    rp = C.page_frame()
    co = C.coefs()
    rp['f'] = C.formula_pred(rp, co)
    rp['miss'] = rp.wpr - rp.f
    rp['os'] = ~rp.track.astype(str).str.lower().isin(au)
    rp['reg'] = np.where(rp.os, rp.track.map(region), 'Australia')
    g = rp.groupby('horse_id')
    for k in range(1, 5):
        rp[f'os{k}'] = g.os.shift(k).fillna(False).astype(int)
        rp[f'reg{k}'] = g.reg.shift(k)
    rp['os4'] = rp[['os1', 'os2', 'os3', 'os4']].sum(axis=1)
    # region of the most recent overseas run among the last 4
    def last_reg(r):
        for k in range(1, 5):
            if r[f'os{k}'] == 1:
                return r[f'reg{k}']
        return None
    t = rp[(~rp.os) & (rp.date >= '2025-01-01') & (rp.n >= 3) & rp.f.notna() & rp.wpr.notna()].copy()
    print('page runs', len(rp), '| overseas rated runs', int(rp.os.sum()), '| Australian target runs 2025+ with 3+ earlier', len(t))
    pd.set_option('display.width', 220)

    def tab(lab, gp):
        x = gp.miss
        print(f"  {lab:34s} n={len(x):6d} mean {x.mean():+.2f} median {x.median():+.2f} sd {x.std():.2f} MAE {x.abs().mean():.2f}")
    print('\nMiss (actual - formula) by how many of the 4 earlier runs were overseas:')
    for lab, m in (('0 overseas', t.os4 == 0), ('1 overseas', t.os4 == 1), ('2 overseas', t.os4 == 2), ('3-4 overseas', t.os4 >= 3)):
        tab(lab, t[m])
    print('\nLatest run was overseas (first Australian run back):')
    tab('previous run overseas', t[t.os1 == 1])
    tab('previous run Australian', t[t.os1 == 0])
    print('\nBy region of the latest overseas run in the last 4 (2+ overseas runs):')
    s = t[t.os4 >= 2].copy()
    s['lr'] = s.apply(last_reg, axis=1)
    for r_ in ('Hong Kong', 'New Zealand', 'Europe/other'):
        tab(r_, s[s.lr == r_])
    print('\nRating level of the overseas runs themselves vs the horse\'s Australian level (same horses, runs in 2025+):')
    both = rp[(rp.date >= '2025-01-01') & rp.horse_id.isin(rp[rp.os].horse_id.unique())]
    lv = both.groupby(['horse_id', 'reg']).wpr.mean().unstack()
    for r_ in ('Hong Kong', 'New Zealand', 'Europe/other'):
        if r_ in lv and 'Australia' in lv:
            x = (lv[r_] - lv['Australia']).dropna()
            print(f"  {r_:14s} horses with both: {len(x):4d}  mean (overseas run rating - Australian run rating) {x.mean():+.2f}  median {x.median():+.2f}")

    # 2026 Melbourne Cup field
    r = pd.read_csv(os.path.join(ROOT, 'runners.csv'), usecols=['date', 'venue', 'race', 'horse', 'horse_id', 'scratched', 'barrier'], low_memory=False)
    cup = r[(r.date == '2026-11-03') & (r.venue == 'Flemington') & (r.race == 7) & (r.scratched.fillna(0) != 1) & (r.barrier > 0)]
    print('\n2026 Melbourne Cup field: last 8 page runs (newest first)')
    rows = []
    for h, nm in zip(cup.horse_id, cup.horse):
        x = rp[rp.horse_id == h].sort_values('date').tail(8)
        regs = list(x.reg.iloc[::-1])
        rows.append((nm, len(x), int((x.reg != 'Australia').sum()), ' '.join(a[:2] if a != 'Europe/other' else 'EU' for a in regs)))
    for nm, n, no, s_ in sorted(rows, key=lambda z: -z[2]):
        print(f'  {nm:20s} runs {n}  overseas {no}   {s_}')


if __name__ == '__main__':
    main()
