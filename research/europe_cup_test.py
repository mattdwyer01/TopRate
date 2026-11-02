"""European-form horses (2 Nov 2026). Run with: PYTHONPATH=.:projection python research/europe_cup_test.py

How does the rating formula (base of the Proj, page ratings as given) do on horses that arrive from Europe?  A run is overseas when its track is not an Australian
track name OR its going has no numeric grade (Australian and New Zealand going reads 'Good 4'; Britain/Ireland/France/Hong Kong read 'Good To Firm', 'Yielding',
'Standard'...), which also catches UK courses that share a name with an Australian one (Ascot, Newmarket, Goodwood).  Regions: Hong Kong, New Zealand (track list),
Europe/other (the rest).  Targets: Australian runs from 2024-07-01 with 3+ earlier page runs and 2+ Europe/other runs among the last 8.  Miss = actual - formula.
Groups: Australian runs since the last Europe/other run (0 = first start in Australia, 1, 2, 3+), and 2400m+ vs shorter.  Then the 2026 Cup field's histories.
Read-only; formula only (no context correction).
"""
import glob
import os
import re
import sys

import numpy as np
import pandas as pd

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
sys.path.insert(0, ROOT)
sys.path.insert(0, os.path.join(ROOT, 'projection'))
os.environ.setdefault('PROJECTION_RATINGS', 'toprate')
import ctx as C  # noqa: E402

K = C.K
HK = ['sha tin', 'happy valley']
NZ = ['ellerslie', 'te rapa', 'matamata', 'pukekohe', 'trentham', 'tauranga', 'wanganui', 'otaki', 'riccarton', 'arawa', 'te aroha', 'taupo', 'new plymouth', 'waverley',
      'hastings', 'cambridge', 'ruakaka', 'wingatui', 'tauherenikau', 'ascot park', 'woodville', 'avondale', 'hawera', 'ashburton', 'timaru', 'pharlap', 'awapuni',
      'te awamutu', 'rotorua', 'waipa', 'gore', 'oamaru', 'rangiora', 'hokitika', 'greymouth', 'omakau', 'wyndham', 'waimate', 'phar lap', 'otago']


def region(track, going, au):
    t = str(track).lower()
    g = str(going)
    graded = bool(re.search(r'\d', g))
    if any(h in t for h in HK):
        return 'Hong Kong'
    if any(n in t for n in NZ):
        return 'New Zealand'
    if t in au and (graded or g in ('nan', 'None', '')):
        return 'Australia'
    if t in au and graded:
        return 'Australia'
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
    rp['reg'] = [region(t, g, au) for t, g in zip(rp.track, rp.going)]
    rp['eu'] = (rp.reg == 'Europe/other').astype(int)
    print('page runs', len(rp), rp.reg.value_counts().to_dict())
    g = rp.groupby('horse_id')
    # Europe/other runs among the last 8, and Australian runs since the last one
    eu8 = sum(g.eu.shift(k).fillna(0) for k in range(1, 9))
    rp['eu8'] = eu8
    since = np.full(len(rp), np.nan)
    hid = rp.horse_id.values
    eu = rp.eu.values
    cnt = {}
    for i in range(len(rp)):
        h = hid[i]
        c = cnt.get(h)
        since[i] = np.nan if c is None else c
        if eu[i] == 1:
            cnt[h] = 0
        elif c is not None:
            cnt[h] = c + 1
    rp['since_eu'] = since
    t = rp[(rp.reg == 'Australia') & (rp.date >= '2024-07-01') & (rp.n >= 3) & rp.f.notna() & rp.wpr.notna() & (rp.eu8 >= 2)].copy()
    base = rp[(rp.reg == 'Australia') & (rp.date >= '2024-07-01') & (rp.n >= 3) & rp.f.notna() & rp.wpr.notna() & (rp.eu8 == 0)]
    pd.set_option('display.width', 220)

    def tab(lab, x):
        m = x.miss
        print(f"  {lab:40s} n={len(m):6d} mean {m.mean():+.2f} median {m.median():+.2f} sd {m.std():.2f} MAE {m.abs().mean():.2f}")
    print('\nMiss (actual - formula), Australian runs since 2024-07 with 2+ Europe/other runs in the last 8:')
    tab('no overseas form (reference)', base)
    tab('all with Europe/other form', t)
    for lab, m in (('first start in Australia', t.since_eu == 0), ('second start', t.since_eu == 1), ('third start', t.since_eu == 2), ('fourth start or later', t.since_eu >= 3)):
        tab(lab, t[m])
    print('\nBy distance:')
    tab('Europe/other form, 2400m+', t[t.distance >= 2400])
    tab('Europe/other form, under 2400m', t[t.distance < 2400])
    tab('no overseas form, 2400m+', base[base.distance >= 2400])
    print('\nEurope/other form horses, by whether they won last start / ran well:')
    t['lastm'] = t.groupby('horse_id').miss.shift(1)
    # the Europe/other ratings themselves vs the same horses' Australian ratings (page ratings as given)
    both = rp[rp.horse_id.isin(rp[rp.eu == 1].horse_id.unique()) & (rp.date >= '2024-01-01')]
    lv = both.groupby(['horse_id', 'reg']).wpr.agg(['mean', 'count']).reset_index()
    a = lv[lv.reg == 'Australia'].set_index('horse_id')
    e = lv[lv.reg == 'Europe/other'].set_index('horse_id')
    j = e.join(a, lsuffix='_eu', rsuffix='_au', how='inner')
    j = j[(j.count_eu >= 2) & (j.count_au >= 2)]
    print(f"  horses with 2+ runs in each: {len(j)}  Europe/other rating minus Australian rating: mean {(j.mean_eu - j.mean_au).mean():+.2f} median {(j.mean_eu - j.mean_au).median():+.2f}")

    r = pd.read_csv(os.path.join(ROOT, 'runners.csv'), usecols=['date', 'venue', 'race', 'horse', 'horse_id', 'scratched', 'barrier'], low_memory=False)
    L = pd.read_csv(os.path.join(ROOT, 'wpr_projection_log.csv.gz'), low_memory=False).drop_duplicates('run_id', keep='last')
    cup = r[(r.date == '2026-11-03') & (r.venue == 'Flemington') & (r.race == 7) & (r.scratched.fillna(0) != 1) & (r.barrier > 0)]
    print('\n2026 Cup horses with Europe/other runs in the last 8: runs newest first as region:rating')
    for h, nm in zip(cup.horse_id, cup.horse):
        x = rp[rp.horse_id == h].sort_values('date').tail(8)
        if (x.reg == 'Europe/other').sum() == 0:
            continue
        s = ' '.join(f"{('EU' if q == 'Europe/other' else q[:2])}:{w:.0f}" for q, w in zip(x.reg.iloc[::-1], x.wpr.iloc[::-1]))
        print(f"  {nm:20s} au_since_eu={int((x.reg.values[::-1] != 'Europe/other').argmin()) if (x.reg == 'Europe/other').any() else 'na'}  {s}")


if __name__ == '__main__':
    main()
