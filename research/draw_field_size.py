"""Does the draw effect change with field size? (27 Oct 2026)
(1) Rating effect: within-race ATW rating (wpr + wfa_scale offset of the weight carried) against barrier, per field-size band, as points rail to widest (relative position),
    points per barrier step (absolute), and the share of within-race variance each explains.
(2) Price view: A2E of inside / middle / wide thirds of the field (relative position) per band, clean SP books only.
Run: PYTHONPATH=. python research/draw_field_size.py"""
import functools
import numpy as np, pandas as pd
import wfa_scale as W
cols = ['race_id', 'date', 'track', 'distance', 'field_size', 'barrier', 'priceStarting', 'positionFinish', 'isBarrierTrial', 'is_jumpout', 'race_class', 'wpr', 'weightCarried', 'horse_foaled', 'horse_age', 'horse_sex']
d = pd.concat([pd.read_csv(f'race_results_{y}.csv.gz', usecols=lambda c: c in cols, low_memory=False) for y in range(2017, 2027)])
d = d[(d.isBarrierTrial.astype(str) != 'True') & (d.is_jumpout.astype(str) != 'True') & ~d.race_class.astype(str).str.contains('Hurdle|Steeple', na=False)]
d['date'] = pd.to_datetime(d.date)
for c in ['distance', 'field_size', 'barrier', 'priceStarting', 'positionFinish', 'wpr', 'weightCarried']: d[c] = pd.to_numeric(d[c], errors='coerce')
d = d[(d.barrier > 0) & (d.field_size >= 5)]
d = d[d.barrier <= d.field_size + 2]
BANDS = [(5, 7), (8, 9), (10, 11), (12, 13), (14, 15), (16, 30)]
def band(n):
    for i, (a, b) in enumerate(BANDS):
        if a <= n <= b: return i
d['fb'] = d.field_size.map(band)
d['dg'] = np.where(d.distance <= 1300, 0, np.where(d.distance <= 1650, 1, 2))
LAB = ['5-7', '8-9', '10-11', '12-13', '14-15', '16+']; DG = ['up to 1300m', '1301-1650m', 'over 1650m']

@functools.lru_cache(None)
def off(foaled, age, sex, date, dist, wt):
    a = W.racing_age(foaled, date) if isinstance(foaled, str) and len(foaled) >= 10 else (None if pd.isna(age) else int(age))
    v = W.atw_offset(a, sex, date.date(), float(dist), wt)
    return np.nan if v is None else v
r = d[d.wpr.notna() & d.weightCarried.notna() & d.distance.notna()].copy()
r['c'] = [off(f, a, str(s).upper()[:1], dt, dist, w) for f, a, s, dt, dist, w in zip(r.horse_foaled, r.horse_age, r.horse_sex, r.date, r.distance, r.weightCarried)]
r = r[r.c.notna()]; r['atw'] = r.wpr + r.c
r['ad'] = r.atw - r.groupby('race_id').atw.transform('mean')
r['bf'] = (r.barrier - 1) / (r.field_size - 1)
r['bs'] = r.barrier - r.groupby('race_id').barrier.transform('mean')   # absolute barrier steps, centred in the race
def fit(x, col):
    xc = x[col] - x[col].mean(); sxx = (xc ** 2).sum(); b = (xc * x.ad).sum() / sxx
    e = x.ad - b * xc; sc = (xc * e).groupby(x.race_id).sum(); se = np.sqrt((sc ** 2).sum()) / sxx
    r2 = 1 - (e ** 2).sum() / (x.ad ** 2).sum()
    return b, se, r2
print(f'RATING EFFECT ({len(r):,} runs, {r.race_id.nunique():,} races)')
print('field   runs   | rail->widest pts (se)   R2     | per barrier step (se)   R2')
for dg in [None, 0, 1, 2]:
    print('-- distance:', 'all' if dg is None else DG[dg])
    for i, l in enumerate(LAB):
        x = r[(r.fb == i) & ((r.dg == dg) if dg is not None else True)]
        if len(x) < 3000: continue
        b, se, r2 = fit(x, 'bf'); b2, se2, r22 = fit(x, 'bs')
        print(f' {l:6s} {len(x):7,} | {b:+.2f} ({se:.2f})  {100*r2:.2f}%  | {b2:+.3f} ({se2:.3f})  {100*r22:.2f}%')
# price view
p = d[(d.priceStarting > 1)].copy()
p['won'] = (p.positionFinish == 1).astype(int); g = p.groupby('race_id')
p = p[(g.won.transform('sum') == 1) & (g.priceStarting.transform(lambda s: (1 / s).sum()).between(1.05, 2.0)) & (g.priceStarting.transform('size') >= 0.9 * g.field_size.transform('first'))]
p['pr'] = (1 / p.priceStarting) / p.groupby('race_id').priceStarting.transform(lambda s: (1 / s).sum())
p['bf'] = (p.barrier - 1) / (p.field_size - 1)
p['third'] = np.where(p.bf < 1 / 3, 0, np.where(p.bf < 2 / 3, 1, 2))
print(f'\nPRICE VIEW ({len(p):,} priced runners): A2E of inside / middle / wide third of the field (z against chance)')
for i, l in enumerate(LAB):
    x = p[p.fb == i]; out = []
    for t in range(3):
        z = x[x.third == t]; w, e = z.won.sum(), z.pr.sum(); zz = (w - e) / np.sqrt((z.pr * (1 - z.pr)).sum())
        out.append(f'{w / e:.3f} (z {zz:+.1f}, n={len(z):,})')
    print(f' {l:6s} ' + ' | '.join(out))
