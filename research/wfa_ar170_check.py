"""AR 170 (northern hemisphere allowance) and the remaining 3yo gap, checked against offsets measured on runner pages for known races (/tmp/atw_exact.pkl from
atw_offset_exact.py; sire country from the results files). Run with PYTHONPATH=."""
import glob
import numpy as np, pandas as pd
import wfa_scale as W
S = pd.concat([pd.read_csv(f, usecols=['horse_id', 'sire_country'], low_memory=False) for f in sorted(glob.glob('race_results_202[56]*.csv.gz')) if '_rc' not in f]).drop_duplicates('horse_id', keep='last')
M = pd.read_pickle('/tmp/atw_exact.pkl').merge(S, on='horse_id', how='left')
M['wc'] = pd.to_numeric(M.weight_carried, errors='coerce'); M = M.dropna(subset=['wc', 'distance', 'foaled'])
M['age'] = [W.racing_age(f, d) for f, d in zip(M.foaled, M.date)]
M['sex'] = M.horse_sex.astype(str).str.upper().str[:1]
M['nh'] = [W.is_nh_eligible(c, f) for c, f in zip(M.sire_country, M.foaled)]
M['base'] = [W.std_weight(a, s, d, dist) for a, s, d, dist in zip(M.age, M.sex, M.date, M.distance)]
M = M.dropna(subset=['base'])
M['al'] = [W.nh_allowance(a, d, dist) if n else 0.0 for a, d, dist, n in zip(M.age, M.date, M.distance, M.nh)]
M['e0'] = M.off - 0.8 * (M.base - M.wc); M['e1'] = M.off - 0.8 * (M.base - M.al - M.wc)
M['ag'] = M.age.clip(upper=5)
for k, g in M.groupby(['ag', 'nh']):
    print(k, len(g), 'without AR170 within .15 %.2f median %.2f | with %.2f median %.2f' % ((g.e0.abs() < .15).mean(), g.e0.median(), (g.e1.abs() < .15).mean(), g.e1.median()))
x = M[M.age == 3].copy(); x['err_kg'] = x.e0 / 0.8; x['blk'] = x.distance.map(W.block_index)
print('3yo error in kg by distance block (measured standard weight minus table):')
print(x.groupby('blk').err_kg.agg(['count', 'median']).round(2).to_string())
