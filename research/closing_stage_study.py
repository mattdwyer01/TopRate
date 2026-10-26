"""Where in a race are the time differences between horses made, and how much of each part can be predicted before the race? (26 Oct 2026)

The rating miss is mostly per-run noise (rating_noise_decomposition.py), route and early position explain under 2% of it, and the rating is built from the
finishing margin. So the question left is the closing stage: split each runner's race time into three phases from the racing.com 200m sections (VIC and SA,
2021 on) and measure, for each phase, (a) its share of the variance of the finishing time within a race and (b) how much of it is predictable from what is
known before the race.

  phases (by distance to go): E = every full 200m section before the 800m mark, M = 800m to 400m, L = the last 400m
  deficit = the runner's phase time minus the race mean of that phase (seconds, positive = slower than the field); total = E + M + L

  A. After the fact: variance of the total explained by each phase (cov(phase, total) / var(total)), and the corr between phases.
  B. Before the race: LightGBM on the horse's own earlier deficits (last 4: mean and spread per phase) and race basics (distance, barrier, field size,
     going, track), then the same plus the field's pace pressure (the field's earlier early deficits: tempo, own early rank, likely leaders), fit before 2025
     and scored 2025 on: R2 for E, M, L and the total, and the total in rating points (1 second is about 6.8 lengths, about 2.15 rating points a length).

  PYTHONPATH=. python research/closing_stage_study.py
"""
import glob
import os
import re
import sys

import lightgbm as lgb
import numpy as np
import pandas as pd

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..'))
GPS = os.path.join(ROOT, 'data', 'gps')
PTS_PER_SEC = 6.8 * 2.15


def clean(s):
    return s.astype(str).str.lower().str.replace(r'\s*\([a-z]{2,3}\)\s*$', '', regex=True).str.replace(r'[^a-z0-9 ]', '', regex=True).str.strip()


def load():
    runs = pd.concat([pd.read_parquet(f, columns=['meet_code', 'race_no', 'venue', 'start_utc', 'race_distance', 'horse', 'tab_no', 'barrier', 'finish'])
                      for f in sorted(glob.glob(os.path.join(GPS, 'rc_gps_runs_*.parquet')))], ignore_index=True)
    runs['meet_code'] = runs.meet_code.astype(str)
    runs['date'] = pd.to_datetime(runs.start_utc).dt.tz_convert('Australia/Melbourne').dt.tz_localize(None).dt.normalize()
    runs['dist'] = runs.race_distance.astype(str).str.replace('m', '').astype(float)
    runs['hk'] = clean(runs.horse)
    s = pd.concat([pd.read_parquet(f, columns=['meet_code', 'race_no', 'tab_no', 'from_m', 'to_m', 'split_s', 'avg_speed_ms'])
                   for f in sorted(glob.glob(os.path.join(GPS, 'rc_gps_sections_*.parquet')))], ignore_index=True)
    s['meet_code'] = s.meet_code.astype(str)
    w = s.from_m - s.to_m
    s = s[(w >= 190) & (w <= 210) & (s.split_s > 8) & (s.split_s < 20) & (s.avg_speed_ms > 8) & (s.avg_speed_ms < 22)].copy()
    s['ph'] = np.where(s.to_m < 400, 'L', np.where(s.to_m < 800, 'M', 'E'))
    k = ['meet_code', 'race_no', 'tab_no']
    t = s.groupby(k + ['ph']).agg(t=('split_s', 'sum'), n=('split_s', 'size')).reset_index()
    p = t.pivot_table(index=k, columns='ph', values=['t', 'n'], aggfunc='first')
    p.columns = [f'{a}_{b}' for a, b in p.columns]
    p = p.reset_index()
    p = p[(p.n_L == 2) & (p.n_M == 2) & (p.n_E >= 2)]
    d = runs.merge(p, on=k)
    d = d[d.finish.between(1, 40)]
    d['nr'] = d.groupby(['meet_code', 'race_no']).tab_no.transform('size')
    d = d[d.nr >= 8].copy()
    # a phase must be measured over the same sections for the whole field to be comparable
    d['key'] = d.meet_code + '|' + d.race_no.astype(str)
    modeE = d.groupby('key').n_E.transform(lambda x: x.mode().iloc[0])
    d = d[d.n_E == modeE].copy()           # a phase must cover the same sections for the whole field
    d['nr'] = d.groupby('key').tab_no.transform('size')
    d = d[d.nr >= 8].copy()
    for c in ('E', 'M', 'L'):
        d[f'd_{c}'] = d[f't_{c}'] - d.groupby('key')[f't_{c}'].transform('mean')
    d['d_T'] = d.d_E + d.d_M + d.d_L
    return d.sort_values(['hk', 'date', 'key']).reset_index(drop=True)


def main():
    d = load()
    print(f'runs {len(d):,} in {d.key.nunique():,} races, {d.hk.nunique():,} horses, {d.date.min().date()} to {d.date.max().date()}')
    sd = {c: d[f'd_{c}'].std() for c in ('E', 'M', 'L', 'T')}
    print('sd of the within-race deficit (seconds): ' + ', '.join(f'{c} {v:.2f}' for c, v in sd.items()) + f'  | total in rating points {sd["T"] * PTS_PER_SEC:.1f}')
    vt = d.d_T.var()
    print('\nA. share of the finishing-time variance made in each phase, cov(phase, total) / var(total):')
    for c in ('E', 'M', 'L'):
        print(f'   {c}: {100 * np.cov(d[f"d_{c}"], d.d_T)[0, 1] / vt:5.1f}%')
    print('   corr between phases: E-M %.2f, E-L %.2f, M-L %.2f' % (d.d_E.corr(d.d_M), d.d_E.corr(d.d_L), d.d_M.corr(d.d_L)))

    # B. history features
    g = d.groupby('hk')
    for c in ('E', 'M', 'L', 'T'):
        lags = pd.concat([g[f'd_{c}'].shift(k) for k in range(1, 5)], axis=1)
        d[f'h_{c}'] = lags.mean(axis=1)
        d[f'hs_{c}'] = lags.std(axis=1)
    d['h_n'] = g.cumcount().astype(float)
    d['barfrac'] = (d.barrier - 1) / (d.nr - 1)
    d['trk'] = d.venue.astype('category')
    # pace pressure of the field from earlier runs
    k = 'key'
    d['f_tempo'] = d.groupby(k).h_E.transform('mean')
    d['f_E_rel'] = d.h_E - d.f_tempo
    d['f_E_rank'] = d.groupby(k).h_E.rank(method='min')
    d['f_leaders'] = d.groupby(k).h_E.transform(lambda x: (x.rank() <= 3).sum())
    d['f_known'] = d.groupby(k).h_E.transform('count') / d.nr
    d['f_L_rel'] = d.h_L - d.groupby(k).h_L.transform('mean')
    base = ['h_E', 'h_M', 'h_L', 'h_T', 'hs_E', 'hs_M', 'hs_L', 'h_n', 'dist', 'barfrac', 'nr', 'trk']
    pace = base + ['f_tempo', 'f_E_rel', 'f_E_rank', 'f_leaders', 'f_known', 'f_L_rel']
    tr = d[(d.date < '2025-01-01') & d.h_E.notna()]
    te = d[(d.date >= '2025-01-01') & d.h_E.notna()]
    print(f'\nB. predictability before the race (fit before 2025: {len(tr):,} runs; scored 2025 on: {len(te):,} runs in {te.key.nunique():,} races)')
    P = dict(learning_rate=0.05, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1, n_estimators=400)
    print(f'   {"target":8s} {"horse only R2":>14s} {"+ pace pressure R2":>19s}   sd (s)   residual sd as rating points (+pace)')
    for c in ('E', 'M', 'L', 'T'):
        out = []
        for cols in (base, pace):
            m = lgb.LGBMRegressor(**P).fit(tr[cols], tr[f'd_{c}'])
            pr = m.predict(te[cols])
            r2 = 1 - ((te[f'd_{c}'] - pr) ** 2).sum() / ((te[f'd_{c}'] - te[f'd_{c}'].mean()) ** 2).sum()
            out.append((r2, np.sqrt(((te[f'd_{c}'] - pr) ** 2).mean())))
        print(f'   {c:8s} {out[0][0]:14.3f} {out[1][0]:19.3f}   {te[f"d_{c}"].std():6.2f}   {out[1][1] * PTS_PER_SEC:6.1f}')
    d.to_pickle(os.environ.get('CS_OUT', '/tmp/closing_stage.pkl'))


if __name__ == '__main__':
    sys.exit(main())
