"""Stride and speed profiles from the Racing Victoria chart PDFs (26 Oct 2026): does a horse's stride length, stride rate or speed fade in one run predict its NEXT run's margin beyond
that run's own margin?  727 chart-layout races (Jul-Oct 2026), consecutive run pairs of the same horse inside the sample.  Small sample: a screen, not a verdict.
  PYTHONPATH=. python research/stride_profile_test.py"""
import glob, numpy as np, pandas as pd
d = pd.read_parquet('data/gps/rc_pdf_chart_sections.parquet'); d['meet_code'] = d.meet_code.astype(str)
r = pd.concat([pd.read_parquet(f) for f in glob.glob('data/gps/rc_gps_runs_*.parquet')]); r['meet_code'] = r.meet_code.astype(str)
d['dist'] = d.label.str.extract(r'(\d+)')[0].astype(float)
key = ['meet_code', 'race_no', 'tab_no']
def agg(g):
    late = g[g.dist <= 400]; mid = g[(g.dist > 400) & (g.dist <= 1000)]
    return pd.Series(dict(sl_late=late.stride_m.mean(), sl_mid=mid.stride_m.mean(), sr_late=late.stride_hz.mean(), sr_mid=mid.stride_hz.mean(), v_late=late.avg_kmh.mean(), v_mid=mid.avg_kmh.mean()))
f = d.groupby(key).apply(agg).reset_index()
f['sl_fade'] = f.sl_late - f.sl_mid; f['sr_fade'] = f.sr_late - f.sr_mid; f['v_fade'] = f.v_late - f.v_mid
x = f.merge(r[key + ['horse', 'start_utc', 'beaten_margin_l', 'finish', 'race_distance']], on=key)
x['m'] = pd.to_numeric(x.beaten_margin_l, errors='coerce')
x['m_dm'] = x.m - x.groupby(['meet_code', 'race_no']).m.transform('mean')
for c in ('sl_late', 'sr_late', 'v_late', 'sl_fade', 'sr_fade', 'v_fade'):
    x[c + '_z'] = x[c] - x.groupby(['meet_code', 'race_no'])[c].transform('mean')
x['start_utc'] = pd.to_datetime(x.start_utc); x = x.sort_values(['horse', 'start_utc'])
g = x.groupby('horse')
x['next_m'] = g.m_dm.shift(-1)
z = x.dropna(subset=['next_m', 'm_dm']).copy()
print(f'{len(x):,} runner-races, {len(z):,} consecutive pairs, {z.horse.nunique():,} horses')
print('\nex-post: within-race corr of the run profile with its own beaten margin (negative = longer/faster is better)')
for c in ('sl_late_z', 'sr_late_z', 'v_late_z', 'sl_fade_z', 'sr_fade_z', 'v_fade_z'):
    s = x.dropna(subset=[c, 'm_dm']); print(f'  {c:11s} corr {np.corrcoef(s[c], s.m_dm)[0,1]:+.3f}  (n={len(s):,})')
print('\npredictive: next run margin (race-demeaned lengths) on run 1 margin, then adding each profile term (OLS, paired gain in squared error, 5-fold)')
from sklearn.model_selection import KFold
from sklearn.linear_model import Ridge
def cv(cols):
    s = z.dropna(subset=cols); e = np.zeros(len(s))
    for a, b in KFold(5, shuffle=True, random_state=0).split(s):
        m = Ridge(1.0).fit(s.iloc[a][cols], s.iloc[a].next_m); e[b] = (s.iloc[b].next_m - m.predict(s.iloc[b][cols])) ** 2
    return s.index, e
for extra in ([], ['sl_late_z'], ['sr_late_z'], ['v_late_z'], ['sl_fade_z'], ['sr_fade_z'], ['v_fade_z'], ['sl_late_z', 'sr_late_z', 'sl_fade_z', 'sr_fade_z']):
    base = ['m_dm']; i0, e0 = cv(base + [c for c in extra]); 
    # same rows for baseline
    s = z.loc[i0]; eb = np.zeros(len(s))
    for a, b in KFold(5, shuffle=True, random_state=0).split(s):
        m = Ridge(1.0).fit(s.iloc[a][base], s.iloc[a].next_m); eb[b] = (s.iloc[b].next_m - m.predict(s.iloc[b][base])) ** 2
    d_ = eb - e0
    print(f'  + {",".join(extra) or "(none)":42s} n={len(s):5d}  gain {d_.mean():+.4f} (se {d_.std()/np.sqrt(len(d_)):.4f})  rmse base {np.sqrt(eb.mean()):.3f}')
