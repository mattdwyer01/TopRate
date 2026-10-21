"""Track bias persistence on FULL fields (GPS data, VIC/SA/QLD 2021+): is the leaders-vs-closers and draw bias a property of the venue, of the day, or just race noise?
Per race: lead = Spearman(position after 400m, finishing order), draw = Spearman(barrier, finishing order) (VIC/SA only, QLD barriers unreliable). 8+ runners.
Reports ICCs by venue and by meeting-day, the correlation of a race's bias with (a) the same day's earlier races, (b) the venue's earlier meetings (trailing 10 meetings, 1 year),
and how much of the day-to-day swing a simple as-of estimate recovers. Run: PYTHONPATH=. python research/bias_persistence_gps.py"""
import sys
import numpy as np, pandas as pd
sys.path.insert(0, 'research')
import gps_counterfactual as G
g = G.gps_runs()
g['bf'] = np.nan
import glob
rc = pd.concat([pd.read_parquet(f, columns=['meet_code', 'race_no', 'start_utc', 'horse', 'barrier']) for f in sorted(glob.glob('data/gps/rc_gps_runs_20*.parquet'))])
rc['date'] = (pd.to_datetime(rc.start_utc, utc=True) + pd.Timedelta(hours=10)).dt.tz_localize(None).dt.normalize(); rc['hn'] = G.norm(rc.horse)
g = g.merge(rc[['date', 'hn', 'barrier']].drop_duplicates(['date', 'hn']), on=['date', 'hn'], how='left')
g['bf'] = g.barrier / g.n
def sp(a, b):
    ok = a.notna() & b.notna()
    return float(a[ok].rank().corr(b[ok].rank())) if ok.sum() >= 6 and a[ok].nunique() > 1 and b[ok].nunique() > 1 else np.nan
R = g.groupby('rk').apply(lambda x: pd.Series(dict(lead=sp(x.ep_f, x.finish), draw=sp(x.bf, x.finish), n=len(x), date=x.date.iloc[0], venue=x.venue_k.iloc[0], src=x.src.iloc[0]))).reset_index()
R = R[R.n >= 8].copy(); R['date'] = pd.to_datetime(R.date); R['md'] = R.venue + '|' + R.date.dt.strftime('%Y-%m-%d')
print('races', len(R), 'meetings', R.md.nunique(), 'venues', R.venue.nunique(), R.src.value_counts().to_dict(), 'dates', R.date.min().date(), R.date.max().date())
def icc(df, col, grp):
    d = df.dropna(subset=[col]); k = d.groupby(grp).size(); d = d[d[grp].isin(k[k >= 2].index)]
    g_ = d.groupby(grp)[col]; n = g_.size(); m = g_.mean(); grand = d[col].mean()
    msb = (n * (m - grand) ** 2).sum() / (len(m) - 1); msw = ((d[col] - g_.transform('mean')) ** 2).sum() / (len(d) - len(m)); n0 = (n.sum() - (n ** 2).sum() / n.sum()) / (len(m) - 1)
    return max(0.0, (msb - msw) / (msb + (n0 - 1) * msw))
for c, lab in (('lead', 'leaders vs closers'), ('draw', 'draw')):
    d = R.dropna(subset=[c])
    print(f'\n{lab}: races {len(d)}, mean {d[c].mean():+.3f}, sd of a race {d[c].std():.3f} (noise alone would be about {1 / np.sqrt(d.n.mean() - 1):.3f})')
    print(f'  share of variance by meeting-day (ICC) {icc(d, c, "md"):.2f}, by venue {icc(d, c, "venue"):.2f}')
    # venue-level persistence: this meeting vs the venue's previous 10 meetings in the past year
    M = d.groupby(['venue', 'date']).agg(v=(c, 'mean'), k=(c, 'size')).reset_index().sort_values(['venue', 'date']); M = M[M.k >= 3]
    M['prior'] = M.groupby('venue').v.transform(lambda s: s.shift(1).rolling(10, min_periods=4).mean())
    a = M.dropna(subset=['prior']); print(f'  meeting mean vs the venue\'s previous 10 meetings: corr {a[["v", "prior"]].corr().iloc[0, 1]:+.2f} (n={len(a)})')
    # within-day
    d = d.sort_values(['md', 'date']); d['i'] = d.groupby('md').cumcount()
    cs = d.groupby('md')[c].cumsum() - d[c]; d['e'] = (cs / d.i.replace(0, np.nan)).where(d.i >= 3)
    a = d.dropna(subset=['e']); print(f'  race vs mean of the 3+ earlier races the same day: corr {a[[c, "e"]].corr().iloc[0, 1]:+.2f} (n={len(a)}), slope {np.polyfit(a.e, a[c], 1)[0]:+.2f}')
    # by size of day mean: how big are the biggest days
    dm = d.groupby('md')[c].agg(['mean', 'size']); dm = dm[dm['size'] >= 6]
    print(f'  meeting-day mean (6+ races): sd {dm["mean"].std():.3f} vs noise-only {d[c].std() / np.sqrt(dm["size"].mean()):.3f}; days beyond +-0.25: {((dm["mean"].abs() > 0.25).mean()):.0%}')
