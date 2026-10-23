"""Ground-lost correction for the time-based speed figure (23 Oct 2026). A horse that ran 8m further than the field lost about 3 lengths of time to the path it took, so its figure
understates its speed. Do the GPS metres (ground lost vs the race, from racing.com, Racing Queensland and ATC) make the history a better predictor of the NEXT speed figure?
Predictor = recency-weighted mean (half-life 4 runs) of the last 4 figures, with each GPS-covered run's figure corrected by k lengths per metre of extra ground. Fit on 2025 targets,
scored on 2026 targets, model only (no price). Run: PYTHONPATH=. python analysis/trip_map/spd_ground_test.py"""
import os, sys
import numpy as np, pandas as pd
sys.path.insert(0, os.path.dirname(__file__)); sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..'))
import gps_feats as GF
import build_trip_map as B
import speed_rating as SR
rr, FL, HIST, CONT = GF.build()
ft = SR.figure_table(2019); ft['hn'] = B.clean_name(ft.key)
d = ft.merge(rr[['hn', 'date', 'extra_rel', 'lane_rel', 'gps']].drop_duplicates(['hn', 'date']), on=['hn', 'date'], how='left')
d['has'] = d.extra_rel.notna()
d = d.sort_values(['hn', 'date']).reset_index(drop=True)
print('figures', len(d), 'with GPS ground lost', int(d.has.sum()), flush=True)
W = np.array([0.5 ** (a / 4) for a in range(4)])
g = d.groupby('hn')
S = np.column_stack([g.sp.shift(a + 1).values for a in range(4)])
X = np.column_stack([g.extra_rel.shift(a + 1).values for a in range(4)])
ok = ~np.isnan(S)
wsum = (W * ok).sum(1)
d['n_prev'] = ok.sum(1); d['n_gps_prev'] = (~np.isnan(X)).sum(1)
d['raw'] = np.where(wsum > 0, (np.where(ok, S, 0) * W).sum(1) / np.where(wsum > 0, wsum, 1), np.nan)
d['corr_term'] = np.where(wsum > 0, (np.where(~np.isnan(X) & ok, X, 0) * W).sum(1) / np.where(wsum > 0, wsum, 1), np.nan)   # weighted mean metres of extra ground (0 when no GPS)
d['err'] = d.sp - d.raw
tr = d[(d.date >= '2025-01-01') & (d.date < '2026-01-01') & (d.n_prev >= 3) & (d.n_gps_prev >= 2)]
te = d[(d.date >= '2026-01-01') & (d.n_prev >= 3) & (d.n_gps_prev >= 2)]
print('targets with >=2 GPS runs among the last 4: train', len(tr), 'test', len(te))
# effective lengths per metre: regress (next - raw) on the weighted mean metres of extra ground (negative = ground lost lowers the old figures, so the correction raises them)
for lab, df in (('2025 fit', tr), ('2026', te)):
    b = np.polyfit(df.corr_term, df.err, 1)
    print(f'  {lab}: next figure minus predictor, slope on weighted mean extra metres {b[0]:+.3f} lengths per metre (mechanical value +0.42 = 1 length per 2.4 m)')
k = np.polyfit(tr.corr_term, tr.err, 1)[0]
print('\nout of sample (2026):')
for lab, kk in (('raw predictor', 0.0), ('mechanical k = 0.42', 0.42), (f'fitted k = {k:.3f}', k), ('half mechanical k = 0.21', 0.21)):
    p = te.raw + kk * te.corr_term
    e = te.sp - p
    print(f'  {lab:28s} n={len(te)} RMSE {np.sqrt((e ** 2).mean()):.4f} lengths, MAE {e.abs().mean():.4f}, corr with next figure {np.corrcoef(p, te.sp)[0, 1]:.4f}')
base = np.sqrt(((te.sp - te.raw) ** 2).mean()); fit = np.sqrt(((te.sp - te.raw - k * te.corr_term) ** 2).mean())
bs = []
rng = np.random.default_rng(3); idx = np.arange(len(te))
e0 = (te.sp - te.raw).values ** 2; e1 = (te.sp - te.raw - k * te.corr_term).values ** 2
dd = e0 - e1
print(f'  squared-error gain per run {dd.mean():+.4f} (se {dd.std() / np.sqrt(len(dd)):.4f}); RMSE {base:.4f} -> {fit:.4f} ({100 * (1 - fit / base):.2f}% better)')
# the high-ground-loss runs: where the correction is large
big = te[te.corr_term.abs() >= 3]
print(f'  runs with a weighted mean extra ground of 3m or more (n={len(big)}): RMSE raw {np.sqrt(((big.sp - big.raw) ** 2).mean()):.4f} -> corrected {np.sqrt(((big.sp - big.raw - k * big.corr_term) ** 2).mean()):.4f}')

# why the correction does not help: (1) within the same run, does extra ground really cost time? (2) does a horse's ground loss repeat from run to run?
dd2 = d[d.has].copy()
dd2['sp_c'] = dd2.sp - dd2.groupby(['date']).sp.transform('mean')    # crude: demean by day (meeting-level par error)
b = np.polyfit(dd2.extra_rel.clip(-15, 25), dd2.sp_c, 1)
print(f'\nsame-run slope of figure (demeaned by day) on extra metres {b[0]:+.3f} lengths per metre (mechanical -0.42)')
gh = dd2.groupby('hn').extra_rel
prev = gh.shift(1); ok2 = prev.notna() & dd2.extra_rel.notna()
print('persistence: corr of extra ground with the same horse\'s previous GPS run %.3f (n=%d); lane_rel persistence %.3f' % (np.corrcoef(prev[ok2], dd2.extra_rel[ok2])[0, 1], int(ok2.sum()), dd2.lane_rel.corr(dd2.groupby('hn').lane_rel.shift(1))))
