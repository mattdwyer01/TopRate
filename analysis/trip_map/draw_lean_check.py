"""Does the mid-meeting draw lean help the Proj? (23 Oct 2026) Production rule (projection/run.py): for a race with 8+ runners, lean = mean over the EARLIER races of the same meeting (8+ runners, top 4 known,
at least 3 such races) of (mean barrier fraction of the top 4 - 0.5); Proj += clip(15 x lean x (barrier fraction - 0.5), +-3). Tested on the out-of-sample Huber-4 Proj of 2025 and 2026
(/tmp/train_ctx_gps_oos.parquet): miss accuracy with and without it, the best strength fitted on 2025 and scored on 2026, and model-only winner accuracy on partial fields.
Run: PYTHONPATH=. python analysis/trip_map/draw_lean_check.py"""
import glob, os, sys
import numpy as np, pandas as pd
from scipy.optimize import minimize_scalar
sys.path.insert(0, os.path.dirname(__file__))
import build_trip_map as B
ROOT = B.ROOT
cols = ['race_id', 'meeting_id', 'date', 'raceNumber', 'track', 'barrier', 'field_size', 'positionFinish', 'horse', 'isBarrierTrial']
d = pd.concat([pd.read_csv(f, usecols=lambda c: c in cols, low_memory=False) for f in sorted(glob.glob(os.path.join(ROOT, 'race_results_202[456].csv.gz')))])
d = d[~d.isBarrierTrial.astype(bool)].drop_duplicates(['race_id', 'horse']).copy()
d['date'] = pd.to_datetime(d.date).dt.normalize().astype('datetime64[ns]'); d['hn'] = B.clean_name(d.horse)
d['bfrac'] = (d.barrier - 1) / (d.field_size - 1).clip(lower=1)
top = d[(d.positionFinish <= 4) & (d.field_size >= 8)]
rl = top.groupby('race_id').agg(n=('bfrac', 'size'), lv=('bfrac', 'mean')); rl = rl[rl.n == 4]; rl['lv'] = rl.lv - 0.5
races = d.groupby('race_id').agg(mid=('meeting_id', 'first'), date=('date', 'first'), track=('track', 'first'), rn=('raceNumber', 'first')).join(rl[['lv']])
races['mkey'] = races.mid.astype(str).where(races.mid.notna(), races.date.astype(str) + races.track.astype(str))
races = races.sort_values(['mkey', 'rn'])
g = races.groupby('mkey')
races['lean'] = g.lv.transform(lambda s: s.shift(1).expanding().mean())
races['n_prev'] = g.lv.transform(lambda s: s.shift(1).expanding().count())
races.loc[races.n_prev < 3, 'lean'] = np.nan
d = d.merge(races[['lean']], left_on='race_id', right_index=True, how='left')
d = d.drop_duplicates(['hn', 'date'])[['hn', 'date', 'lean', 'bfrac', 'field_size']].rename(columns={'field_size': 'fs_csv'})
pg = pd.read_parquet('/tmp/train_ctx_gps_oos.parquet'); pg['date'] = pd.to_datetime(pg.date).astype('datetime64[ns]')
m = pg.merge(d, on=['hn', 'date'], how='left')
m['miss0'] = m.wpr - m.proj0
x = m.lean * (m.bfrac - 0.5)
ok = m.lean.notna() & (m.fs_csv >= 8) & m.bfrac.notna()
m['x'] = x.where(ok, 0.0)
m['adj'] = (15.0 * m.x).clip(-3, 3); m['miss1'] = m.miss0 - m.adj
print('runs', len(m), '| with a lean adjustment applied (8+ field, 3+ earlier races): %.1f%%, |adj| >= 1 on %.1f%%, mean |adj| %.2f' % (100 * ok.mean(), 100 * (m.adj.abs() >= 1).mean(), m.adj.abs()[ok].mean()))
def st(e): return f'MAE {e.abs().mean():.4f} rmse {np.sqrt((e ** 2).mean()):.4f}'
def pair(e0, e1):
    a = e0.abs() - e1.abs(); s = e0 ** 2 - e1 ** 2
    return f'abs gain {a.mean():+.4f} (se {a.std() / np.sqrt(len(a)):.4f}), sq gain {s.mean():+.4f} (se {s.std() / np.sqrt(len(s)):.4f})'
for yr, sel in (('2025', m.date < '2026-01-01'), ('2026', m.date >= '2026-01-01')):
    for lab, msk in (('all runs', sel), ('runs the lean touches (8+ field, lean known)', sel & ok), ('runs with |adj| >= 1', sel & (m.adj.abs() >= 1))):
        dd = m[msk]; print(f'{yr} {lab:46s} n={len(dd):6d} Proj as is: {st(dd.miss0)} | with lean: {st(dd.miss1)} | {pair(dd.miss0, dd.miss1)}')
# best strength: slope of the miss on lean x (bf - 0.5)
for yr, sel in (('2025', m.date < '2026-01-01'), ('2026', m.date >= '2026-01-01')):
    dd = m[sel & ok]; b = np.polyfit(dd.x, dd.miss0, 1)[0]; se = np.sqrt(((dd.miss0 - np.polyval(np.polyfit(dd.x, dd.miss0, 1), dd.x)) ** 2).mean() / (len(dd) * dd.x.var()))
    print(f'{yr}: fitted strength k = {b:.1f} (se {se:.1f}) vs production 15')
k25 = np.polyfit(m[(m.date < '2026-01-01') & ok].x, m[(m.date < '2026-01-01') & ok].miss0, 1)[0]
t = m[(m.date >= '2026-01-01')]
print(f'2026 scored with k fitted on 2025 ({k25:.1f}, capped at +-3): ', pair(t.miss0, t.miss0 - (k25 * t.x).clip(-3, 3)))
# by lean extreme: do wide barriers really do better on wide-leaning days?
dd = m[ok & (m.date >= '2025-01-01')].copy(); dd['third'] = pd.cut(dd.bfrac, [-0.01, 0.33, 0.66, 1.01], labels=['inside', 'middle', 'wide']); dd['leanbin'] = pd.cut(dd.lean, [-1, -0.10, 0.10, 1], labels=['inside-leaning', 'neutral', 'wide-leaning'])
print('\nmean miss (actual - Proj) by barrier third and the meeting lean so far:')
print(dd.pivot_table(index='leanbin', columns='third', values='miss0', aggfunc=['mean', 'size'], observed=True).round(2).to_string())
# winners, partial fields
w = m[m.rid.notna() & (m.n >= 3)].copy(); w['win'] = (w.positionFinish == 1).astype(int)
gb = w.groupby('rid'); w = w[(gb.win.transform('sum') == 1) & (gb.win.transform('size') >= 5)].copy()
w['p1'] = w.proj0 + w.adj
def ll(col, beta, df):
    s = beta * (df[col] - df.groupby('rid')[col].transform('mean')); mx = s.groupby(df.rid).transform('max'); ex = np.exp(s - mx); den = ex.groupby(df.rid).transform('sum'); return np.log(ex / den)[df.win == 1]
tr, te = w[w.date < '2026-01-01'], w[w.date >= '2026-01-01']
b0 = minimize_scalar(lambda x: -ll('proj0', x, tr).sum(), bounds=(0.01, 1), method='bounded').x; b1 = minimize_scalar(lambda x: -ll('p1', x, tr).sum(), bounds=(0.01, 1), method='bounded').x
l0, l1 = ll('proj0', b0, te), ll('p1', b1, te); dd = l1.values - l0.values
print(f'\nWINNERS (model only, partial fields, beta from 2025): 2026 races {te.rid.nunique()} | Proj {l0.mean():.4f} -> with lean {l1.mean():.4f}, gain {dd.mean():+.4f} (se {dd.std() / np.sqrt(len(dd)):.4f})')
dd2 = te[te.adj.abs() >= 1]; rs = set(dd2.rid)
mask = te.loc[te.win == 1, 'rid'].isin(rs).values
print(f'  races where the lean moves someone by 1+ point: {int(mask.sum())}, gain {dd[mask].mean():+.4f} (se {dd[mask].std() / np.sqrt(max(mask.sum(), 1)):.4f})')
