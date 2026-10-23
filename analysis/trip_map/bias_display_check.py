"""Judge the DISPLAY parts of the track-bias update (23 Oct 2026). (1) Draw-lean banner / row chip: a runner is flagged when the lean moved its Proj by >= 0.3. Do flagged runners behave the way the flag says?
(2) Meeting lean line (racing.com GPS, VIC/SA): shown when the earlier races (3+) average a leaders lean >= +0.45 or a fence lean >= +0.35. Rebuilt from the GPS history (rank correlation per race of position after 400m,
average rail distance and barrier with the finishing order), then: does the flag persist into the next race, and do the horses the line favours beat the Proj on flagged days?
Needs /tmp/train_ctx_gps_oos.parquet. Run: PYTHONPATH=. python analysis/trip_map/bias_display_check.py"""
import glob, os, sys
import numpy as np, pandas as pd
sys.path.insert(0, os.path.dirname(__file__))
import build_trip_map as B
ROOT = B.ROOT; G = os.path.join(ROOT, 'data', 'gps')
# ---------------- draw lean per race (production rule), applied to the out-of-sample Proj
cols = ['race_id', 'meeting_id', 'date', 'raceNumber', 'track', 'barrier', 'field_size', 'positionFinish', 'horse', 'isBarrierTrial']
d = pd.concat([pd.read_csv(f, usecols=lambda c: c in cols, low_memory=False) for f in sorted(glob.glob(os.path.join(ROOT, 'race_results_202[456].csv.gz')))])
d = d[~d.isBarrierTrial.astype(bool)].drop_duplicates(['race_id', 'horse']).copy()
d['date'] = pd.to_datetime(d.date).dt.normalize().astype('datetime64[ns]'); d['hn'] = B.clean_name(d.horse); d['bfrac'] = (d.barrier - 1) / (d.field_size - 1).clip(lower=1)
top = d[(d.positionFinish <= 4) & (d.field_size >= 8)]
rl = top.groupby('race_id').agg(n=('bfrac', 'size'), lv=('bfrac', 'mean')); rl = rl[rl.n == 4]; rl['lv'] = rl.lv - 0.5
races = d.groupby('race_id').agg(mid=('meeting_id', 'first'), date=('date', 'first'), track=('track', 'first'), rn=('raceNumber', 'first')).join(rl[['lv']])
races['mkey'] = races.mid.astype(str).where(races.mid.notna(), races.date.astype(str) + races.track.astype(str)); races = races.sort_values(['mkey', 'rn'])
g = races.groupby('mkey'); races['lean'] = g.lv.transform(lambda s: s.shift(1).expanding().mean()); races['n_prev'] = g.lv.transform(lambda s: s.shift(1).expanding().count()); races.loc[races.n_prev < 3, 'lean'] = np.nan
d = d.merge(races[['lean']], left_on='race_id', right_index=True, how='left')
d = d.drop_duplicates(['hn', 'date'])[['hn', 'date', 'lean', 'bfrac', 'field_size']].rename(columns={'field_size': 'fs_csv'})
pg = pd.read_parquet('/tmp/train_ctx_gps_oos.parquet'); pg['date'] = pd.to_datetime(pg.date).astype('datetime64[ns]')
m = pg.merge(d, on=['hn', 'date'], how='left'); m['miss0'] = m.wpr - m.proj0
ok = m.lean.notna() & (m.fs_csv >= 8) & m.bfrac.notna()
m['adj'] = (15.0 * m.lean * (m.bfrac - 0.5)).clip(-3, 3).where(ok, 0.0)
print('=== 1. DRAW-LEAN FLAG (|adj| >= 0.3 moves the runner) ===')
n_all = len(m); fl_up, fl_dn = m.adj >= 0.3, m.adj <= -0.3
print(f'runs flagged: helped {100 * fl_up.mean():.1f}%, hurt {100 * fl_dn.mean():.1f}% of all runs ({100 * (fl_up | fl_dn).sum() / max(ok.sum(), 1):.1f}% of the runs the lean can touch)')
base = m[ok & ~(fl_up | fl_dn)].miss0
for lab, msk in (('flagged HELPED (adj >= +0.3)', fl_up), ('flagged HURT (adj <= -0.3)', fl_dn)):
    s = m[msk]; diff = s.miss0.mean() - base.mean(); se = np.sqrt(s.miss0.var() / len(s) + base.var() / len(base))
    print(f'  {lab:30s} n={len(s):5d} mean miss of the Proj WITHOUT the lean {s.miss0.mean():+.2f} vs unflagged {base.mean():+.2f}: difference {diff:+.2f} (se {se:.2f}); the flag claims {s.adj.mean():+.2f}')
# does the lean change the top pick, and is the new top pick better?
w = m[m.rid.notna() & (m.n >= 3)].copy(); w['win'] = (w.positionFinish == 1).astype(int); gb = w.groupby('rid'); w = w[(gb.win.transform('sum') == 1) & (gb.win.transform('size') >= 5)].copy()
w['p1'] = w.proj0 + w.adj
w['r0'] = w.groupby('rid').proj0.rank(ascending=False, method='first'); w['r1'] = w.groupby('rid').p1.rank(ascending=False, method='first')
ch = w.groupby('rid').apply(lambda z: (z.loc[z.r0 == 1].index[0] != z.loc[z.r1 == 1].index[0]))
rs = ch[ch].index
print(f'races where the lean changes the #1: {len(rs)} of {w.rid.nunique()} ({100 * len(rs) / w.rid.nunique():.1f}%)')
if len(rs):
    z = w[w.rid.isin(rs)]
    print(f'   old #1 wins {100 * z[z.r0 == 1].win.mean():.1f}%, new #1 wins {100 * z[z.r1 == 1].win.mean():.1f}% (n={len(rs)}; a gap of 8 points is about one standard error)')
# ---------------- 2. meeting lean line from GPS (rc = VIC/SA)
rcr = pd.concat([pd.read_parquet(f) for f in sorted(glob.glob(os.path.join(G, 'rc_gps_runs_*.parquet')))])
rcr['date'] = pd.to_datetime(rcr.start_utc).dt.tz_convert('Australia/Melbourne').dt.tz_localize(None).dt.normalize().astype('datetime64[ns]')
rcr = rcr[(rcr.finish > 0)].copy(); rcr['hn'] = B.clean_name(rcr.horse); rcr['run'] = rcr.meet_code.astype(str) + '|' + rcr.race_no.astype(str) + '|' + rcr.tab_no.astype(str)
sec = pd.concat([pd.read_parquet(f) for f in sorted(glob.glob(os.path.join(G, 'rc_gps_sections_*.parquet')))])
sec['run'] = sec.meet_code.astype(str) + '|' + sec.race_no.astype(str) + '|' + sec.tab_no.astype(str)
sec = sec.sort_values(['run', 'from_m'], ascending=[True, False]); sec['i'] = sec.groupby('run').cumcount()
early = sec[sec.i == 1].set_index('run').pos.rename('pos_early')
rcr = rcr.merge(early, left_on='run', right_index=True, how='left')
rcr['race'] = rcr.meet_code.astype(str) + '|' + rcr.race_no.astype(str)
def sp(z, a):
    t = z[[a, 'finish']].dropna()
    return t[a].corr(t.finish, method='spearman') if len(t) >= 6 else np.nan
rows = []
for k, z in rcr.groupby('race'):
    rows.append((k, z.meet_code.iloc[0], int(z.race_no.iloc[0]), sp(z, 'pos_early'), sp(z, 'rail_avg_m'), sp(z, 'barrier')))
rl2 = pd.DataFrame(rows, columns=['race', 'meet', 'rn', 'lead', 'fence', 'draw']).sort_values(['meet', 'rn'])
gm = rl2.groupby('meet')
for c in ('lead', 'fence', 'draw'):
    rl2[c + '_sofar'] = gm[c].transform(lambda s: s.shift(1).expanding().mean()); 
rl2['n_prev'] = gm.lead.transform(lambda s: s.shift(1).expanding().count()); 
ev = rl2[rl2.n_prev >= 3].copy()
ev['lead_flag'] = ev.lead_sofar >= 0.45; ev['fence_flag'] = ev.fence_sofar >= 0.35
print('\n=== 2. MEETING LEAN LINE (racing.com GPS races, VIC/SA) ===')
print(f'races with 3+ earlier GPS races: {len(ev)}; leaders line would show on {100 * ev.lead_flag.mean():.1f}%, fence line on {100 * ev.fence_flag.mean():.1f}%')
for flag, col, lab in (('lead_flag', 'lead', 'leaders'), ('fence_flag', 'fence', 'fence')):
    a, b = ev[ev[flag]], ev[~ev[flag]]
    se = lambda s: s.std() / np.sqrt(s.count())
    print(f'  {lab:8s} line shown: the race itself then runs lean {a[col].mean():+.3f} (se {se(a[col]):.3f}, n={len(a)}) vs {b[col].mean():+.3f} (se {se(b[col]):.3f}) when not shown; average lean over all races {ev[col].mean():+.3f}')
    print(f'           persistence: corr of the so-far lean with the race\'s own lean {ev[col + "_sofar"].corr(ev[col]):.3f}')
# do the favoured horses beat the Proj on flagged days?  usual early position (settle_h3, low = forward) and barrier fraction as the expected position / lane
rcr_k = rcr.drop_duplicates(['hn', 'date'])[['hn', 'date', 'race']].merge(ev[['race', 'lead_flag', 'fence_flag', 'lead_sofar', 'fence_sofar']], on='race', how='inner')
t = m.merge(rcr_k, on=['hn', 'date'], how='inner')
t['sc'] = t.settle_h3 - t.groupby('rid').settle_h3.transform('mean'); t['bc'] = t.bf - t.groupby('rid').bf.transform('mean')
print('\nslope of the Proj miss on the horse\'s usual early position (negative = forward types beat the Proj more), by whether the leaders line was shown:')
def slope(z, c):
    z = z.dropna(subset=[c, 'miss0']); 
    if len(z) < 50: return 'n/a'
    b = np.polyfit(z[c], z.miss0, 1); r = z.miss0 - np.polyval(b, z[c]); return f'{b[0]:+.2f} (se {np.sqrt(r.var() / (len(z) * z[c].var())):.2f}, n={len(z)})'
for flag in (True, False):
    print(f'  leaders line shown={flag}: {slope(t[t.lead_flag == flag], "sc")}')
print('slope of the Proj miss on barrier position (negative = inside barriers beat the Proj more), by whether the fence line was shown:')
for flag in (True, False):
    print(f'  fence line shown={flag}: {slope(t[t.fence_flag == flag], "bc")}')
