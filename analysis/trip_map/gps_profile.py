"""Rich GPS profile features (23 Oct 2026). Beyond the coarse whole-run numbers (ground lost, average lane, early speed): the per-200m sectional data of all four GPS sources
(racing.com, Racing Queensland, ATC, plus none for HK) turned into a running profile per run, then into the horse's history as of each race, and the race's pace set-up from the
whole field's histories. Per run (speed and position z-scored inside the race): early speed, mid-race speed (800m to 400m to go), finishing speed (last 400m), kick = finish minus mid,
fade = mid minus early, peak speed, position at 800 / 400 / 0 to go as a share of the field, positions gained from 800m and from 400m to the line, lane at 800m and 400m to go and its
drift (Queensland), stride rate and length late (Queensland). Horse history = mean of the last 3 and last 8 GPS runs strictly before the race. Race set-up = rivals' histories: how many
rivals have faster early speed, the fastest rival's early speed, own gap to it, how many have a stronger kick, the field's mean early speed and spread (pace pressure).
Writes /tmp/gps_profile_feats.parquet keyed (hn, date). Run: PYTHONPATH=. python analysis/trip_map/gps_profile.py"""
import glob, os, sys
import numpy as np, pandas as pd
sys.path.insert(0, os.path.dirname(__file__))
import build_trip_map as B
ROOT = B.ROOT; G = os.path.join(ROOT, 'data', 'gps')
def rd(pat): return pd.concat([pd.read_parquet(f) for f in sorted(glob.glob(os.path.join(G, pat)))], ignore_index=True)

# ---------------- unified section table
rcr = rd('rc_gps_runs_*.parquet')[['meet_code', 'race_no', 'start_utc', 'horse', 'tab_no', 'speed_peak_ms', 'finish']]
rcr['date'] = pd.to_datetime(rcr.start_utc).dt.tz_convert('Australia/Melbourne').dt.tz_localize(None).dt.normalize()
rcs = rd('rc_gps_sections_*.parquet')
rcs = rcs.merge(rcr[['meet_code', 'race_no', 'tab_no', 'date', 'speed_peak_ms']].drop_duplicates(['meet_code', 'race_no', 'tab_no']), on=['meet_code', 'race_no', 'tab_no'], how='inner')
U1 = pd.DataFrame({'src': 'rc', 'key': 'rc' + rcs.meet_code.astype(str) + '_' + rcs.race_no.astype(str), 'tab': rcs.tab_no.astype(str), 'horse': rcs.horse, 'date': rcs.date,
                   'start_togo': rcs.from_m.astype(float), 'end_togo': rcs.to_m.astype(float), 'speed': rcs.avg_speed_ms.astype(float), 'pos': rcs.pos.astype(float), 'rail': np.nan, 'hz': np.nan, 'stm': np.nan, 'peak': rcs.speed_peak_ms.astype(float)})
rqs = rd('rq_gps_sections_*.parquet')
for c in ('tab_no', 'cum_dist_m', 'real_dist_m', 'rank', 'avg_speed_ms', 'top_speed_ms', 'stride_hz', 'stride_m', 'rail_m'): rqs[c] = pd.to_numeric(rqs[c], errors='coerce')
rqs['last_cum'] = rqs.groupby('race_code').cum_dist_m.transform('max')
U2 = pd.DataFrame({'src': 'rq', 'key': 'rq' + rqs.race_code.astype(str), 'tab': rqs.tab_no.astype(int).astype(str), 'horse': rqs.horse, 'date': pd.to_datetime(rqs.race_date),
                   'start_togo': rqs.last_cum - rqs.cum_dist_m + rqs.real_dist_m, 'end_togo': rqs.last_cum - rqs.cum_dist_m, 'speed': rqs.avg_speed_ms, 'pos': rqs['rank'], 'rail': rqs.rail_m, 'hz': rqs.stride_hz, 'stm': rqs.stride_m, 'peak': rqs.top_speed_ms})
ats = rd('atc_gps_sections_*.parquet')
ats = ats[(ats.speed_kmh >= 30) & (ats.speed_kmh <= 80)]
U3 = pd.DataFrame({'src': 'atc', 'key': 'atc' + ats.meet_code.astype(str) + '_' + ats.race_no.astype(str), 'tab': ats.tab_no.astype(str), 'horse': ats.horse, 'date': pd.to_datetime(ats.race_date),
                   'start_togo': ats.to_go_m.astype(float), 'end_togo': ats.to_go_m.astype(float) - (ats.to_m - ats.from_m).astype(float), 'speed': ats.speed_kmh / 3.6, 'pos': ats.pos.astype(float), 'rail': np.nan, 'hz': np.nan, 'stm': np.nan, 'peak': np.nan})
U = pd.concat([U1, U2, U3], ignore_index=True)
U = U[(U.speed > 8) & (U.speed < 24)].copy()
U['hn'] = B.clean_name(U.horse); U['run'] = U.key + '|' + U.tab
print('sections', len(U), 'runs', U.run.nunique(), flush=True)
U['bin'] = (np.round(U.end_togo / 200) * 200).where((U.end_togo - np.round(U.end_togo / 200) * 200).abs() <= 60)
mx = U.groupby('key').start_togo.transform('max')
U['early'] = U.start_togo >= mx - 400
def piv(col, sel, name_fmt):
    t = U[sel & U.bin.isin([0, 200, 400, 600, 800])].pivot_table(index='run', columns='bin', values=col, aggfunc='first')
    t.columns = [name_fmt % int(c) for c in t.columns]; return t
P = piv('speed', U.bin.notna(), 'spd_s%d').join(piv('pos', U.bin.notna(), 'pos_s%d'), how='outer')
P = P.join(piv('rail', U.bin.notna(), 'rail_s%d'), how='outer').join(piv('hz', U.bin.notna(), 'hz_s%d'), how='outer').join(piv('stm', U.bin.notna(), 'stm_s%d'), how='outer')
P['early_spd'] = U[U.early].groupby('run').speed.mean()
P['peak'] = U.groupby('run').peak.max()
meta = U.groupby('run').agg(src=('src', 'first'), key=('key', 'first'), hn=('hn', 'first'), date=('date', 'first'))
P = meta.join(P)
for c in ('spd_s0', 'spd_s200', 'spd_s400', 'spd_s600', 'spd_s800', 'pos_s0', 'pos_s400', 'pos_s800', 'rail_s400', 'rail_s800', 'hz_s0', 'hz_s200', 'stm_s0', 'stm_s200'):
    if c not in P.columns: P[c] = np.nan
# z-scores inside the race
gk = P.groupby('key')
nrun = gk.hn.transform('size')
def z(c): return (P[c] - gk[c].transform('mean')) / gk[c].transform('std').replace(0, np.nan)
P['z_early'] = z('early_spd'); P['z_s800'] = z('spd_s800'); P['z_s600'] = z('spd_s600'); P['z_s400'] = z('spd_s400'); P['z_s200'] = z('spd_s200'); P['z_s0'] = z('spd_s0'); P['z_peak'] = z('peak')
P['z_mid'] = P[['z_s800', 'z_s600']].mean(axis=1); P['z_fin'] = P[['z_s200', 'z_s0']].mean(axis=1)
P['kick'] = P.z_fin - P.z_mid; P['fade'] = P.z_mid - P.z_early; P['late_vs_early'] = P.z_fin - P.z_early
for p in ('pos_s800', 'pos_s400', 'pos_s0'):
    P[p + '_pct'] = (P[p] - 1) / (gk[p].transform('count') - 1).replace(0, np.nan)
P['gain800'] = P.pos_s800_pct - P.pos_s0_pct; P['gain400'] = P.pos_s400_pct - P.pos_s0_pct
for c in ('rail_s800', 'rail_s400'): P['lane_' + c[5:]] = P[c] - gk[c].transform('median')
P['lane_drift'] = P.lane_s400 - P.lane_s800
P['hz_late'] = z('hz_s0'); P['stm_late'] = z('stm_s0')
PROF = ['z_early', 'z_mid', 'z_fin', 'kick', 'fade', 'late_vs_early', 'z_peak', 'pos_s800_pct', 'pos_s400_pct', 'gain800', 'gain400', 'lane_s800', 'lane_s400', 'lane_drift', 'hz_late', 'stm_late']
P = P[P.groupby('key').hn.transform('size') >= 6]
P = P.drop_duplicates(['hn', 'date'], keep='last').reset_index(drop=True)
print('runs with a profile', len(P), '| coverage of each metric:', {c: round(float(P[c].notna().mean()), 2) for c in PROF}, flush=True)

# ---------------- horse history as of each GPS run (strictly earlier GPS runs) and as of any later date
P = P.sort_values(['hn', 'date']).reset_index(drop=True)
g = P.groupby('hn')
H = P[['hn', 'date']].copy()
for c in PROF:
    H['pf3_' + c] = g[c].transform(lambda s: s.rolling(3, min_periods=1).mean())
    H['pf8_' + c] = g[c].transform(lambda s: s.rolling(8, min_periods=2).mean())
H['pf_n'] = g.cumcount() + 1
# value known AFTER this run, so a later race sees it; merge_asof with exact matches excluded gives the history strictly before the race
H = H.rename(columns={'date': 'hdate'}).sort_values('hdate')
out = {'H': H, 'PROF': PROF}
H.to_parquet('/tmp/gps_profile_hist.parquet'); P[['hn', 'date', 'key', 'src'] + PROF].to_parquet('/tmp/gps_profile_runs.parquet')
print('history rows', len(H), flush=True)
