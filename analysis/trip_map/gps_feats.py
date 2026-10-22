"""Run-level GPS, settle-history and contention features keyed by (hn, date), shared by the GPS-in-Proj tests (built from results files, data/gps, contention_feats.parquet)."""
import glob, os, sys
import numpy as np, pandas as pd
sys.path.insert(0, os.path.dirname(__file__))
import build_trip_map as B
ROOT = B.ROOT


def build():
    # ---------------- results side: GPS per run, comments, settle history, contention
    cols = ['race_id', 'horse_id', 'comments_steward', 'comments_video', 'position600m', 'position400m', 'margin600m', 'margin400m', 'positionFinish']
    ex = pd.concat([pd.read_csv(f, usecols=lambda c: c in cols, low_memory=False) for f in sorted(glob.glob(os.path.join(ROOT, 'race_results_20*.csv.gz')))]).drop_duplicates(['race_id', 'horse_id'])
    res = B.add_result_features(B.load_results()).merge(ex.drop(columns=['positionFinish']), on=['race_id', 'horse_id'], how='left')
    res['date'] = pd.to_datetime(res.date).dt.normalize()
    res['gap600'] = res.margin600m.clip(0, 30); res['gap400'] = res.margin400m.clip(0, 30)
    res = res.sort_values(['horse_id', 'date', 'race_id']).reset_index(drop=True)
    gh = res.groupby('horse_id')
    for t in ('settle', 'gap800'):
        res[t + '_h3'] = gh[t].transform(lambda s: s.shift(1).rolling(3, min_periods=1).mean()); res[t + '_h8'] = gh[t].transform(lambda s: s.shift(1).rolling(8, min_periods=2).mean())
    res['prior3'] = gh.wpr.transform(lambda s: s.shift(1).rolling(3, min_periods=2).mean())
    res['rank_prior'] = res.groupby('race_id').prior3.rank(ascending=False, method='first')
    res['half'] = res.rank_prior <= (res.fs / 2).round()
    txt = (res.comments_steward.fillna('') + ' ' + res.comments_video.fillna('')).str.lower()
    FL = {'f_wide': r'\b(?:wide|three wide|four wide|five wide|without cover|exposed|no cover)\b', 'f_blocked': r'(?:held up|blocked|checked|not clear|hampered|bumped|interfer|steadied|crowded|squeezed|shut in)',
          'f_slow': r'(?:slow(?:ly)? away|began awkward|missed the start|fumbled|dwelt|stumbled|reared)', 'f_keen': r'(?:keen|pulled|over ?raced|fought|laid out|laid in|hung)',
          'f_vet': r'(?:vet|lame|bled|bleed|arrhythm|sore|injur|tailed|distress|cardiac)', 'f_soft': r'(?:eased|not persevered|not knocked|dropped out|weak)'}
    for k, p in FL.items(): res[k] = txt.str.contains(p, regex=True).astype(int)
    cf = pd.read_parquet('/tmp/contention_feats.parquet')
    cf = cf.drop_duplicates(['race_id', 'horse_id']); res = res.merge(cf.drop(columns=['date']), on=['race_id', 'horse_id'], how='left')
    v = B.vicsa_runs(res); q = B.qld_runs(res); v['src'] = 0; q['src'] = 1
    gp = pd.concat([v, q], ignore_index=True)[['race_id', 'horse_id', 'src', 'extra', 'lane', 'early']]
    gp['extra_rel'] = gp.extra - gp.groupby('race_id').extra.transform('median'); gp['lane_rel'] = gp.lane - gp.groupby('race_id').lane.transform('median'); gp['early_z'] = gp.early / gp.groupby('src').early.transform('std')
    a = pd.concat([pd.read_parquet(f) for f in glob.glob(os.path.join(ROOT, 'data/gps/atc_gps_runs_*.parquet'))])
    a['date'] = pd.to_datetime(a.race_date); a['hn'] = B.clean_name(a.horse); gg = ['meet_code', 'race_no']
    a['extra_rel'] = a.dist_vs_winner_m - a.groupby(gg).dist_vs_winner_m.transform('median'); e = -(a.first400_s - a.groupby(gg).first400_s.transform('mean')); a['early_z'] = e / e.std()
    a = a[['date', 'hn', 'distance', 'extra_rel', 'early_z']]; a = a[~a.duplicated(['date', 'hn', 'distance'], keep=False)]
    at = res.merge(a, on=['date', 'hn', 'distance'])[['race_id', 'horse_id', 'extra_rel', 'early_z']]; at['src'] = 2
    G = pd.concat([gp[['race_id', 'horse_id', 'src', 'extra_rel', 'lane_rel', 'early_z']], at], ignore_index=True).drop_duplicates(['race_id', 'horse_id'])
    res = res.merge(G, on=['race_id', 'horse_id'], how='left'); res['gps'] = res.src.notna()
    res['pace'] = res.groupby('race_id').early_z.transform(lambda s: s.nlargest(3).mean() if s.notna().sum() >= 4 else np.nan)
    # horse GPS history (strictly earlier GPS runs), over the full res so history is not cut by the Proj window
    res = res.sort_values(['horse_id', 'date', 'race_id']).reset_index(drop=True); gh = res.groupby('horse_id')
    for t in ('extra_rel', 'lane_rel', 'early_z'):
        res[t + '_h3'] = gh[t].transform(lambda s: s.shift(1).rolling(6, min_periods=1).apply(lambda w: np.nanmean(w[-3:]) if np.isfinite(w).any() else np.nan, raw=True))
        res[t + '_h8'] = gh[t].transform(lambda s: s.shift(1).rolling(12, min_periods=2).mean())
    res['n_gps'] = gh.gps.transform(lambda s: s.shift(1).astype(float).fillna(0).cumsum())
    res['burn_h'] = res.early_z_h3 - res.early_z_h8
    res['bar_x_early'] = res.barfrac * res.early_z_h3
    keep = ['hn', 'date', 'race_id', 'half', 'rank_prior', 'gps', 'extra_rel', 'lane_rel', 'early_z', 'pace', 'settle', 'gap800', 'gap600', 'gap400', 'barfrac', 'fs', 'settle_h3', 'gap800_h3', 'prior3',
            'extra_rel_h3', 'extra_rel_h8', 'lane_rel_h3', 'lane_rel_h8', 'early_z_h3', 'early_z_h8', 'n_gps', 'burn_h', 'bar_x_early'] + list(FL) + list(cf.columns.difference(['race_id', 'horse_id', 'date']))
    rr = res[keep].rename(columns={'race_id': 'rid', 'barfrac': 'bf', 'fs': 'fs_res'}).drop_duplicates(['hn', 'date'])
    HIST_ = ['extra_rel_h3', 'extra_rel_h8', 'lane_rel_h3', 'lane_rel_h8', 'early_z_h3', 'early_z_h8', 'n_gps', 'burn_h']
    CONT_ = [c for c in rr.columns if c.startswith('c_')] + ['settle_h3', 'gap800_h3', 'bf', 'bar_x_early']
    return rr, list(FL), HIST_, CONT_
