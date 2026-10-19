"""Track outline geometry (OSM) as rating-prediction features (19 Oct 2026). Per track from research/track_outline_geometry.py: perimeter, longest straight, bend radius,
compactness, elongation, bend share; laps = distance / perimeter. Two uses: (1) the numbers themselves added to baseline B, (2) the horse's own as-of record on
tight / medium / wide bends, short / medium / long straights and small / large circuits (residual of its rating vs its last-5 average, shrunk), which generalises across
tracks the way horse-at-track cannot. Same baseline B, split and scoring as horse_condition_study.py; also scored on the races at tracks with a matched outline.
usage: PYTHONPATH=. python research/track_outline_study.py"""
import os
import sys

import lightgbm as lgb
import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(__file__))
import fourth_rating_study as fr  # noqa: E402
import independent_rating_study as ir  # noqa: E402
import speed_figure_study as sf  # noqa: E402

SHR = 2.0
GEO = os.path.join('data', 'track_outlines', 'track_geometry.json')


def asof_mean(runs, key, name, val='res'):
    """Per horse and condition key: mean of `val` over EARLIER runs with the same key, shrunk to 0 by SHR runs. Vectorised cumulative sums."""
    sid = runs.groupby(['horse_id', key], sort=False).ngroup()
    ok = runs[val].notna().astype(int)
    v0 = runs[val].fillna(0.0)
    cs = v0.groupby(sid).cumsum() - v0
    n = ok.groupby(sid).cumsum() - ok
    runs[name] = (cs / (n + SHR)).where(n > 0)
    runs[name + '_n'] = n


def main():
    trials, runs = fr.load_all()
    runs['wpr_dm'] = runs.wpr - runs.groupby('race_id').wpr.transform('mean')
    runs = ir.asof_entity(runs, 'jockey', 'jk')
    runs = ir.asof_entity(runs, 'trainer', 'tn')
    runs['bfrac'] = (runs.barrier - 1) / (runs.field_size - 1).clip(lower=1)
    runs['tcode'] = runs.track.astype('category').cat.codes
    runs = runs.sort_values(['horse_id', 'date']).reset_index(drop=True)
    g = runs.groupby('horse_id', sort=False)
    runs['nprior'] = g.cumcount()
    runs['days'] = (runs.date - g.date.shift(1)).dt.days
    for k in (1, 2, 3):
        runs[f'wpr_{k}'] = g.wpr.shift(k)
    runs['wpr_m3'] = runs[['wpr_1', 'wpr_2', 'wpr_3']].mean(axis=1)
    runs['wpr_m5'] = g.wpr.transform(lambda s: s.shift(1).rolling(5, min_periods=2).mean())
    runs['res'] = runs.wpr - runs.wpr_m5
    import json
    geo = pd.DataFrame(json.load(open(GEO))).T
    for c, n in (('perim', 'g_perim'), ('straight', 'g_str'), ('bend_radius', 'g_rad'), ('compact', 'g_cmp'), ('elong', 'g_elo'), ('bend_share', 'g_bsh')):
        runs[n] = runs.track.map(pd.to_numeric(geo[c], errors='coerce'))
    runs['g_laps'] = runs.distance / runs.g_perim
    runs['g_turns'] = runs.g_laps * 2
    runs['g_bend_m'] = runs.distance * runs.g_bsh
    for src, nm, k in (('g_rad', 'rc', 3), ('g_str', 'sc', 3), ('g_perim', 'pc', 3)):
        q = geo[{'g_rad': 'bend_radius', 'g_str': 'straight', 'g_perim': 'perim'}[src]].astype(float).quantile([1 / 3, 2 / 3]).values
        runs[nm] = np.where(runs[src].isna(), np.nan, np.digitize(runs[src], q).astype(float))
    runs['have_geo'] = runs.g_perim.notna()
    for key, nm in (('rc', 'h_rc'), ('sc', 'h_sc'), ('pc', 'h_pc')):
        asof_mean(runs, key, nm)
    d = runs[(runs.nprior >= 3) & runs.wpr_1.notna() & runs.wpr_2.notna() & runs.wpr_3.notna()].copy()
    base = ['wpr_1', 'wpr_2', 'wpr_3', 'wpr_m3', 'wpr_m5']
    conn = ['jk', 'jk_n', 'tn', 'tn_n']
    dm = set(base + ['jk', 'tn'])
    for c in dm:
        d[c + '_dm'] = d[c] - d.groupby('race_id')[c].transform('mean')
    d['dist_f'] = d.distance
    d['gnum_f'] = d.gnum
    raw = ['days', 'field_size', 'barrier', 'bfrac', 'dist_f', 'gnum_f', 'tcode']
    cols = lambda l: [c + '_dm' if c in dm else c for c in l]
    fam = {
        'track geometry numbers': ['g_perim', 'g_str', 'g_rad', 'g_cmp', 'g_elo', 'g_bsh', 'g_laps', 'g_turns', 'g_bend_m'],
        'horse at bend tightness': ['h_rc', 'h_rc_n'],
        'horse at straight length': ['h_sc', 'h_sc_n'],
        'horse at circuit size': ['h_pc', 'h_pc_n'],
        'horse at geometry (all three)': ['h_rc', 'h_rc_n', 'h_sc', 'h_sc_n', 'h_pc', 'h_pc_n'],
    }
    trn, va, te = d[d.date < '2025-01-01'], d[(d.date >= '2025-01-01') & (d.date < '2025-07-01')], d[d.date >= '2025-07-01'].copy()
    print('train/valid/test', len(trn), len(va), len(te), 'test with outline', int(te.have_geo.sum()), flush=True)
    P = dict(objective='l2', learning_rate=0.05, num_leaves=63, min_data_in_leaf=200, feature_fraction=0.8, bagging_fraction=0.8, bagging_freq=1, lambda_l2=20, verbose=-1, num_threads=4)

    def fit(feats):
        m = lgb.train(P, lgb.Dataset(trn[feats], trn.wpr_dm), 3000, valid_sets=[lgb.Dataset(va[feats], va.wpr_dm)], callbacks=[lgb.early_stopping(50, verbose=False)])
        return m.predict(te[feats], num_iteration=m.best_iteration)
    rm = lambda c, m=None: np.sqrt(((te.wpr_dm - te[c]) ** 2)[te.have_geo if m else slice(None)].mean())
    te['B'] = fit(cols(base + conn) + raw)
    print(f'B: RMSE {rm("B"):.4f}, winner LL {sf.winner_ll(te, "B")[0]:.4f}', flush=True)
    for nm, l in fam.items():
        te['j'] = fit(cols(base + conn) + raw + l)
        dj = fr.rd(te, 'j', 'B')
        print(f'{nm}: matched-track RMSE {rm("j", 1):.4f} vs B {rm("B", 1):.4f} ({100 * (rm("j", 1) / rm("B", 1) - 1):+.2f}%); all RMSE {rm("j"):.4f} ({100 * (rm("j") / rm("B") - 1):+.2f}%), paired winner LL {dj.mean():+.4f} (se {dj.std() / np.sqrt(len(dj)):.4f}, {len(dj)} races)', flush=True)
    print('done', flush=True)


if __name__ == '__main__':
    main()
