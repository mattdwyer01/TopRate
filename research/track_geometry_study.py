"""Track geometry study (19 Oct 2026): does track and course shape knowledge improve RATING prediction (held-out RMSE and winner log-lik, no price)?
No outline data exists in the repo, so geometry is measured from results: per (track, distance) draw slope, early-position (run to the first turn proxy) slope,
front bias, rail metres out, and each horse's as-of residual at the same track. Baseline B = prior ratings + jockey/trainer + barrier, field size, distance, track,
going (what Proj already has), so only genuinely new information counts. Encodings are fitted on runs before 2025 only (shrunk); train before 2025,
early stop 2025-01..06, test 2025-07+. usage: PYTHONPATH=. python research/track_geometry_study.py"""
import os
import sys

import lightgbm as lgb
import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(__file__))
import fourth_rating_study as fr  # noqa: E402
import independent_rating_study as ir  # noqa: E402
import speed_figure_study as sf  # noqa: E402

K = 50.0


def rail_m(s):
    s = s.astype(str)
    n = s.str.extract(r'(\d+)\s*m')[0].astype(float)
    sign = np.where(s.str.contains('Out', case=False), 1.0, 1.0)
    return (n * sign).fillna(0.0).where(s.str.lower() != 'nan', np.nan)


def shrunk_slope(df, key, y, x, name, cut):
    """Per-key slope of y on x (both race-demeaned), fitted on rows before cut, shrunk to 0 by K runs."""
    t = df[df.date < cut]
    g = t.assign(xy=t[x] * t[y], xx=t[x] ** 2).groupby(key)[['xy', 'xx']].sum()
    n = t.groupby(key).size()
    s = (g.xy / (g.xx + K * 0.08)).rename(name)  # 0.08 ~ var of bfrac; ridge toward 0
    return df.merge(s, left_on=key, right_index=True, how='left')


def main():
    trials, runs = fr.load_all()
    runs = runs.merge(pd.read_csv('race_results_2025.csv.gz', usecols=['race_id', 'horse_id', 'rail_position'], low_memory=False).drop_duplicates(['race_id', 'horse_id']),
                      on=['race_id', 'horse_id'], how='left') if False else runs
    import glob
    rp = pd.concat([pd.read_csv(f, usecols=['race_id', 'horse_id', 'rail_position'], low_memory=False) for f in sorted(glob.glob('race_results_20*.csv.gz'))
                    if not f.endswith('_rc.csv.gz') and int(f[-11:-7]) >= 2019], ignore_index=True).drop_duplicates(['race_id', 'horse_id'])
    runs = runs.merge(rp, on=['race_id', 'horse_id'], how='left')
    runs['wpr_dm'] = runs.wpr - runs.groupby('race_id').wpr.transform('mean')
    runs = ir.asof_entity(runs, 'jockey', 'jk')
    runs = ir.asof_entity(runs, 'trainer', 'tn')
    runs['bfrac'] = (runs.barrier - 1) / (runs.field_size - 1).clip(lower=1)
    runs['bf_dm'] = runs.bfrac - 0.5
    runs['m6r'] = (runs.groupby('race_id').margin600m.rank(method='average') - 1) / (runs.field_size - 1).clip(lower=1)
    runs['m6_dm'] = runs.m6r - 0.5
    runs['dbin'] = (runs.distance / 100).round() * 100
    runs['td'] = runs.track.astype(str) + '|' + runs.dbin.astype(int).astype(str)
    runs['rail'] = rail_m(runs.rail_position)
    cut = pd.Timestamp('2025-01-01')
    runs = shrunk_slope(runs, 'td', 'wpr_dm', 'bf_dm', 'td_dslope', cut)      # wide draw costs rating here
    runs = shrunk_slope(runs, 'td', 'm6_dm', 'bf_dm', 'td_eslope', cut)       # wide draw sits further back early (run to first turn proxy)
    runs = shrunk_slope(runs, 'track', 'wpr_dm', 'bf_dm', 'tk_dslope', cut)
    t = runs[runs.date < cut]
    fb = t[t.positionFinish == 1].groupby('td').m6r.agg(['mean', 'size'])
    runs['td_front'] = runs.td.map((fb['mean'] * fb['size'] + 0.5 * K) / (fb['size'] + K)) - 0.5   # winners' early position at the td (front bias)
    runs['draw_cost'] = runs.td_dslope * runs.bf_dm
    runs['early_cost'] = runs.td_eslope * runs.bf_dm
    runs = runs.sort_values(['horse_id', 'date']).reset_index(drop=True)
    g = runs.groupby('horse_id', sort=False)
    runs['nprior'] = g.cumcount()
    runs['days'] = (runs.date - g.date.shift(1)).dt.days
    for k in (1, 2, 3):
        runs[f'wpr_{k}'] = g.wpr.shift(k)
    runs['wpr_m3'] = runs[['wpr_1', 'wpr_2', 'wpr_3']].mean(axis=1)
    runs['wpr_m5'] = g.wpr.transform(lambda s: s.shift(1).rolling(5, min_periods=2).mean())
    runs['m6r_m5'] = g.m6r.transform(lambda s: s.shift(1).rolling(5, min_periods=2).mean())
    runs['style_fit'] = (runs.m6r_m5 - 0.5) * runs.td_front
    # horse as-of residual vs its own recent form at the same track and at the same track|distance
    runs['res'] = runs.wpr - runs.wpr_m5
    for key, nm in (('track', 'h_trk'), ('td', 'h_td')):
        sid = runs.groupby(['horse_id', key], sort=False).ngroup()
        ok = runs.res.notna().astype(int)
        r0 = runs.res.fillna(0.0)
        cs = r0.groupby(sid).cumsum() - r0
        n = ok.groupby(sid).cumsum() - ok
        runs[nm] = (cs / (n + 2)).where(n > 0)
        runs[nm + '_n'] = n
    runs['tcode'] = runs.track.astype('category').cat.codes
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
        'draw/early slopes (td)': ['td_dslope', 'td_eslope', 'tk_dslope', 'draw_cost', 'early_cost'],
        'front bias x style': ['td_front', 'style_fit', 'm6r_m5'],
        'rail': ['rail'],
        'horse at track': ['h_trk', 'h_trk_n', 'h_td', 'h_td_n'],
    }
    trn, va, te = d[d.date < '2025-01-01'], d[(d.date >= '2025-01-01') & (d.date < '2025-07-01')], d[d.date >= '2025-07-01'].copy()
    print('train/valid/test', len(trn), len(va), len(te), flush=True)
    P = dict(objective='l2', learning_rate=0.05, num_leaves=63, min_data_in_leaf=200, feature_fraction=0.8, bagging_fraction=0.8, bagging_freq=1, lambda_l2=20, verbose=-1, num_threads=4)

    def fit(feats):
        m = lgb.train(P, lgb.Dataset(trn[feats], trn.wpr_dm), 3000, valid_sets=[lgb.Dataset(va[feats], va.wpr_dm)], callbacks=[lgb.early_stopping(50, verbose=False)])
        return m.predict(te[feats], num_iteration=m.best_iteration)
    rm = lambda c: np.sqrt(((te.wpr_dm - te[c]) ** 2).mean())
    te['A2'] = fit(cols(base + conn) + ['days', 'field_size'])
    te['B'] = fit(cols(base + conn) + raw)
    print(f'A2 {rm("A2"):.4f}  B (adds barrier, field, distance, track, going) {rm("B"):.4f}, winner LL {sf.winner_ll(te, "B")[0]:.4f}', flush=True)
    for nm, l in fam.items():
        te['j'] = fit(cols(base + conn) + raw + l)
        dj = fr.rd(te, 'j', 'B')
        print(f'{nm}: RMSE {rm("j"):.4f} (B {rm("B"):.4f}, {100 * (rm("j") / rm("B") - 1):+.2f}%), paired winner LL {dj.mean():+.4f} (se {dj.std() / np.sqrt(len(dj)):.4f}, {len(dj)} races)', flush=True)
    allf = sum(fam.values(), [])
    te['j'] = fit(cols(base + conn) + raw + allf)
    dj = fr.rd(te, 'j', 'B')
    print(f'all: RMSE {rm("j"):.4f} ({100 * (rm("j") / rm("B") - 1):+.2f}%), paired winner LL {dj.mean():+.4f} (se {dj.std() / np.sqrt(len(dj)):.4f})', flush=True)


if __name__ == '__main__':
    main()
