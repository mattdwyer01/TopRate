"""Track character from positions, no outlines (19 Oct 2026). For every track and distance band (all courses, from results sectional positions, fitted before 2025):
 hold = slope of finish place on 600m place (high = early position holds: tight or short-straight course), late = mean absolute place change from 400m to the finish
 (high = long straight, much changes late), wide = slope of 600m place on barrier fraction (cost of a wide draw early). Horse style = its own as-of mean early place and
 late gain. Test: do style x course-character fits improve held-out rating prediction over the usual baseline B (prior ratings + jockey/trainer + barrier, field,
 distance, track, going)? Same split as the other studies. usage: PYTHONPATH=. python research/track_character_study.py"""
import os
import sys

import lightgbm as lgb
import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(__file__))
import fourth_rating_study as fr  # noqa: E402
import independent_rating_study as ir  # noqa: E402
import speed_figure_study as sf  # noqa: E402


def slope(df, key, y, x, cut, ridge=0.5):
    t = df[df.date < cut].dropna(subset=[y, x])
    xm = t[x] - t.groupby('race_id')[x].transform('mean')
    ym = t[y] - t.groupby('race_id')[y].transform('mean')
    g = pd.DataFrame({'k': t[key].values, 'xy': (xm * ym).values, 'xx': (xm * xm).values}).groupby('k').sum()
    return df[key].map(g.xy / (g.xx + ridge))


def main():
    trials, runs = fr.load_all()
    runs['wpr_dm'] = runs.wpr - runs.groupby('race_id').wpr.transform('mean')
    runs = ir.asof_entity(runs, 'jockey', 'jk')
    runs = ir.asof_entity(runs, 'trainer', 'tn')
    fs1 = (runs.field_size - 1).clip(lower=1)
    runs['bfrac'] = (runs.barrier - 1) / fs1
    rk = lambda c: (runs.groupby('race_id')[c].rank(method='average') - 1) / fs1
    runs['p600'] = rk('margin600m')
    runs['p400'] = rk('margin400m')
    runs['pfin'] = (runs.positionFinish - 1) / fs1
    runs['late_gain'] = runs.p400 - runs.pfin            # positive = made up places in the last 400m
    runs['dbin'] = (runs.distance / 100).round() * 100
    runs['td'] = runs.track.astype(str) + '|' + runs.dbin.astype(int).astype(str)
    runs['tcode'] = runs.track.astype('category').cat.codes
    cut = pd.Timestamp('2025-01-01')
    runs['td_hold'] = slope(runs, 'td', 'pfin', 'p600', cut)
    runs['td_wide'] = slope(runs, 'td', 'p600', 'bfrac', cut)
    t = runs[runs.date < cut].dropna(subset=['late_gain'])
    la = t.assign(a=t.late_gain.abs()).groupby('td').a.agg(['mean', 'size'])
    runs['td_late'] = runs.td.map((la['mean'] * la['size'] + la['mean'].mean() * 30) / (la['size'] + 30))
    runs = runs.sort_values(['horse_id', 'date']).reset_index(drop=True)
    g = runs.groupby('horse_id', sort=False)
    runs['nprior'] = g.cumcount()
    runs['days'] = (runs.date - g.date.shift(1)).dt.days
    for k in (1, 2, 3):
        runs[f'wpr_{k}'] = g.wpr.shift(k)
    runs['wpr_m3'] = runs[['wpr_1', 'wpr_2', 'wpr_3']].mean(axis=1)
    runs['wpr_m5'] = g.wpr.transform(lambda s: s.shift(1).rolling(5, min_periods=2).mean())
    runs['h_early'] = g.p600.transform(lambda s: s.shift(1).rolling(5, min_periods=2).mean())
    runs['h_late'] = g.late_gain.transform(lambda s: s.shift(1).rolling(5, min_periods=2).mean())
    runs['fit_hold'] = (runs.h_early - 0.5) * runs.td_hold      # front-runner at a course where early position holds
    runs['fit_late'] = runs.h_late * runs.td_late               # closer at a course where places change late
    runs['fit_wide'] = (runs.bfrac - 0.5) * runs.td_wide * (1 - runs.h_early.fillna(0.5))
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
        'course character only (hold, late, wide)': ['td_hold', 'td_late', 'td_wide'],
        'horse style only (early place, late gain)': ['h_early', 'h_late'],
        'style x course fits': ['h_early', 'h_late', 'td_hold', 'td_late', 'td_wide', 'fit_hold', 'fit_late', 'fit_wide'],
    }
    trn, va, te = d[d.date < '2025-01-01'], d[(d.date >= '2025-01-01') & (d.date < '2025-07-01')], d[d.date >= '2025-07-01'].copy()
    print('train/valid/test', len(trn), len(va), len(te), flush=True)
    P = dict(objective='l2', learning_rate=0.05, num_leaves=63, min_data_in_leaf=200, feature_fraction=0.8, bagging_fraction=0.8, bagging_freq=1, lambda_l2=20, verbose=-1, num_threads=4)

    def fit(feats):
        m = lgb.train(P, lgb.Dataset(trn[feats], trn.wpr_dm), 3000, valid_sets=[lgb.Dataset(va[feats], va.wpr_dm)], callbacks=[lgb.early_stopping(50, verbose=False)])
        return m.predict(te[feats], num_iteration=m.best_iteration)
    rm = lambda c: np.sqrt(((te.wpr_dm - te[c]) ** 2).mean())
    te['B'] = fit(cols(base + conn) + raw)
    print(f'B: RMSE {rm("B"):.4f}, winner LL {sf.winner_ll(te, "B")[0]:.4f}', flush=True)
    for nm, l in fam.items():
        te['j'] = fit(cols(base + conn) + raw + l)
        dj = fr.rd(te, 'j', 'B')
        print(f'{nm}: RMSE {rm("j"):.4f} ({100 * (rm("j") / rm("B") - 1):+.2f}%), paired winner LL {dj.mean():+.4f} (se {dj.std() / np.sqrt(len(dj)):.4f}, {len(dj)} races)', flush=True)
    print('done', flush=True)


if __name__ == '__main__':
    main()
