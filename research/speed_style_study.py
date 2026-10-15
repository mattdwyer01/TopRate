"""Speed / pace-style study (14 Oct 2026): does a horse's own early and late speed history, with the pace of the race, add to predicting its rating?

Data: race_results_20*.csv.gz (TopRate era, every runner, 2019 to early Oct 2026): sect_i_* are TopRate's sectional ratings in LENGTHS against its standard for
the race (found 14 Oct 2026: within a race they equal the margin at that point plus a race constant; 1 length ~ 0.147 s), margins at points, race shape and the
winner's time. Everything used for a run's features comes from the horse's EARLIER runs only. Target: the run's own rating (wpr), demeaned within the race so a
race-wide shift cannot help. Train before 2025, early-stop 2025-01..06, score 2025-07 onward.
usage: python research/speed_style_study.py
"""
import glob
import sys

import lightgbm as lgb
import numpy as np
import pandas as pd

USE = ['race_id', 'date', 'horse_id', 'track', 'distance', 'going', 'positionFinish', 'marginFinish', 'wpr', 'field_size', 'weightCarried', 'barrier',
       'sect_i_time', 'sect_i_early', 'sect_i_to600', 'sect_i_l600', 'sect_i_l200', 'sect_i_l400', 'winners_time', 'raceShapeEarly', 'raceShapeMid', 'raceShapeLate',
       'margin600m', 'positionSettled', 'isBarrierTrial', 'race_class']


def load():
    fs = [f for f in sorted(glob.glob('race_results_20*.csv.gz')) if not f.endswith('_rc.csv.gz') and int(f[-11:-7]) >= 2019]
    d = pd.concat([pd.read_csv(f, usecols=lambda c: c in USE, low_memory=False) for f in fs], ignore_index=True)
    d['date'] = pd.to_datetime(d.date)
    d = d[d.isBarrierTrial.fillna(0) == 0] if 'isBarrierTrial' in d else d
    d = d.dropna(subset=['wpr', 'horse_id']).sort_values(['horse_id', 'date']).reset_index(drop=True)
    return d


def add_history(d):
    g = d.groupby('horse_id', sort=False)
    d['gnum'] = d.going.astype(str).str.extract(r'(\d+)').astype(float)
    # within-race demeaned figures so a whole race running fast or slow cancels
    d['e'] = d.sect_i_to600
    d['l'] = d.sect_i_l600
    d['close'] = d.l - d.e
    for c in ('wpr', 'e', 'l', 'close', 'sect_i_time', 'sect_i_l200', 'raceShapeEarly', 'raceShapeLate'):
        for k in (1, 2, 3):
            d[f'{c}_{k}'] = g[c].shift(k)
    for c in ('wpr', 'e', 'l', 'close', 'sect_i_time'):
        d[f'{c}_m3'] = d[[f'{c}_1', f'{c}_2', f'{c}_3']].mean(axis=1)
    d['wpr_m5'] = g.wpr.transform(lambda s: s.shift(1).rolling(5, min_periods=2).mean())
    d['l_m5'] = g.l.transform(lambda s: s.shift(1).rolling(5, min_periods=2).mean())
    d['e_m5'] = g.e.transform(lambda s: s.shift(1).rolling(5, min_periods=2).mean())
    d['nprior'] = g.cumcount()
    d['days'] = (d.date - g.date.shift(1)).dt.days
    # horse's late figure when the earlier race shape was fast vs slow early (as-of)
    return d


def main():
    d = add_history(load())
    d = d[(d.nprior >= 3) & d.wpr_1.notna() & d.wpr_2.notna() & d.wpr_3.notna()].copy()
    # race-demean the target and every numeric feature
    def dm(cols):
        for c in cols:
            d[c + '_dm'] = d[c] - d.groupby('race_id')[c].transform('mean')
    base_c = ['wpr_1', 'wpr_2', 'wpr_3', 'wpr_m3', 'wpr_m5', 'days']
    style_c = ['e_1', 'e_2', 'e_3', 'e_m3', 'e_m5', 'l_1', 'l_2', 'l_3', 'l_m3', 'l_m5', 'close_m3', 'sect_i_time_m3', 'sect_i_l200_1']
    dm(['wpr'] + base_c + style_c)
    # race-level predictors of the pace: field mean of horses' early figures, share of front runners (positive early), realised shape
    d['pace_pressure'] = d.groupby('race_id')['e_m3'].transform('mean')
    d['e_rank'] = d.groupby('race_id')['e_m3'].rank(ascending=False, pct=True)
    d['l_rank'] = d.groupby('race_id')['l_m3'].rank(ascending=False, pct=True)
    ctx = ['distance', 'field_size', 'gnum']
    arms = {
        'A base (prior ratings)': [c + '_dm' for c in base_c] + ctx,
        'B + early/late history': [c + '_dm' for c in base_c + style_c] + ctx,
        'C + history + predicted pace pressure': [c + '_dm' for c in base_c + style_c] + ctx + ['pace_pressure', 'e_rank', 'l_rank'],
        'D + history + REALISED race shape (upper bound)': [c + '_dm' for c in base_c + style_c] + ctx + ['pace_pressure', 'e_rank', 'l_rank', 'raceShapeEarly', 'raceShapeLate'],
    }
    tr, va, te = d[d.date < '2025-01-01'], d[(d.date >= '2025-01-01') & (d.date < '2025-07-01')], d[d.date >= '2025-07-01'].copy()
    print('rows', len(d), 'train/valid/test', len(tr), len(va), len(te), flush=True)
    P = dict(objective='l2', learning_rate=0.05, num_leaves=63, min_data_in_leaf=200, feature_fraction=0.8, bagging_fraction=0.8, bagging_freq=1, lambda_l2=20, verbose=-1, num_threads=4)
    for name, feats in arms.items():
        m = lgb.train(P, lgb.Dataset(tr[feats], tr.wpr_dm), 3000, valid_sets=[lgb.Dataset(va[feats], va.wpr_dm)], callbacks=[lgb.early_stopping(50, verbose=False)])
        p = m.predict(te[feats], num_iteration=m.best_iteration)
        te['p'] = p
        rmse = np.sqrt(((te.wpr_dm - p) ** 2).mean())
        # winner log-likelihood within race (softmax of predicted demeaned rating, beta fitted by grid)
        ll = []
        for beta in (0.1, 0.15, 0.2, 0.25, 0.3):
            lls, n = 0.0, 0
            for _, g in te.groupby('race_id'):
                w = (g.positionFinish == 1).values
                if w.sum() != 1 or len(g) < 4:
                    continue
                s = g.p.values
                q = np.exp(beta * (s - s.max()))
                lls += np.log(q[w][0] / q.sum())
                n += 1
            ll.append((lls / n, beta, n))
        best = max(ll)
        imp = pd.Series(m.feature_importance('gain'), feats).sort_values(ascending=False).head(4)
        print(f'{name}: RMSE {rmse:.4f}, winner log-lik {best[0]:.4f} (beta {best[1]}, {best[2]} races), iters {m.best_iteration}', flush=True)
        print('   top features:', ', '.join(f'{k} {v / imp.sum():.0%}' for k, v in imp.items()), flush=True)


if __name__ == '__main__':
    main()
