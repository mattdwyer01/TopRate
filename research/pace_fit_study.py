"""Pace-fit study (14 Oct 2026): does a horse's own record in fast-early vs slow-early races, combined with the PREDICTED pace of today's race, predict its rating?

Builds on speed_style_study.py (same data, split and metrics). New per-horse, as-of features from its earlier runs:
  resid_j      the run's within-race rating minus the horse's own mean over its previous 5 runs (how much better or worse than usual)
  slope_e/l    rolling (last 8 runs, 4 minimum) regression slope of resid on the race's early / late shape. Positive slope_e = does better when the race is
               run fast early (endurance); negative = does better when it is run slowly (sprint home / needs a soft lead)
  pace_fit_e/l slope x (today's expected shape minus the average shape)
Today's expected shape comes from a model of raceShapeEarly / raceShapeLate on the field's early-speed history, distance and field size (out-of-fold for the
training years). Arms: C (previous best before pace), E (C + slopes + predicted shape + pace_fit), F (same with the REALISED shape: an upper bound).
usage: python research/pace_fit_study.py
"""
import os
import sys

import lightgbm as lgb
import numpy as np
import pandas as pd
from sklearn.model_selection import GroupKFold

sys.path.insert(0, os.path.dirname(__file__))
import speed_style_study as S  # noqa: E402


def rolling_slope(g, resid, shape, window=8, minp=4):
    """Slope of resid on shape over the previous `window` runs of each horse (as-of: shifted by one run)."""
    x, y = shape, resid
    df = pd.DataFrame({'h': g, 'x': x, 'y': y, 'xy': x * y, 'xx': x * x, 'one': 1.0})
    gb = df.groupby('h', sort=False)
    sums = {c: gb[c].transform(lambda s: s.shift(1).rolling(window, min_periods=minp).sum()) for c in ('x', 'y', 'xy', 'xx', 'one')}
    n = sums['one']
    cov = sums['xy'] - sums['x'] * sums['y'] / n
    var = sums['xx'] - sums['x'] ** 2 / n
    slope = cov / var.where(var > 0.5)
    return slope.clip(-3, 3), n


def main():
    d = S.add_history(S.load())
    d['wprd'] = d.wpr - d.groupby('race_id').wpr.transform('mean')
    hexp = d.groupby('horse_id', sort=False).wprd.transform(lambda s: s.shift(1).rolling(5, min_periods=2).mean())
    d['resid'] = d.wprd - hexp
    d['sh_e'] = d.raceShapeEarly
    d['sh_l'] = d.raceShapeLate
    ok = d.sh_e.notna() & d.resid.notna()
    d['slope_e'], d['n_slope'] = rolling_slope(d.horse_id, d.resid.where(ok), d.sh_e.where(ok))
    d['slope_l'], _ = rolling_slope(d.horse_id, d.resid.where(d.sh_l.notna() & d.resid.notna()), d.sh_l.where(d.sh_l.notna() & d.resid.notna()))
    d = d[(d.nprior >= 3) & d.wpr_1.notna() & d.wpr_2.notna() & d.wpr_3.notna()].copy()
    for c in ('wpr', 'wpr_1', 'wpr_2', 'wpr_3', 'wpr_m3', 'wpr_m5', 'days', 'e_1', 'e_2', 'e_3', 'e_m3', 'e_m5', 'l_1', 'l_2', 'l_3', 'l_m3', 'l_m5', 'close_m3', 'sect_i_time_m3', 'sect_i_l200_1'):
        d[c + '_dm'] = d[c] - d.groupby('race_id')[c].transform('mean')
    gr = d.groupby('race_id')
    d['pace_pressure'] = gr['e_m3'].transform('mean')
    d['e_rank'] = gr['e_m3'].rank(ascending=False, pct=True)
    d['l_rank'] = gr['l_m3'].rank(ascending=False, pct=True)
    d['e_max'] = gr['e_m3'].transform('max')
    d['n_front'] = gr['e_m3'].transform(lambda s: (s > 1.0).sum())
    d['l_pressure'] = gr['l_m3'].transform('mean')
    d['n_in_race'] = gr['horse_id'].transform('size')
    # expected shape of the race from field-level predictors, out-of-fold for the training years
    rf = d.groupby('race_id').agg(date=('date', 'first'), dist=('distance', 'first'), fs=('field_size', 'first'), gnum=('gnum', 'first'),
                                  pp=('pace_pressure', 'first'), emax=('e_max', 'first'), nf=('n_front', 'first'), lp=('l_pressure', 'first'),
                                  she=('raceShapeEarly', 'first'), shl=('raceShapeLate', 'first')).dropna(subset=['she', 'shl'])
    fe = ['dist', 'fs', 'gnum', 'pp', 'emax', 'nf', 'lp']
    PP = dict(objective='l2', learning_rate=0.05, num_leaves=15, min_data_in_leaf=100, verbose=-1, num_threads=4)
    trn = rf[rf.date < '2025-01-01']
    for tgt, name in (('she', 'pred_sh_e'), ('shl', 'pred_sh_l')):
        pred = pd.Series(index=rf.index, dtype=float)
        for a, b in GroupKFold(4).split(trn, groups=trn.index):
            m = lgb.train(PP, lgb.Dataset(trn.iloc[a][fe], trn.iloc[a][tgt]), 300)
            pred.loc[trn.index[b]] = m.predict(trn.iloc[b][fe])
        mall = lgb.train(PP, lgb.Dataset(trn[fe], trn[tgt]), 300)
        rest = rf.index.difference(trn.index)
        pred.loc[rest] = mall.predict(rf.loc[rest, fe])
        te_m = rf.loc[rest]
        ok2 = te_m[tgt].notna()
        print(f'{name}: held-out corr with realised shape {np.corrcoef(pred.loc[rest][ok2], te_m[tgt][ok2])[0, 1]:.3f}, sd of shape {te_m[tgt].std():.2f}', flush=True)
        d[name] = d.race_id.map(pred)
    me, ml = d.sh_e.mean(), d.sh_l.mean()
    d['fit_e_pred'] = d.slope_e * (d.pred_sh_e - me)
    d['fit_l_pred'] = d.slope_l * (d.pred_sh_l - ml)
    d['fit_e_real'] = d.slope_e * (d.sh_e - me)
    d['fit_l_real'] = d.slope_l * (d.sh_l - ml)
    for c in ('slope_e', 'slope_l', 'fit_e_pred', 'fit_l_pred', 'fit_e_real', 'fit_l_real'):
        d[c + '_dm'] = d[c] - d.groupby('race_id')[c].transform('mean')
    base_c = ['wpr_1', 'wpr_2', 'wpr_3', 'wpr_m3', 'wpr_m5', 'days']
    style_c = ['e_1', 'e_2', 'e_3', 'e_m3', 'e_m5', 'l_1', 'l_2', 'l_3', 'l_m3', 'l_m5', 'close_m3', 'sect_i_time_m3', 'sect_i_l200_1']
    C = [c + '_dm' for c in base_c + style_c] + ['distance', 'field_size', 'gnum', 'pace_pressure', 'e_rank', 'l_rank']
    arms = {
        'C history + pace pressure (previous best)': C,
        'E + pace-fit slopes, PREDICTED shape': C + ['slope_e_dm', 'slope_l_dm', 'fit_e_pred_dm', 'fit_l_pred_dm', 'n_slope', 'pred_sh_e', 'pred_sh_l'],
        'F + pace-fit slopes, REALISED shape (upper bound)': C + ['slope_e_dm', 'slope_l_dm', 'fit_e_real_dm', 'fit_l_real_dm', 'n_slope', 'sh_e', 'sh_l'],
    }
    tr, va, te = d[d.date < '2025-01-01'], d[(d.date >= '2025-01-01') & (d.date < '2025-07-01')], d[d.date >= '2025-07-01'].copy()
    print('rows', len(d), 'train/valid/test', len(tr), len(va), len(te), 'share with slope', round(float(d.slope_e.notna().mean()), 2), flush=True)
    P = dict(objective='l2', learning_rate=0.05, num_leaves=63, min_data_in_leaf=200, feature_fraction=0.8, bagging_fraction=0.8, bagging_freq=1, lambda_l2=20, verbose=-1, num_threads=4)
    for name, feats in arms.items():
        m = lgb.train(P, lgb.Dataset(tr[feats], tr.wpr_dm), 3000, valid_sets=[lgb.Dataset(va[feats], va.wpr_dm)], callbacks=[lgb.early_stopping(50, verbose=False)])
        te['p'] = m.predict(te[feats], num_iteration=m.best_iteration)
        rmse = np.sqrt(((te.wpr_dm - te.p) ** 2).mean())
        best = None
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
            if best is None or lls / n > best[0]:
                best = (lls / n, beta, n)
        imp = pd.Series(m.feature_importance('gain'), feats).sort_values(ascending=False)
        new = [f for f in feats if f not in C]
        print(f'{name}: RMSE {rmse:.4f}, winner log-lik {best[0]:.4f} (beta {best[1]}, {best[2]} races), iters {m.best_iteration}', flush=True)
        print('   gain share of the new features:', ', '.join(f'{k} {imp[k] / imp.sum():.1%}' for k in new if k in imp.index), flush=True)
    # direct check: do slopes mean anything out of sample? correlation of slope_e with the residual on a high-vs-low shape race
    t2 = te.dropna(subset=['slope_e', 'resid', 'sh_e'])
    hi, lo = t2[t2.sh_e > t2.sh_e.quantile(0.75)], t2[t2.sh_e < t2.sh_e.quantile(0.25)]
    print(f'corr(slope_e, resid): fast-early races {hi.slope_e.corr(hi.resid):.3f}, slow-early races {lo.slope_e.corr(lo.resid):.3f} (n {len(hi)}/{len(lo)})')
    print(f'mean resid by slope_e tercile in fast-early races: ' + str(hi.groupby(pd.qcut(hi.slope_e, 3, labels=["neg", "mid", "pos"]), observed=True).resid.mean().round(2).to_dict()))
    print(f'mean resid by slope_e tercile in slow-early races: ' + str(lo.groupby(pd.qcut(lo.slope_e, 3, labels=["neg", "mid", "pos"]), observed=True).resid.mean().round(2).to_dict()))


if __name__ == '__main__':
    main()
