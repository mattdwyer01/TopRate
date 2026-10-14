"""A/B in the REAL main model: does the pace-fit block (14 Oct 2026 study, research/pace_fit_study.py) add to the shipped feature set?

Arm A = the shipped features (train_main.ORIGINAL + ladder). Arm B adds, per runner: each horse's rolling slope of its rating residual on the early / late race shape
(last 8 runs, 4 minimum, as-of), the race's predicted early / late shape (from the field's early-speed and late-speed history, distance, going, field size; out-of-fold for
the training years), slope x (predicted shape - average shape), the number of runs behind the slope, and the field pace pressure and the runner's rank in it. Race shapes are
read straight from the results files (the overlay blanks them for the model). Same split and single seed as train_main (train before 2025, early-stop 2025-01..06, score
2025-07 onward). Nothing is written. Run with PROJECTION_RATINGS=toprate to match the live model.
usage: PROJECTION_RATINGS=toprate python projection/pace_fit_ab.py
"""
import glob
import os
import sys

import lightgbm as lgb
import numpy as np
import pandas as pd
from sklearn.model_selection import GroupKFold

sys.path.insert(0, os.path.dirname(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'research'))
import features as F  # noqa: E402
import train_main as T  # noqa: E402
from pace_fit_study import rolling_slope  # noqa: E402

NEW = ['pf_slope_e', 'pf_slope_l', 'pf_n', 'pf_pred_e', 'pf_pred_l', 'pf_fit_e', 'pf_fit_l', 'pf_pressure', 'pf_e_rank', 'pf_l_pressure']


def add_pace_fit(L):
    sh = pd.concat([pd.read_csv(f, usecols=['race_id', 'horse_id', 'raceShapeEarly', 'raceShapeLate'], low_memory=False)
                    for f in sorted(glob.glob(os.path.join(F.ROOT, 'race_results_20*.csv.gz'))) if not f.endswith('_rc.csv.gz')]).drop_duplicates(['race_id', 'horse_id'])
    L = L.merge(sh.rename(columns={'raceShapeEarly': 'sh_e', 'raceShapeLate': 'sh_l'}), on=['race_id', 'horse_id'], how='left')
    L = L.sort_values(['horse_id', 'date', 'race_id']).reset_index(drop=True)
    L['wprd'] = L.wpr - L.groupby('race_id').wpr.transform('mean')
    hexp = L.groupby('horse_id', sort=False).wprd.transform(lambda s: s.shift(1).rolling(5, min_periods=2).mean())
    L['resid'] = L.wprd - hexp
    ok = L.sh_e.notna() & L.resid.notna()
    L['pf_slope_e'], L['pf_n'] = rolling_slope(L.horse_id, L.resid.where(ok), L.sh_e.where(ok))
    ok2 = L.sh_l.notna() & L.resid.notna()
    L['pf_slope_l'], _ = rolling_slope(L.horse_id, L.resid.where(ok2), L.sh_l.where(ok2))
    gr = L.groupby('race_id')
    L['pf_pressure'] = gr['lad_r12_early'].transform('mean')
    L['pf_l_pressure'] = gr['lad_r12_l400'].transform('mean')
    L['pf_e_rank'] = gr['lad_r12_early'].rank(ascending=False, pct=True)
    L['_emax'] = gr['lad_r12_early'].transform('max')
    L['_nf'] = gr['lad_r12_early'].transform(lambda s: (s > s.mean() + 1.0).sum())
    rf = L.groupby('race_id').agg(date=('date', 'first'), dist=('dist', 'first'), fs=('field_size', 'first'), gn=('going_num', 'first'), pp=('pf_pressure', 'first'),
                                  emax=('_emax', 'first'), nf=('_nf', 'first'), lp=('pf_l_pressure', 'first'), she=('sh_e', 'first'), shl=('sh_l', 'first'))
    fe = ['dist', 'fs', 'gn', 'pp', 'emax', 'nf', 'lp']
    PP = dict(objective='l2', learning_rate=0.05, num_leaves=15, min_data_in_leaf=100, verbose=-1, num_threads=4)
    fit_rows = rf[(rf.date < '2025-01-01') & rf.she.notna() & rf.shl.notna()]
    for tgt, name in (('she', 'pf_pred_e'), ('shl', 'pf_pred_l')):
        pred = pd.Series(index=rf.index, dtype=float)
        for a, b in GroupKFold(4).split(fit_rows, groups=fit_rows.index):
            m = lgb.train(PP, lgb.Dataset(fit_rows.iloc[a][fe], fit_rows.iloc[a][tgt]), 300)
            pred.loc[fit_rows.index[b]] = m.predict(fit_rows.iloc[b][fe])
        mall = lgb.train(PP, lgb.Dataset(fit_rows[fe], fit_rows[tgt]), 300)
        rest = rf.index.difference(fit_rows.index)
        pred.loc[rest] = mall.predict(rf.loc[rest, fe].fillna(rf[fe].median()))
        L[name] = L.race_id.map(pred)
    me, ml = L.sh_e.mean(), L.sh_l.mean()
    L['pf_fit_e'] = L.pf_slope_e * (L.pf_pred_e - me)
    L['pf_fit_l'] = L.pf_slope_l * (L.pf_pred_l - ml)
    return L


def winner_ll(te, col, betas=(0.1, 0.15, 0.2, 0.25, 0.3)):
    best = None
    for beta in betas:
        ll, n = 0.0, 0
        for _, g in te.groupby('race_id'):
            w = (g.positionFinish == 1).values
            if w.sum() != 1 or len(g) < 4:
                continue
            s = g[col].values
            q = np.exp(beta * (s - s.max()))
            ll += np.log(q[w][0] / q.sum()); n += 1
        if best is None or ll / n > best[0]:
            best = (ll / n, beta, n)
    return best


def main():
    L = add_pace_fit(T.assemble())
    base = T.ORIGINAL + F.LADDER_FEATURES
    L = L[(L.nruns >= 3) & L[T.BASE].notna().all(axis=1) & L.wpr.notna() & (L.date >= '2018-01-01')].copy()
    tr, va, te = L[L.date < '2025-01-01'], L[(L.date >= '2025-01-01') & (L.date < '2025-07-01')], L[L.date >= '2025-07-01'].copy()
    print('rows', len(L), 'train/valid/test', len(tr), len(va), len(te), 'share with slope', round(float(L.pf_slope_e.notna().mean()), 2), flush=True)
    for name, feats in (('A shipped features', base), ('B + pace-fit block', base + NEW)):
        m, coef = T.fit(tr, feats, None, 1, valid=va)
        te['pred'] = np.c_[np.ones(len(te)), te[T.BASE].values] @ coef + m.predict(te[feats], num_iteration=m.best_iteration)
        err = te.wpr - te.pred
        # within-race demeaned prediction for the winner softmax (a race-wide level shift cannot matter)
        te['pd'] = te.pred - te.groupby('race_id').pred.transform('mean')
        ll = winner_ll(te, 'pd')
        print(f'{name}: RMSE {np.sqrt((err ** 2).mean()):.4f}, winner log-lik {ll[0]:.4f} (beta {ll[1]}, {ll[2]} races), iters {m.best_iteration}', flush=True)
        if feats is not base:
            imp = pd.Series(m.feature_importance('gain'), feats).sort_values(ascending=False)
            print('   gain share of new features:', ', '.join(f'{k} {imp[k] / imp.sum():.2%}' for k in NEW), flush=True)
        te[f'p_{name[0]}'] = te.pred
    d = te.dropna(subset=['p_A', 'p_B']).copy()
    # paired difference in per-race winner log-lik at beta 0.2 for a standard error
    diffs = []
    for _, g in d.groupby('race_id'):
        w = (g.positionFinish == 1).values
        if w.sum() != 1 or len(g) < 4:
            continue
        v = []
        for c in ('p_A', 'p_B'):
            s = g[c].values - g[c].values.mean()
            q = np.exp(0.2 * (s - s.max()))
            v.append(np.log(q[w][0] / q.sum()))
        diffs.append(v[1] - v[0])
    diffs = np.array(diffs)
    print(f'paired gain in winner log-lik (B minus A, beta 0.2): {diffs.mean():+.4f}, standard error {diffs.std() / np.sqrt(len(diffs)):.4f}, races {len(diffs)}', flush=True)


if __name__ == '__main__':
    main()
