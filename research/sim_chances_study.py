"""Simulation vs formula for win / place / quinella chances (14 Oct 2026).

Same data, split and features as pace_fit_study.py (train before 2025, early-stop 2025-01..06, score 2025-07 onward). A rating model gives each runner an expected
within-race rating; four ways of turning ratings into chances are compared on the held-out races:
  S0  softmax of the predicted ratings (beta fitted on the validation half-year)
  S1  simulation: predicted rating + independent normal noise, sd by number of prior runs (fitted on validation residuals)
  S2  S1 but the rating model is the one with the pace-fit features (the 'formula with a feature' route)
  S3  scenario simulation: base rating model WITHOUT pace-fit, each simulated race draws an early shape (predicted shape + noise) and every horse is moved by its own
      slope x (drawn shape - average shape), plus the same independent noise
Scores: winner log-likelihood, place log-loss (3 places for 8+ runners, 2 for 5-7), quinella (first two, either order) log-likelihood with additive smoothing, and
longshot calibration (runners the method gives under 5%: predicted vs actual win rate).
usage: python research/sim_chances_study.py
"""
import os
import sys

import lightgbm as lgb
import numpy as np
import pandas as pd
from sklearn.model_selection import GroupKFold

sys.path.insert(0, os.path.dirname(__file__))
import speed_style_study as S  # noqa: E402
from pace_fit_study import rolling_slope  # noqa: E402

NSIM = 4000
rng = np.random.default_rng(7)


def prepare():
    d = S.add_history(S.load())
    d['wprd'] = d.wpr - d.groupby('race_id').wpr.transform('mean')
    hexp = d.groupby('horse_id', sort=False).wprd.transform(lambda s: s.shift(1).rolling(5, min_periods=2).mean())
    d['resid'] = d.wprd - hexp
    d['sh_e'] = d.raceShapeEarly
    d['sh_l'] = d.raceShapeLate
    ok = d.sh_e.notna() & d.resid.notna()
    d['slope_e'], d['n_slope'] = rolling_slope(d.horse_id, d.resid.where(ok), d.sh_e.where(ok))
    ok2 = d.sh_l.notna() & d.resid.notna()
    d['slope_l'], _ = rolling_slope(d.horse_id, d.resid.where(ok2), d.sh_l.where(ok2))
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
    rf = d.groupby('race_id').agg(date=('date', 'first'), dist=('distance', 'first'), fs=('field_size', 'first'), gnum=('gnum', 'first'), pp=('pace_pressure', 'first'),
                                  emax=('e_max', 'first'), nf=('n_front', 'first'), lp=('l_pressure', 'first'), she=('raceShapeEarly', 'first'), shl=('raceShapeLate', 'first')).dropna(subset=['she', 'shl'])
    fe = ['dist', 'fs', 'gnum', 'pp', 'emax', 'nf', 'lp']
    PP = dict(objective='l2', learning_rate=0.05, num_leaves=15, min_data_in_leaf=100, verbose=-1, num_threads=4)
    trn = rf[rf.date < '2025-01-01']
    pred = pd.Series(index=rf.index, dtype=float)
    for a, b in GroupKFold(4).split(trn, groups=trn.index):
        m = lgb.train(PP, lgb.Dataset(trn.iloc[a][fe], trn.iloc[a]['she']), 300)
        pred.loc[trn.index[b]] = m.predict(trn.iloc[b][fe])
    mall = lgb.train(PP, lgb.Dataset(trn[fe], trn['she']), 300)
    rest = rf.index.difference(trn.index)
    pred.loc[rest] = mall.predict(rf.loc[rest, fe])
    d['pred_sh_e'] = d.race_id.map(pred)
    shape_sd = float((rf.loc[rest, 'she'] - pred.loc[rest]).std())
    me = d.sh_e.mean()
    d['fit_e_pred'] = d.slope_e * (d.pred_sh_e - me)
    d['fit_e_pred_dm'] = d.fit_e_pred - d.groupby('race_id')['fit_e_pred'].transform('mean')
    d['slope_e_dm'] = d.slope_e - d.groupby('race_id')['slope_e'].transform('mean')
    return d, me, shape_sd


def fit(tr, va, feats):
    P = dict(objective='l2', learning_rate=0.05, num_leaves=63, min_data_in_leaf=200, feature_fraction=0.8, bagging_fraction=0.8, bagging_freq=1, lambda_l2=20, verbose=-1, num_threads=4)
    return lgb.train(P, lgb.Dataset(tr[feats], tr.wpr_dm), 3000, valid_sets=[lgb.Dataset(va[feats], va.wpr_dm)], callbacks=[lgb.early_stopping(50, verbose=False)])


def bucket(n):
    return np.where(n < 6, 0, np.where(n < 12, 1, 2))


def places_for(n):
    return 3 if n >= 8 else (2 if n >= 5 else 0)


def score_method(te, draws_fn, name):
    """draws_fn(group_df) -> array (NSIM, n) of simulated ratings. Returns metrics."""
    ll_w = ll_p = ll_q = 0.0
    nw = npl = nq = 0
    lp, lw = [], []
    for _, g in te.groupby('race_id', sort=False):
        n = len(g)
        w = (g.positionFinish == 1).values
        if n < 4 or w.sum() != 1:
            continue
        sim = draws_fn(g)
        order = np.argsort(-sim, axis=1)
        win = np.bincount(order[:, 0], minlength=n) / NSIM
        pw = (win + 1e-4) / (win + 1e-4).sum()
        ll_w += np.log(pw[w][0]); nw += 1
        lp.extend(pw.tolist()); lw.extend(w.astype(float).tolist())
        k = places_for(n)
        pos = g.positionFinish.values
        if k:
            top = order[:, :k]
            pl = np.zeros(n)
            for j in range(k):
                pl += np.bincount(top[:, j], minlength=n)
            pl = np.clip(pl / NSIM, 1e-3, 1 - 1e-3)
            placed = (pos <= k) & (pos >= 1)
            ll_p += np.sum(np.where(placed, np.log(pl), np.log(1 - pl))) / n; npl += 1
        a, b = np.where(pos == 1)[0], np.where(pos == 2)[0]
        if len(a) == 1 and len(b) == 1:
            pair = np.sort(order[:, :2], axis=1)
            key = pair[:, 0] * n + pair[:, 1]
            cnt = np.bincount(key, minlength=n * n)
            x, y = min(a[0], b[0]), max(a[0], b[0])
            npairs = n * (n - 1) / 2
            ll_q += np.log((cnt[x * n + y] + 0.5) / (NSIM + 0.5 * npairs)); nq += 1
    lp, lw = np.array(lp), np.array(lw)
    ls = lp < 0.05
    print(f'{name:<44} win LL {ll_w / nw:.4f}  place LL {ll_p / npl:.4f}  quinella LL {ll_q / nq:.4f}  | longshots <5%: n {ls.sum()}, predicted {lp[ls].mean():.4f} actual {lw[ls].mean():.4f}', flush=True)


def main():
    d, me, shape_sd = prepare()
    base_c = ['wpr_1', 'wpr_2', 'wpr_3', 'wpr_m3', 'wpr_m5', 'days']
    style_c = ['e_1', 'e_2', 'e_3', 'e_m3', 'e_m5', 'l_1', 'l_2', 'l_3', 'l_m3', 'l_m5', 'close_m3', 'sect_i_time_m3', 'sect_i_l200_1']
    C = [c + '_dm' for c in base_c + style_c] + ['distance', 'field_size', 'gnum', 'pace_pressure', 'e_rank', 'l_rank']
    E = C + ['slope_e_dm', 'fit_e_pred_dm', 'n_slope', 'pred_sh_e']
    tr, va, te = d[d.date < '2025-01-01'], d[(d.date >= '2025-01-01') & (d.date < '2025-07-01')], d[d.date >= '2025-07-01'].copy()
    print('rows', len(d), 'train/valid/test', len(tr), len(va), len(te), 'shape sd (resid)', round(shape_sd, 2), flush=True)
    mC, mE = fit(tr, va, C), fit(tr, va, E)
    for m, f, nm in ((mC, C, 'pC'), (mE, E, 'pE')):
        va[nm] = m.predict(va[f], num_iteration=m.best_iteration)
        te[nm] = m.predict(te[f], num_iteration=m.best_iteration)
    sdC = [float((va.wpr_dm - va.pC)[bucket(va.nprior.values) == b].std()) for b in range(3)]
    sdE = [float((va.wpr_dm - va.pE)[bucket(va.nprior.values) == b].std()) for b in range(3)]
    print('noise sd by prior-run bucket (3-5, 6-11, 12+):', [round(x, 2) for x in sdC], '(with pace-fit features:', [round(x, 2) for x in sdE], ')', flush=True)
    # S0 softmax: beta by grid on validation
    best = None
    for beta in (0.08, 0.1, 0.12, 0.15, 0.2, 0.25):
        ll, n = 0.0, 0
        for _, g in va.groupby('race_id'):
            w = (g.positionFinish == 1).values
            if w.sum() != 1 or len(g) < 4:
                continue
            s = g.pC.values
            q = np.exp(beta * (s - s.max()))
            ll += np.log(q[w][0] / q.sum()); n += 1
        if best is None or ll / n > best[0]:
            best = (ll / n, beta)
    beta = best[1]
    print('softmax beta (validation)', beta, flush=True)

    def softmax_draws(g):
        # Gumbel-max sampling = softmax win chances; used so every method is scored through the same simulated-order machinery
        return beta * g.pC.values[None, :] + rng.gumbel(size=(NSIM, len(g)))
    score_method(te, softmax_draws, 'S0 softmax (as Gumbel draws)')

    def indep(col, sds):
        def f(g):
            s = np.array(sds)[bucket(g.nprior.values)]
            return g[col].values[None, :] + rng.normal(size=(NSIM, len(g))) * s[None, :]
        return f
    score_method(te, indep('pC', sdC), 'S1 independent noise by runs (base model)')
    score_method(te, indep('pE', sdE), 'S2 independent noise (pace-fit feature model)')

    def scenario(g):
        s = np.array(sdC)[bucket(g.nprior.values)]
        shape = g.pred_sh_e.values[0] + rng.normal(size=(NSIM, 1)) * shape_sd
        slope = np.nan_to_num(g.slope_e.values)[None, :]
        # the base model already includes the average pace effect at the predicted shape through pace_pressure, so only the drawn deviation is added
        move = slope * (shape - g.pred_sh_e.values[0])
        move = move - move.mean(axis=1, keepdims=True) * 0.0
        return g.pC.values[None, :] + move + rng.normal(size=(NSIM, len(g))) * s[None, :]
    score_method(te, scenario, 'S3 scenario sim (pace draw x horse slope)')


if __name__ == '__main__':
    main()
