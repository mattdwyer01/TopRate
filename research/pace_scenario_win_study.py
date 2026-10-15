"""Pace study round 2 (14 Oct 2026): three ways to make the pace effect bigger than the 0.004 nats of round 1.

Round 1 asked whether pace helps predict a run's RATING. The ceiling there (perfect pace knowledge) was only +0.005 nats. Pace is mostly a tactical effect on the finish,
so this round models WINNING and PLACING directly (LightGBM binary on the race-demeaned features, probabilities normalised within the race) and adds:
  W0  baseline: the round-1 'C' features (rating history, early/late speed history, field pace pressure)
  W1  + scenario features (idea 1): how many other runners have faster early-speed history, how many of those are drawn inside, lead contest (runners within 1.0 of the
        best early figure), gap to the next fastest, whether the runner is the lone leader, and the field's predicted shape
  W2  + pooled style response (idea 2): the runner's style class (from its last five settled positions) x predicted race shape, valued by the mean residual of that class
        and shape bucket in the TRAINING years (count-shrunk), instead of each horse's own noisy slope
  W3  + better pace predictor (idea 3): the race shape is predicted again with the field's settling profile (expected number of leaders, summed early speed of likely leaders)
        added; W3 uses it in place of the W1/W2 predicted shape. The held-out correlation of both predictors with the real shape is printed.
Same data, split (train before 2025, early-stop 2025-01..06, score 2025-07 onward) and single seed as sim_chances_study.py. Reports winner and place log-likelihood and the
paired gain over W0 with a standard error.
usage: python research/pace_scenario_win_study.py
"""
import os
import sys

import lightgbm as lgb
import numpy as np
import pandas as pd
from sklearn.model_selection import GroupKFold

sys.path.insert(0, os.path.dirname(__file__))
import sim_chances_study as M  # noqa: E402


def add_scenario(d):
    g = d.groupby('race_id', sort=False)
    d['bf'] = (d.barrier - 1) / (d.field_size - 1).clip(lower=1)
    e = d.e_m3.fillna(d.e_m3.median())
    d['_e'] = e
    gm = d.groupby('race_id')['_e']
    d['e_rank_abs'] = gm.rank(ascending=False, method='min')
    d['e_gap_best_other'] = d._e - gm.transform(lambda s: s.nlargest(2).iloc[-1] if len(s) > 1 else s.iloc[0]).where(d._e >= gm.transform('max'), gm.transform('max'))
    d['lone_leader'] = ((d._e >= gm.transform('max')) & ((d._e - d.groupby('race_id')['_e'].transform(lambda s: s.nlargest(2).iloc[-1] if len(s) > 1 else -9)) > 1.0)).astype(float)
    d['lead_contest'] = d.groupby('race_id')['_e'].transform(lambda s: (s >= s.max() - 1.0).sum())
    # faster runners drawn inside me
    n_faster, n_faster_inside = [], []
    for rid, idx in d.groupby('race_id', sort=False).indices.items():
        ee, bb = d._e.values[idx], d.barrier.values[idx]
        nf = (ee[None, :] > ee[:, None]).sum(axis=1)
        nfi = ((ee[None, :] > ee[:, None]) & (bb[None, :] < bb[:, None])).sum(axis=1)
        n_faster.append(pd.Series(nf, index=d.index[idx])); n_faster_inside.append(pd.Series(nfi, index=d.index[idx]))
    d['n_faster'] = pd.concat(n_faster).reindex(d.index)
    d['n_faster_inside'] = pd.concat(n_faster_inside).reindex(d.index)
    return d


def add_style_class(d):
    g = d.groupby('horse_id', sort=False)
    rel = (d.positionSettled / d.field_size).clip(0, 1)
    d['_rel'] = rel
    d['settle5'] = g['_rel'].transform(lambda s: s.shift(1).rolling(5, min_periods=2).mean())
    d['style'] = pd.cut(d.settle5, [-0.01, 0.2, 0.45, 0.7, 1.01], labels=False)
    return d


def pooled_response(d, tr_mask):
    """Mean within-race residual (resid) by style class x predicted-shape bucket, from the training years only, shrunk toward zero by count."""
    t = d[tr_mask & d.style.notna() & d.resid.notna() & d.pred_sh_e.notna()]
    sb = pd.qcut(t.pred_sh_e, 5, labels=False, duplicates='drop')
    edges = np.unique(np.quantile(t.pred_sh_e, np.linspace(0, 1, 6)))
    tab = t.groupby([t.style, sb]).resid.agg(['mean', 'count'])
    tab['val'] = tab['mean'] * tab['count'] / (tab['count'] + 200.0)
    key = lambda df: list(zip(df.style.fillna(-1).astype(int), np.clip(np.searchsorted(edges[1:-1], df.pred_sh_e.fillna(df.pred_sh_e.median())), 0, len(edges) - 2)))
    val = tab['val'].to_dict()
    return lambda df: pd.Series([val.get(k, 0.0) for k in key(df)], index=df.index)


def predict_shape(d, extra=None):
    rf_cols = dict(date=('date', 'first'), dist=('distance', 'first'), fs=('field_size', 'first'), gnum=('gnum', 'first'), pp=('pace_pressure', 'first'),
                   emax=('e_max', 'first'), nf=('n_front', 'first'), lp=('l_pressure', 'first'), she=('raceShapeEarly', 'first'))
    if extra:
        rf_cols.update(extra)
    rf = d.groupby('race_id').agg(**rf_cols).dropna(subset=['she'])
    fe = [c for c in rf.columns if c not in ('date', 'she')]
    PP = dict(objective='l2', learning_rate=0.05, num_leaves=15, min_data_in_leaf=100, verbose=-1, num_threads=4)
    trn = rf[rf.date < '2025-01-01']
    pred = pd.Series(index=rf.index, dtype=float)
    for a, b in GroupKFold(4).split(trn, groups=trn.index):
        m = lgb.train(PP, lgb.Dataset(trn.iloc[a][fe], trn.iloc[a]['she']), 300)
        pred.loc[trn.index[b]] = m.predict(trn.iloc[b][fe])
    mall = lgb.train(PP, lgb.Dataset(trn[fe], trn['she']), 300)
    rest = rf.index.difference(trn.index)
    pred.loc[rest] = mall.predict(rf.loc[rest, fe])
    c = np.corrcoef(pred.loc[rest], rf.loc[rest, 'she'])[0, 1]
    return pred, c


def race_probs(df, col):
    p = df[col].values
    s = pd.Series(p, index=df.index)
    return s / s.groupby(df.race_id).transform('sum')


def main():
    d, me, shape_sd = M.prepare()
    d = add_style_class(add_scenario(d))
    d['win'] = (d.positionFinish == 1).astype(float)
    d['top3'] = ((d.positionFinish <= 3) & (d.positionFinish >= 1)).astype(float)
    # predicted shape 1 (round-1 predictor) is d.pred_sh_e; predictor 2 adds the field's settling profile
    gs = d.groupby('race_id')
    d['n_leaders_est'] = gs['settle5'].transform(lambda s: (s < 0.2).sum())
    d['sum_lead_e'] = gs.apply(lambda g: g._e.where(g.settle5 < 0.3, 0).sum()).reindex(d.race_id).values
    p2, corr2 = predict_shape(d, dict(nl=('n_leaders_est', 'first'), sle=('sum_lead_e', 'first')))
    p1, corr1 = predict_shape(d)
    print(f'predicted early shape: held-out corr with the real shape  round-1 predictor {corr1:.3f}  with settling profile {corr2:.3f}', flush=True)
    d['pred_sh_e2'] = d.race_id.map(p2)
    tr_mask = d.date < '2025-01-01'
    resp = pooled_response(d, tr_mask)
    d['style_resp'] = resp(d)
    base_c = ['wpr_1', 'wpr_2', 'wpr_3', 'wpr_m3', 'wpr_m5', 'days']
    style_c = ['e_1', 'e_2', 'e_3', 'e_m3', 'e_m5', 'l_1', 'l_2', 'l_3', 'l_m3', 'l_m5', 'close_m3', 'sect_i_time_m3', 'sect_i_l200_1']
    C = [c + '_dm' for c in base_c + style_c] + ['distance', 'field_size', 'gnum', 'pace_pressure', 'e_rank', 'l_rank']
    scen = ['n_faster', 'n_faster_inside', 'lead_contest', 'lone_leader', 'e_gap_best_other', 'e_rank_abs', 'bf', 'pred_sh_e']
    arms = {
        'W0 baseline (round-1 C features)': C,
        'W1 + scenario features': C + scen,
        'W2 + pooled style response': C + scen + ['style_resp', 'settle5'],
        'W3 + better pace predictor': C + [s for s in scen if s != 'pred_sh_e'] + ['pred_sh_e2', 'style_resp', 'settle5'],
    }
    tr, va, te = d[d.date < '2025-01-01'], d[(d.date >= '2025-01-01') & (d.date < '2025-07-01')], d[d.date >= '2025-07-01'].copy()
    print('rows', len(d), 'train/valid/test', len(tr), len(va), len(te), flush=True)
    P = dict(objective='binary', learning_rate=0.05, num_leaves=31, min_data_in_leaf=300, feature_fraction=0.8, bagging_fraction=0.8, bagging_freq=1, lambda_l2=30, verbose=-1, num_threads=4)
    res = {}
    for name, feats in arms.items():
        out = {}
        for tgt in ('win', 'top3'):
            m = lgb.train(P, lgb.Dataset(tr[feats], tr[tgt]), 3000, valid_sets=[lgb.Dataset(va[feats], va[tgt])], callbacks=[lgb.early_stopping(60, verbose=False)])
            te['raw'] = m.predict(te[feats], num_iteration=m.best_iteration)
            te['pn'] = race_probs(te, 'raw') if tgt == 'win' else te['raw']
            out[tgt] = (te.pn.copy(), m.best_iteration)
        # per-race winner log-likelihood and place log-loss
        wl, pl = {}, {}
        for rid, g in te.groupby('race_id', sort=False):
            if len(g) < 4 or g.win.sum() != 1:
                continue
            wl[rid] = float(np.log(max(out['win'][0].loc[g.index][g.win == 1].iloc[0], 1e-6)))
            q = out['top3'][0].loc[g.index].clip(1e-4, 1 - 1e-4)
            k = 3 if len(g) >= 8 else 2
            pl[rid] = float(np.mean(np.where(g.top3 == 1, np.log(q), np.log(1 - q)))) if len(g) >= 8 else np.nan
        res[name] = (pd.Series(wl), pd.Series(pl))
        print(f'{name}: winner log-lik {res[name][0].mean():.4f}, place log-loss (8+ runners) {res[name][1].mean():.4f}, iters win {out["win"][1]} place {out["top3"][1]}', flush=True)
    base = list(res)[0]
    for name in list(res)[1:]:
        dw = (res[name][0] - res[base][0]).dropna()
        dp = (res[name][1] - res[base][1]).dropna()
        print(f'  {name} vs W0: winner log-lik {dw.mean():+.4f} (se {dw.std() / np.sqrt(len(dw)):.4f}, {len(dw)} races), place {dp.mean():+.4f} (se {dp.std() / np.sqrt(len(dp)):.4f}, {len(dp)} races)', flush=True)


if __name__ == '__main__':
    main()
