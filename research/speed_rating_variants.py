"""Can the pre-race speed rating be calculated better? Variants of how a horse's earlier time-based speed figures are turned into one pre-race number.
Test: results-file races 2025-07+ where every runner has a rating for every variant (complete cases). Scores: winner log-lik (softmax, best beta per variant),
top pick win%, winner in top 3, paired gain vs the baseline (mean of last 3 figures, par v1), and the paired gain when the variant is added to L3
(z-scored within race; weight fitted on 2025-07..12, scored on 2026). No market price anywhere.
Variants: par v2 (conditions model), margin cap, mean of last 5, best of 3, median of 5, recency-weighted (ewm), weight adjustment (lengths per kg b, figure
re-based to today's weight), shrink for few runs, and a learned speed-only rating (LightGBM on the figure history + today's weight and distance).
usage: python research/speed_rating_variants.py
"""
import os
import sys

import lightgbm as lgb
import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(__file__))
import speed_figure_study2 as s2  # noqa: E402  (extends sf.USE)
import speed_figure_study as sf  # noqa: E402

SEC = sf.SEC


def figures():
    d = sf.load()
    r = s2.races_table(d)
    r['par1'] = sf.build_par(r)
    r['par2'] = s2.fit_par(r)
    for k in ('par1', 'par2'):
        dev = r.winners_time - r[k]
        v = s2.variant(r, dev, k)
        r['fast_' + k] = -(dev - v) / SEC
    d = d.merge(r[['race_id', 'fast_par1', 'fast_par2']], on='race_id', how='left')
    d['marg'] = d.marginFinish.clip(lower=0, upper=25)
    d['marg12'] = d.marginFinish.clip(lower=0, upper=12)
    d['sp1'] = d.fast_par1 - d.marg
    d['sp2'] = d.fast_par2 - d.marg
    d['sp2c'] = d.fast_par2 - d.marg12
    return d.dropna(subset=['sp2']).sort_values(['horse_id', 'date']).reset_index(drop=True)


def variants(d):
    g = d.groupby('horse_id', sort=False)
    sh = lambda c: g[c].shift(1)
    d['_s1'], d['_s2'], d['_s2c'], d['_w'], d['_wr'] = sh('sp1'), sh('sp2'), sh('sp2c'), sh('weightCarried'), sh('wpr')
    gg = d.groupby('horse_id', sort=False)
    roll = lambda c, n, f: gg[c].transform(lambda s: getattr(s.rolling(n, min_periods=2), f)())
    # the shifted series are already as-of, so a rolling window over them never includes the current run
    d['V0 baseline: mean last 3, par v1'] = roll('_s1', 3, 'mean')
    d['V1 par v2'] = roll('_s2', 3, 'mean')
    d['V2 par v2, margin capped at 12'] = roll('_s2c', 3, 'mean')
    d['V3 mean last 5'] = roll('_s2', 5, 'mean')
    d['V4 best of last 3'] = roll('_s2', 3, 'max')
    d['V5 median of last 5'] = roll('_s2', 5, 'median')
    for h in (1.0, 2.0, 4.0):
        d[f'V6 recency weighted, halflife {h:g} runs'] = gg['_s2'].transform(lambda s, h=h: s.ewm(halflife=h, min_periods=2).mean())
    m3 = d['V1 par v2']
    w3 = roll('_w', 3, 'mean')
    for b in (0.1, 0.2, 0.3, 0.5):
        d[f'V7 weight adjusted, {b} length per kg'] = m3 + b * (w3 - d.weightCarried)
    n = d.groupby('horse_id', sort=False)['_s2'].transform(lambda s: s.rolling(3, min_periods=1).count())
    d['V8 shrunk for few runs (k=1)'] = m3 * n / (n + 1.0)
    d['L3 (mean last 3 wpr)'] = roll('_wr', 3, 'mean')
    d['n_prior'] = n
    d['_l1'], d['_l2'], d['_l3'] = d['_s2'], gg['_s2'].shift(1), gg['_s2'].shift(2)
    d['_l4'], d['_l5'] = gg['_s2'].shift(3), gg['_s2'].shift(4)
    d['m3'], d['w3'] = m3, w3
    d['best3'], d['med5'] = d['V4 best of last 3'], d['V5 median of last 5']
    d['ewm2'] = d['V6 recency weighted, halflife 2 runs']
    d['days'] = (d.date - gg['date'].shift(1)).dt.days
    return d


def ll_by_beta(score, starts, win_idx, betas):
    out = {}
    for b in betas:
        s = b * score
        mx = np.maximum.reduceat(s, starts)
        rep = np.repeat(mx, np.diff(np.append(starts, len(s))))
        e = np.exp(s - rep)
        lse = np.log(np.add.reduceat(e, starts)) + mx
        out[b] = s[win_idx] - lse
    return out


def main():
    d = variants(figures())
    vcols = [c for c in d.columns if c[:2] in ('V0', 'V1', 'V2', 'V3', 'V4', 'V5', 'V6', 'V7', 'V8') or c.startswith('L3')]
    t = d[d.date >= '2025-07-01'].copy()
    t['won'] = (t.positionFinish == 1).astype(int)
    # learned speed-only rating (train before 2025, early stop 2025-01..06), as a LightGBM on the figure history and today's weight
    d['_wrdm'] = d.wpr - d.groupby('race_id').wpr.transform('mean')
    feats = ['_l1', '_l2', '_l3', '_l4', '_l5', 'm3', 'best3', 'med5', 'ewm2', 'n_prior', 'days', 'w3', 'weightCarried', 'distance', 'field_size', 'gnum']
    tr = d[(d.date < '2025-01-01') & d._wrdm.notna() & d.m3.notna()]
    va = d[(d.date >= '2025-01-01') & (d.date < '2025-07-01') & d._wrdm.notna() & d.m3.notna()]
    P = dict(objective='l2', learning_rate=0.05, num_leaves=63, min_data_in_leaf=200, feature_fraction=0.8, bagging_fraction=0.8, bagging_freq=1, lambda_l2=20,
             verbose=-1, num_threads=4)
    mdl = lgb.train(P, lgb.Dataset(tr[feats], tr._wrdm), 3000, valid_sets=[lgb.Dataset(va[feats], va._wrdm)], callbacks=[lgb.early_stopping(50, verbose=False)])
    t['V9 learned speed-only (LightGBM)'] = mdl.predict(t[feats], num_iteration=mdl.best_iteration)
    vcols.append('V9 learned speed-only (LightGBM)')
    ok = t.groupby('race_id').apply(lambda x: x[vcols].notna().all().all() and len(x) >= 5 and x.won.sum() == 1)
    t = t[t.race_id.isin(ok[ok].index)].sort_values(['race_id', 'horse_id']).reset_index(drop=True)
    starts = np.flatnonzero(np.r_[True, t.race_id.values[1:] != t.race_id.values[:-1]])
    win_idx = np.flatnonzero(t.won.values)
    nr = len(starts)
    print('complete-case races', nr, 'runners', len(t), flush=True)
    betas = [0.01, 0.02, 0.03, 0.05, 0.075, 0.1, 0.15, 0.2, 0.3, 0.5]
    z = lambda c: (t[c] - t.groupby('race_id')[c].transform('mean')) / t.groupby('race_id')[c].transform('std').replace(0, np.nan)
    zl3 = z('L3 (mean last 3 wpr)').fillna(0).values
    race_no = np.repeat(np.arange(nr), np.diff(np.append(starts, len(t))))
    half = np.repeat(t.groupby('race_id').date.first().values < np.datetime64('2026-01-01'), np.diff(np.append(starts, len(t))))
    half_r = t.groupby('race_id').date.first().values < np.datetime64('2026-01-01')
    base_ll = None
    rows = []
    for c in vcols:
        sc = t[c].values.astype(float)
        res = ll_by_beta(sc, starts, win_idx, betas)
        bb = max(betas, key=lambda b: res[b].mean())
        ll = res[bb]
        rk = t.groupby('race_id')[c].rank(ascending=False, method='first').values
        wr = rk[win_idx]
        if c.startswith('V0'):
            base_ll = ll
        # added to L3: weight fitted on the first half, scored on the second
        zc = z(c).fillna(0).values
        best_w, best_v = 0.0, -9
        for w in (0.0, 0.1, 0.2, 0.3, 0.5, 0.75, 1.0):
            comb = zl3 + w * zc
            r2 = ll_by_beta(comb, starts, win_idx, [0.5, 1.0, 1.5])
            v = max(r2[k][half_r].mean() for k in r2)
            if v > best_v:
                best_v, best_w = v, w
        comb = zl3 + best_w * zc
        r3 = ll_by_beta(comb, starts, win_idx, [0.5, 1.0, 1.5])
        r0 = ll_by_beta(zl3, starts, win_idx, [0.5, 1.0, 1.5])
        kb = max(r3, key=lambda k: r3[k][half_r].mean())
        diff = (r3[kb] - r0[kb])[~half_r]
        rows.append({'variant': c, 'winner LL alone': ll.mean(), 'top1 wins %': 100 * (wr == 1).mean(), 'winner in top3 %': 100 * (wr <= 3).mean(),
                     'w added to L3': best_w, 'gain over L3 (2026)': diff.mean(), 'se': diff.std() / np.sqrt(len(diff))})
        lastll = ll
    out = pd.DataFrame(rows).set_index('variant')
    pd.set_option('display.width', 220)
    pd.set_option('display.max_colwidth', 50)
    out['paired vs V0'] = np.nan
    # paired LL vs baseline (same beta not enforced; difference of best-beta per-race LL)
    for c in vcols:
        sc = t[c].values.astype(float)
        res = ll_by_beta(sc, starts, win_idx, betas)
        bb = max(betas, key=lambda b: res[b].mean())
        dd = res[bb] - base_ll
        out.loc[c, 'paired vs V0'] = dd.mean()
    print(out.round(4).to_string())


if __name__ == '__main__':
    main()
