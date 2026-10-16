"""Independent rating study (16 Oct 2026): which rating built from the same results data is genuinely DIFFERENT from Proj / Nett / L3, and still predicts winners?

No market price anywhere. Stand-in for the three current ratings = arm A (LightGBM on the horse's prior wpr, i.e. L3 / Proj-like; Nett is not available as history).
Candidate ratings are each a LightGBM trained to predict the run's race-demeaned wpr from ONE family of as-of features only (so each is a rating on the wpr scale):
  closing    : gain on the winner over the last 600m in earlier runs (margin600m vs finish)
  early      : margin behind the leader at 600m in earlier runs (positionSettled is blank in the results files)
  conditions : the horse's own earlier rating at today's distance band / going / track vs its overall average
  connections: jockey and trainer as-of residual rating (their runners' wpr minus the race mean, shrunk, strictly before the day)
Report per candidate: within-race correlation with A, winner log-lik alone, and the paired gain when added to A (weight fitted on 2025-07..12, scored 2026).
Train before 2025, early-stop 2025-01..06, test 2025-07+.
usage: python research/independent_rating_study.py
"""
import os
import sys

import lightgbm as lgb
import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(__file__))
import speed_figure_study as sf  # noqa: E402

sf.USE = sf.USE + ['margin600m', 'positionSettled', 'jockey', 'trainer']


def asof_entity(d, col, name, k=30.0):
    """As-of mean of wpr_dm per entity (jockey/trainer) strictly before the day, shrunk toward 0 with k pseudo-runs."""
    t = d[['date', col, 'wpr_dm']].dropna()
    daily = t.groupby([col, 'date']).wpr_dm.agg(['sum', 'count']).reset_index().sort_values([col, 'date'])
    g = daily.groupby(col)
    daily['cs'] = g['sum'].cumsum() - daily['sum']
    daily['cn'] = g['count'].cumsum() - daily['count']
    daily[name] = daily.cs / (daily.cn + k)
    daily[name + '_n'] = daily.cn
    return d.merge(daily[[col, 'date', name, name + '_n']], on=[col, 'date'], how='left')


def main():
    d = sf.load()
    d = d.dropna(subset=['wpr'])
    d['wpr_dm'] = d.wpr - d.groupby('race_id').wpr.transform('mean')
    d = d.drop_duplicates(['race_id', 'horse_id'])
    w6 = d[d.positionFinish == 1].groupby('race_id').margin600m.first().rename('w6')
    d = d.merge(w6, on='race_id', how='left')
    d['marg'] = d.marginFinish.clip(lower=0, upper=25)
    d['gain'] = ((d.margin600m - d.w6).clip(-25, 25) - d.marg)
    d['gain'] = d.gain - d.groupby('race_id').gain.transform('mean')
    d['m6dm'] = d.margin600m.clip(upper=25) - d.groupby('race_id').margin600m.transform(lambda s: s.clip(upper=25).mean())
    d['dband'] = (d.distance // 200).astype(int)
    d['gcode'] = d.gname.astype('category').cat.codes
    d = asof_entity(d, 'jockey', 'jk')
    d = asof_entity(d, 'trainer', 'tn')
    d = d.sort_values(['horse_id', 'date']).reset_index(drop=True)
    g = d.groupby('horse_id', sort=False)
    d['nprior'] = g.cumcount()
    d['days'] = (d.date - g.date.shift(1)).dt.days
    for c in ('wpr', 'gain', 'm6dm'):
        for k in (1, 2, 3):
            d[f'{c}_{k}'] = g[c].shift(k)
        d[f'{c}_m3'] = d[[f'{c}_1', f'{c}_2', f'{c}_3']].mean(axis=1)
    d['wpr_m5'] = g.wpr.transform(lambda s: s.shift(1).rolling(5, min_periods=2).mean())
    d['gain_m5'] = g.gain.transform(lambda s: s.shift(1).rolling(5, min_periods=2).mean())
    d['m6dm_m5'] = g.m6dm.transform(lambda s: s.shift(1).rolling(5, min_periods=2).mean())
    # conditions: the horse's own as-of mean wpr in the same distance band / going / track, minus its overall as-of mean
    d['hm'] = (g.wpr.cumsum() - d.wpr) / d.nprior.replace(0, np.nan)
    for key, nm in (('dband', 'cd'), ('gcode', 'cg'), ('track', 'ct')):
        gg = d.groupby(['horse_id', key], sort=False)
        n = gg.cumcount()
        mean_k = (gg.wpr.cumsum() - d.wpr) / n.replace(0, np.nan)
        d[nm] = (mean_k - d.hm).where(n > 0)
        d[nm + '_n'] = n
    d = d[(d.nprior >= 3) & d.wpr_1.notna() & d.wpr_2.notna() & d.wpr_3.notna()].copy()
    d = d[d.gain_1.notna() & d.gain_2.notna() & d.gain_3.notna() & d.m6dm_1.notna()]
    print('rows', len(d), flush=True)
    base = ['wpr_1', 'wpr_2', 'wpr_3', 'wpr_m3', 'wpr_m5']
    fam = {
        'closing': ['gain_1', 'gain_2', 'gain_3', 'gain_m3', 'gain_m5'],
        'early': ['m6dm_1', 'm6dm_2', 'm6dm_3', 'm6dm_m3', 'm6dm_m5'],
        'conditions': ['cd', 'cd_n', 'cg', 'cg_n', 'ct', 'ct_n', 'distance', 'gnum', 'hm'],
        'connections': ['jk', 'jk_n', 'tn', 'tn_n'],
    }
    ctx = ['days', 'field_size']
    # race-demean the horse-level inputs
    allc = set(base + sum(fam.values(), [])) - {'distance', 'gnum', 'jk_n', 'tn_n', 'cd_n', 'cg_n', 'ct_n'}
    for c in allc:
        d[c + '_dm'] = d[c] - d.groupby('race_id')[c].transform('mean')
    def cols(l):
        return [c + '_dm' if c in allc else c for c in l] + ctx
    trn, va, te = d[d.date < '2025-01-01'], d[(d.date >= '2025-01-01') & (d.date < '2025-07-01')], d[d.date >= '2025-07-01'].copy()
    print('train/valid/test', len(trn), len(va), len(te), flush=True)
    P = dict(objective='l2', learning_rate=0.05, num_leaves=63, min_data_in_leaf=200, feature_fraction=0.8, bagging_fraction=0.8, bagging_freq=1, lambda_l2=20,
             verbose=-1, num_threads=4)
    def fit(feats):
        m = lgb.train(P, lgb.Dataset(trn[feats], trn.wpr_dm), 3000, valid_sets=[lgb.Dataset(va[feats], va.wpr_dm)], callbacks=[lgb.early_stopping(50, verbose=False)])
        return m.predict(te[feats], num_iteration=m.best_iteration)
    te['A'] = fit(cols(base))
    for nm, l in fam.items():
        te[nm] = fit(cols(l))
    te['A_dm'] = te.A - te.groupby('race_id').A.transform('mean')
    for nm in fam:
        te[nm + '_dm2'] = te[nm] - te.groupby('race_id')[nm].transform('mean')
    rmse = lambda c: np.sqrt(((te.wpr_dm - te[c]) ** 2).mean())
    half = te.date < '2026-01-01'
    out = []
    llA = sf.winner_ll(te, 'A')
    print(f'A (L3 / Proj-like): RMSE {rmse("A"):.4f}, winner log-lik {llA[0]:.4f} ({llA[2]} races)', flush=True)
    for nm in fam:
        corr = te['A_dm'].corr(te[nm + '_dm2'])
        ll = sf.winner_ll(te, nm)
        # blend weight fitted on the first half, scored on the second
        best = (-9, 0)
        for w in (0.0, 0.1, 0.2, 0.3, 0.4, 0.5, 0.75, 1.0):
            te['bl'] = te.A_dm + w * te[nm + '_dm2']
            r = sf.winner_ll(te[half], 'bl')
            if r[0] > best[0]:
                best = (r[0], w)
        te['bl'] = te.A_dm + best[1] * te[nm + '_dm2']
        te['b0'] = te.A_dm
        h2 = ~half
        a2, b2 = sf.winner_ll(te[h2], 'b0'), sf.winner_ll(te[h2], 'bl')
        sub = te[h2]
        d_ = sf_race_diff(sub, 'bl', 'b0')
        print(f'{nm}: within-race corr with A {corr:.3f}, alone RMSE {rmse(nm):.4f}, winner log-lik alone {ll[0]:.4f}; added to A (w={best[1]}): '
              f'second half {a2[0]:.4f} -> {b2[0]:.4f}, paired {d_.mean():+.4f} (se {d_.std() / np.sqrt(len(d_)):.4f}, {len(d_)} races)', flush=True)
    # does a separate connections rating still add once the base model already has jockey and trainer inputs (as the real Proj does)?
    te['A2'] = fit(cols(base + fam['connections']))
    te['A2_dm'] = te.A2 - te.groupby('race_id').A2.transform('mean')
    print(f'A2 (prior ratings + jockey/trainer inputs): RMSE {rmse("A2"):.4f}, winner log-lik {sf.winner_ll(te, "A2")[0]:.4f} (A {llA[0]:.4f})', flush=True)
    te['b2'] = te.A2_dm
    for w in (0.2, 0.4):
        te['bl2'] = te.A2_dm + w * te['connections_dm2']
        d2 = sf_race_diff(te[~half], 'bl2', 'b2')
        print(f'  A2 + {w} x separate connections rating (second half): paired {d2.mean():+.4f} (se {d2.std() / np.sqrt(len(d2)):.4f})', flush=True)
    # everything together
    te['all'] = te.A_dm + sum(0.3 * te[n + '_dm2'] for n in fam)
    print('A + 0.3 x each family:', sf.winner_ll(te[~half], 'all')[0], 'vs A', sf.winner_ll(te[~half], 'b0')[0], flush=True)


def sf_race_diff(df, c1, c0, beta=0.2):
    out = []
    for _, gg in df.groupby('race_id'):
        w = (gg.positionFinish == 1).values
        if w.sum() != 1 or len(gg) < 4:
            continue
        r = []
        for c in (c1, c0):
            s = beta * gg[c].values
            r.append(s[w][0] - s.max() - np.log(np.exp(s - s.max()).sum()))
        out.append(r[0] - r[1])
    return pd.Series(out)


if __name__ == '__main__':
    main()
