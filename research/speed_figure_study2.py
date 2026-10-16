"""Speed figure study 2 (16 Oct 2026): (1) better par times, (2) closing speed figures. Follows research/speed_figure_study.py (same split and model).

(1) Par: v1 = hierarchical median of winner times (study 1); v2 = LightGBM on winner time per km from track, distance, going, class, grading, field size, season,
    mean weight (conditions only); v3 = v2 plus the race's mean wpr (field quality; circular with ratings, so it measures a rating-flavoured figure).
    Each has a same-day venue variant from the OTHER races. Quality = sd of the race-level residual in lengths on 2025-07+ (out of sample), then the downstream arms.
(2) Closing: gain on the winner over the last 600m = (margin600m - winner's margin600m) - max(marginFinish, 0) in lengths (full coverage, 92%); absolute last-600m figure
    where the winner's last-600m time is known (time_last600m: 1% of runs in 2019 to 40% in 2026): par600 (track, distance, going, fitted before 2025) + variant - time.
usage: python research/speed_figure_study2.py
"""
import os
import sys

import lightgbm as lgb
import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(__file__))
import speed_figure_study as sf  # noqa: E402

SEC = sf.SEC
sf.USE = sf.USE + ['margin600m', 'time_last600m']


def variant(races, resid_s, tag):
    """Shrunk mean of the OTHER races' clipped residual (seconds) at the same venue and day."""
    r = resid_s.clip(-6, 6)
    key = [races.track, races.date]
    n = r.groupby(key).transform('count')
    s = r.groupby(key).transform('sum')
    others = (s - r.fillna(0)) / (n - r.notna().astype(int)).clip(lower=1)
    m = (n - r.notna().astype(int))
    return np.where(m >= 2, others * (m / (m + 2.0)), 0.0)


def races_table(d):
    g = d.groupby('race_id')
    r = g.agg(date=('date', 'first'), track=('track', 'first'), distance=('distance', 'first'), going=('going', 'first'), gname=('gname', 'first'),
              cls=('cls', 'first'), winners_time=('winners_time', 'first'), field_size=('field_size', 'first'), grading=('trackGrading', 'first'),
              gnum=('gnum', 'first'), mw=('weightCarried', 'mean'), mwpr=('wpr', 'mean'), t600=('time_last600m', 'max')).reset_index()
    r['doy'] = r.date.dt.dayofyear
    r['perkm'] = r.winners_time / r.distance * 1000
    return r


def fit_par(r, extra=()):
    feats = ['distance', 'gnum', 'field_size', 'doy', 'mw'] + list(extra)
    cats = ['track', 'gname', 'cls', 'grading']
    X = r[feats + cats].copy()
    for c in cats:
        X[c] = X[c].astype(str).astype('category')
    tr = (r.date < '2025-01-01') & (r.date >= '2020-01-01')
    P = dict(objective='l2', learning_rate=0.05, num_leaves=63, min_data_in_leaf=20, feature_fraction=0.9, lambda_l2=5, cat_smooth=10, verbose=-1, num_threads=4)
    m = lgb.train(P, lgb.Dataset(X[tr], r.perkm[tr]), 500)
    return m.predict(X) * r.distance / 1000


def race_ll(te, col, beta):
    out = {}
    for rid, gg in te.groupby('race_id'):
        w = (gg.positionFinish == 1).values
        if w.sum() != 1 or len(gg) < 4:
            continue
        s = beta * gg[col].values
        out[rid] = s[w][0] - np.log(np.exp(s - s.max()).sum()) - s.max()
    return pd.Series(out)


def market_test(te, preds):
    """Paired winner log-lik gain over arm A with its standard error, and a market-anchored conditional logit (does it add to the starting price?)."""
    from scipy.optimize import minimize
    te = te.copy()
    for nm, p in preds.items():
        te['s_' + nm[0]] = p.values
    base = race_ll(te, 's_A', 0.2)
    for nm in preds:
        if nm[0] == 'A':
            continue
        diff = race_ll(te, 's_' + nm[0], 0.2) - base
        print(f'   paired winner log-lik gain over A, {nm}: {diff.mean():+.4f} (se {diff.std() / np.sqrt(len(diff)):.4f}, {len(diff)} races)', flush=True)
    te = te[te.priceStarting.notna() & (te.priceStarting > 1)].copy()
    te['lm'] = np.log(1 / te.priceStarting)
    te['lm'] = te.lm - np.log(te.groupby('race_id').lm.transform(lambda x: np.exp(x).sum()))
    keep = te.groupby('race_id').size()
    cnt = te.groupby('race_id').positionFinish.apply(lambda x: (x == 1).sum())
    te = te[te.race_id.isin(keep[keep >= 4].index.intersection(cnt[cnt == 1].index))]
    ids = np.sort(te.race_id.unique())
    fit_ids = set(ids[: len(ids) // 2])
    def nll(w, df, cols):
        sc = sum(wi * df[c].values for wi, c in zip(w, cols))
        dfx = pd.DataFrame({'r': df.race_id.values, 's': sc, 'y': (df.positionFinish == 1).values})
        mx = dfx.groupby('r').s.transform('max')
        lse = np.log(np.exp(dfx.s - mx).groupby(dfx.r).sum()) + mx.groupby(dfx.r).first()
        return -(dfx.s[dfx.y].values.sum() - lse.sum()) / dfx.r.nunique()
    fit, ev = te[te.race_id.isin(fit_ids)], te[~te.race_id.isin(fit_ids)]
    for nm in preds:
        cols = ['lm'] + ([] if nm[0] == 'A' and False else ['s_' + nm[0]])
        r = minimize(nll, [1.0, 0.05], args=(fit, cols), method='Nelder-Mead')
        print(f'   market + {nm[:2]}: weights {np.round(r.x, 3)}, held-out half log-lik {-nll(r.x, ev, cols):.4f} (market only {-nll([1.0], ev, ["lm"]):.4f})', flush=True)


def main():
    d = sf.load()
    r = races_table(d)
    r['par1'] = sf.build_par(r)
    r['par2'] = fit_par(r)
    r['par3'] = fit_par(r, ['mwpr'])
    te_r = r.date >= '2025-07-01'
    for k in ('par1', 'par2', 'par3'):
        dev = r.winners_time - r[k]
        v = variant(r, dev, k)
        r[f'fast_{k}'] = -(dev - v) / SEC
        ok = te_r & r[k].notna()
        print(f'{k}: race-level residual sd (lengths) before variant {(dev[ok] / SEC).std():.2f}, after same-day variant {r.loc[ok, "fast_" + k].std():.2f}, races {ok.sum()}', flush=True)
    # closing: gain on the winner over the last 600m, per runner
    d = d.merge(r[['race_id'] + [f'fast_par{i}' for i in (1, 2, 3)]], on='race_id', how='left')
    d['marg'] = d.marginFinish.clip(lower=0, upper=25)
    w6 = d[d.positionFinish == 1].groupby('race_id').margin600m.first().rename('w6')
    d = d.merge(w6, on='race_id', how='left')
    d['gain'] = ((d.margin600m - d.w6).clip(-25, 25) - d.marg)  # lengths gained on the winner in the last 600m (positive = out-finished)
    d.loc[d.w6.isna() | d.margin600m.isna(), 'gain'] = np.nan
    for i in (1, 2, 3):
        d[f'sp{i}'] = d[f'fast_par{i}'] - d.marg
    # absolute last-600m figure where the winner's last-600m time is known
    tr = r[(r.date < '2025-01-01') & r.t600.notna()]
    par6 = pd.Series(np.nan, index=r.index)
    for k in (['track', 'distance', 'gname'], ['track', 'distance'], ['distance']):
        g = tr.groupby(k).t600.agg(['median', 'size']).reset_index()
        g = g[g['size'] >= 8].rename(columns={'median': '_p'})
        par6 = par6.fillna(pd.Series(r[k].merge(g[k + ['_p']], on=k, how='left')['_p'].values, index=r.index))
    dev6 = (r.t600 - par6)
    r['fast600'] = -(dev6 - pd.Series(variant(r, dev6, 'c'), index=r.index)) / SEC
    print('last-600m par: races with winner t600', int(r.t600.notna().sum()), 'residual sd (lengths) test', round((dev6[te_r] / SEC).std(), 2),
          '(raw t600 sd', round((r.t600[te_r] / SEC).std(), 2), ')', flush=True)
    d = d.merge(r[['race_id', 'fast600']], on='race_id', how='left')
    d['abs_close'] = d.fast600 + d.gain  # lengths faster than par over the last 600m
    d['close_dm'] = d.gain - d.groupby('race_id').gain.transform('mean')
    d = d.sort_values(['horse_id', 'date']).reset_index(drop=True)
    g = d.groupby('horse_id', sort=False)
    for c in ('wpr', 'sp1', 'sp2', 'sp3', 'gain', 'close_dm', 'abs_close', 'fast_par2'):
        for k in (1, 2, 3):
            d[f'{c}_{k}'] = g[c].shift(k)
        d[f'{c}_m3'] = d[[f'{c}_1', f'{c}_2', f'{c}_3']].mean(axis=1)
    d['wpr_m5'] = g.wpr.transform(lambda s: s.shift(1).rolling(5, min_periods=2).mean())
    d['gain_m5'] = g.gain.transform(lambda s: s.shift(1).rolling(5, min_periods=2).mean())
    d['sp2_m5'] = g.sp2.transform(lambda s: s.shift(1).rolling(5, min_periods=2).mean())
    d['sp3_m5'] = g.sp3.transform(lambda s: s.shift(1).rolling(5, min_periods=2).mean())
    d['sp1_m5'] = g.sp1.transform(lambda s: s.shift(1).rolling(5, min_periods=2).mean())
    d['abs_close_best'] = d[['abs_close_1', 'abs_close_2', 'abs_close_3']].max(axis=1)
    d['abs_close_n'] = d[['abs_close_1', 'abs_close_2', 'abs_close_3']].notna().sum(axis=1)
    d['nprior'] = g.cumcount()
    d['days'] = (d.date - g.date.shift(1)).dt.days
    d = d[(d.nprior >= 3) & d.wpr_1.notna() & d.wpr_2.notna() & d.wpr_3.notna() & d.wpr.notna() & d.sp2_1.notna() & d.sp2_2.notna() & d.sp2_3.notna()
          & d.gain_1.notna() & d.gain_2.notna() & d.gain_3.notna()].copy()
    print('closing gain (full coverage) vs race-demeaned: corr(gain_m3, wpr_m3) =', round(d.gain_m3.corr(d.wpr_m3), 3), '; abs_close coverage in test rows',
          round((d[d.date >= '2025-07-01'].abs_close_n > 0).mean(), 3), flush=True)
    base = ['wpr_1', 'wpr_2', 'wpr_3', 'wpr_m3', 'wpr_m5', 'days']
    sp1 = ['sp1_1', 'sp1_2', 'sp1_3', 'sp1_m3', 'sp1_m5']
    sp2 = ['sp2_1', 'sp2_2', 'sp2_3', 'sp2_m3', 'sp2_m5']
    sp3 = ['sp3_1', 'sp3_2', 'sp3_3', 'sp3_m3', 'sp3_m5']
    cl = ['close_dm_1', 'close_dm_2', 'close_dm_3', 'close_dm_m3', 'gain_m5']
    ab = ['abs_close_1', 'abs_close_2', 'abs_close_3', 'abs_close_m3', 'abs_close_best', 'abs_close_n']
    allc = base + sp1 + sp2 + sp3 + cl + ab
    for c in set(allc + ['wpr']):
        if c in ('abs_close_n',):
            d[c + '_dm'] = d[c]
        else:
            d[c + '_dm'] = d[c] - d.groupby('race_id')[c].transform('mean')
    ctx = ['distance', 'field_size', 'gnum']
    f = lambda cols: [c + '_dm' for c in cols] + ctx
    arms = {
        'A prior ratings only': f(base),
        'B1 + speed, par v1 (study 1)': f(base + sp1),
        'B2 + speed, par v2 (conditions model)': f(base + sp2),
        'B3 + speed, par v3 (plus field quality)': f(base + sp3),
        'C1 + margin closing gain (92% coverage)': f(base + cl),
        'C2 + closing gain + absolute last-600 figure': f(base + cl + ab),
        'D speed v2 + closing gain': f(base + sp2 + cl),
        'E closing gain only (no ratings)': f(['days'] + cl),
    }
    trn, va, te = d[d.date < '2025-01-01'], d[(d.date >= '2025-01-01') & (d.date < '2025-07-01')], d[d.date >= '2025-07-01'].copy()
    print('train/valid/test', len(trn), len(va), len(te), flush=True)
    P = dict(objective='l2', learning_rate=0.05, num_leaves=63, min_data_in_leaf=200, feature_fraction=0.8, bagging_fraction=0.8, bagging_freq=1, lambda_l2=20,
             verbose=-1, num_threads=4)
    preds = {}
    if os.environ.get('ARMS'):
        arms = {k: v for k, v in arms.items() if k[0] in os.environ['ARMS']}
    for name, feats in arms.items():
        m = lgb.train(P, lgb.Dataset(trn[feats], trn.wpr_dm), 3000, valid_sets=[lgb.Dataset(va[feats], va.wpr_dm)], callbacks=[lgb.early_stopping(50, verbose=False)])
        te['p'] = m.predict(te[feats], num_iteration=m.best_iteration)
        preds[name] = te.p.copy()
        rmse = np.sqrt(((te.wpr_dm - te.p) ** 2).mean())
        ll = sf.winner_ll(te, 'p')
        print(f'{name}: RMSE {rmse:.4f}, winner log-lik {ll[0]:.4f} (beta {ll[1]}, {ll[2]} races)', flush=True)
    a = preds['A prior ratings only']
    market_test(te, preds)
    resid = te.wpr_dm - a
    for name in list(arms)[1:]:
        diff = preds[name] - a
        print(f'   {name}: slope of A residual on (arm - A) {np.polyfit(diff, resid, 1)[0]:.2f}, corr(A, arm) {np.corrcoef(a, preds[name])[0, 1]:.4f}')
    # subset where an absolute closing figure exists for at least one earlier run
    sub = te.abs_close_n > 0
    for nm in ('C1 + margin closing gain (92% coverage)', 'C2 + closing gain + absolute last-600 figure'):
        e = np.sqrt(((te.wpr_dm - preds[nm])[sub] ** 2).mean())
        print(f'   subset with absolute last-600 figure ({sub.sum()} runs): {nm} RMSE {e:.4f} vs A {np.sqrt((resid[sub] ** 2).mean()):.4f}', flush=True)


if __name__ == '__main__':
    main()
