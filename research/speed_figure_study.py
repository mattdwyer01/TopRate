"""Raw speed figure study (16 Oct 2026): does a TIME-based speed figure add an angle beyond the margin-based ratings (L3 ~ wpr_m3, Proj ~ model on prior wpr)?

Figure (per run): finish time t = winners_time + 0.147 x max(marginFinish, 0) (winner's own marginFinish is NEGATIVE = winning margin, so it is clipped to 0),
minus a par time for the track, distance, class and going, minus a same-day track variant (median of the OTHER races that day at the venue), in lengths
(0.147 s each); positive = faster than par. Par is fitted on races before 2025 only, so the 2025-07+ test is out of sample.
Note: inside one race the figure is the winner's figure minus the margin, so the ONLY information beyond margins is the race level (winner time vs par+variant).

usage: python research/speed_figure_study.py
"""
import glob

import lightgbm as lgb
import numpy as np
import pandas as pd

SEC = 0.147
USE = ['race_id', 'date', 'horse_id', 'track', 'distance', 'going', 'positionFinish', 'marginFinish', 'wpr', 'field_size', 'weightCarried', 'winners_time',
       'isBarrierTrial', 'race_class', 'priceStarting', 'trackGrading']


def load():
    fs = [f for f in sorted(glob.glob('race_results_20*.csv.gz')) if not f.endswith('_rc.csv.gz') and int(f[-11:-7]) >= 2019]
    d = pd.concat([pd.read_csv(f, usecols=lambda c: c in USE, low_memory=False) for f in fs], ignore_index=True)
    d['date'] = pd.to_datetime(d.date)
    d = d[d.isBarrierTrial.fillna(False).astype(bool) == False]
    d = d[~d.race_class.astype(str).str.contains('HUR|STE|JUMP', case=False, na=False)]
    d = d.dropna(subset=['horse_id', 'winners_time', 'marginFinish', 'distance'])
    d = d[(d.winners_time > 20) & (d.winners_time < 400)].drop_duplicates(['race_id', 'horse_id'])
    d['gnum'] = d.going.astype(str).str.extract(r'(\d+)').astype(float)
    d['gname'] = d.going.astype(str).str.extract(r'([A-Za-z]+)')[0]
    d['cls'] = d.race_class.astype(str).str.replace(r'\d+', '', regex=True)  # OPEN, MAI, BM, CLS, RST ...
    return d


def build_par(races):
    """Hierarchical median winner time. Fitted on pre-2025 races only."""
    tr = races[races.date < '2025-01-01']
    keys = [['track', 'distance', 'cls', 'going'], ['track', 'distance', 'going'], ['track', 'distance', 'gname'], ['track', 'distance'], ['distance']]
    minn = [12, 12, 15, 15, 20]
    par = pd.Series(np.nan, index=races.index)
    for k, mn in zip(keys, minn):
        g = tr.groupby(k).winners_time.agg(['median', 'size']).reset_index()
        g = g[g['size'] >= mn].rename(columns={'median': '_p'})
        m = races[k].merge(g[k + ['_p']], on=k, how='left')['_p'].values
        par = par.fillna(pd.Series(m, index=races.index))
    return par


def add_figure(d):
    races = d.drop_duplicates('race_id')[['race_id', 'date', 'track', 'distance', 'going', 'gname', 'cls', 'winners_time']].copy().reset_index(drop=True)
    races['par'] = build_par(races)
    races['dev'] = races.winners_time - races.par  # seconds slower than par (positive = slow)
    # same-day venue variant from the OTHER races, shrunk
    g = races.groupby(['track', 'date']).dev
    s, n = g.transform('sum'), g.transform('count')
    # median of others is costly, use trimmed mean of others: (sum - own) / (n - 1) on dev clipped
    races['devc'] = races.dev.clip(-6, 6)
    s = races.groupby(['track', 'date']).devc.transform('sum')
    others = (s - races.devc) / (n - 1).clip(lower=1)
    k = (n - 1) / (n - 1 + 2.0)
    races['variant'] = np.where(n >= 3, others * k, 0.0)
    races['fast_len'] = -(races.dev - races.variant) / SEC  # race level: winner lengths faster than par+variant
    races['has_par'] = races.par.notna()
    d = d.merge(races[['race_id', 'par', 'variant', 'fast_len', 'has_par']], on='race_id', how='left')
    d['marg'] = d.marginFinish.clip(lower=0, upper=25)
    d['sp'] = d.fast_len - d.marg  # lengths faster than par for this runner
    d.loc[~d.has_par, 'sp'] = np.nan
    return d.sort_values(['horse_id', 'date']).reset_index(drop=True)


def add_history(d):
    g = d.groupby('horse_id', sort=False)
    for c in ('wpr', 'sp', 'fast_len'):
        for k in (1, 2, 3):
            d[f'{c}_{k}'] = g[c].shift(k)
        d[f'{c}_m3'] = d[[f'{c}_1', f'{c}_2', f'{c}_3']].mean(axis=1)
    d['wpr_m5'] = g.wpr.transform(lambda s: s.shift(1).rolling(5, min_periods=2).mean())
    d['sp_m5'] = g.sp.transform(lambda s: s.shift(1).rolling(5, min_periods=2).mean())
    d['sp_best3'] = d[['sp_1', 'sp_2', 'sp_3']].max(axis=1)
    d['nprior'] = g.cumcount()
    d['days'] = (d.date - g.date.shift(1)).dt.days
    return d


def winner_ll(te, col):
    best = None
    for beta in (0.1, 0.15, 0.2, 0.25, 0.3):
        lls, n = 0.0, 0
        for _, gg in te.groupby('race_id'):
            w = (gg.positionFinish == 1).values
            if w.sum() != 1 or len(gg) < 4:
                continue
            s = gg[col].values
            q = np.exp(beta * (s - s.max()))
            lls += np.log(q[w][0] / q.sum())
            n += 1
        if best is None or lls / n > best[0]:
            best = (lls / n, beta, n)
    return best


def main():
    d = add_history(add_figure(load()))
    print('rows', len(d), 'with par', d.has_par.mean().round(3), flush=True)
    t = d[(d.date >= '2025-07-01') & d.sp.notna() & d.wpr.notna()].copy()
    for c in ('wpr', 'sp'):
        t[c + '_dm'] = t[c] - t.groupby('race_id')[c].transform('mean')
    print('within-race corr(wpr, sp) on', len(t), 'runs:', round(t.wpr_dm.corr(t.sp_dm), 3), flush=True)
    print('across all runs corr(wpr, sp):', round(t.wpr.corr(t.sp), 3), '| corr(fast_len, race mean wpr):',
          round(t.groupby('race_id').fast_len.first().corr(t.groupby('race_id').wpr.mean()), 3), flush=True)
    d = d[(d.nprior >= 3) & d.wpr_1.notna() & d.wpr_2.notna() & d.wpr_3.notna() & d.wpr.notna()].copy()
    print('L3 (wpr_m3) vs sp_m3 corr', round(d.wpr_m3.corr(d.sp_m3), 3), flush=True)

    def dm(cols):
        for c in cols:
            d[c + '_dm'] = d[c] - d.groupby('race_id')[c].transform('mean')
    base_c = ['wpr_1', 'wpr_2', 'wpr_3', 'wpr_m3', 'wpr_m5', 'days']
    sp_c = ['sp_1', 'sp_2', 'sp_3', 'sp_m3', 'sp_m5', 'sp_best3']
    lvl_c = ['fast_len_1', 'fast_len_2', 'fast_len_3']  # race-level speed of the earlier races (how fast the field ran)
    dm(['wpr'] + base_c + sp_c + lvl_c)
    ctx = ['distance', 'field_size', 'gnum']
    arms = {
        'A prior ratings only (L3 / Proj-like)': [c + '_dm' for c in base_c] + ctx,
        'B + speed figure history': [c + '_dm' for c in base_c + sp_c] + ctx,
        'C + speed figure + earlier race-level speed': [c + '_dm' for c in base_c + sp_c + lvl_c] + ctx,
        'S speed figure only (no ratings)': [c + '_dm' for c in ['days'] + sp_c] + ctx,
    }
    tr, va, te = d[d.date < '2025-01-01'], d[(d.date >= '2025-01-01') & (d.date < '2025-07-01')], d[d.date >= '2025-07-01'].copy()
    te = te[te.sp_1.notna() & te.sp_2.notna() & te.sp_3.notna()].copy()  # same rows for every arm
    tr = tr[tr.sp_1.notna() & tr.sp_2.notna() & tr.sp_3.notna()]
    va = va[va.sp_1.notna() & va.sp_2.notna() & va.sp_3.notna()]
    print('train/valid/test', len(tr), len(va), len(te), flush=True)
    P = dict(objective='l2', learning_rate=0.05, num_leaves=63, min_data_in_leaf=200, feature_fraction=0.8, bagging_fraction=0.8, bagging_freq=1, lambda_l2=20,
             verbose=-1, num_threads=4)
    preds = {}
    for name, feats in arms.items():
        m = lgb.train(P, lgb.Dataset(tr[feats], tr.wpr_dm), 3000, valid_sets=[lgb.Dataset(va[feats], va.wpr_dm)], callbacks=[lgb.early_stopping(50, verbose=False)])
        te['p'] = m.predict(te[feats], num_iteration=m.best_iteration)
        preds[name] = te.p.copy()
        rmse = np.sqrt(((te.wpr_dm - te.p) ** 2).mean())
        ll = winner_ll(te, 'p')
        imp = pd.Series(m.feature_importance('gain'), feats).sort_values(ascending=False).head(4)
        print(f'{name}: RMSE {rmse:.4f}, winner log-lik {ll[0]:.4f} (beta {ll[1]}, {ll[2]} races), iters {m.best_iteration}', flush=True)
        print('   top:', ', '.join(f'{k} {v / imp.sum():.0%}' for k, v in imp.items()), flush=True)
    # does the speed arm's prediction carry information the rating arm lacks? residual of A regressed on (B - A)
    a, b = preds['A prior ratings only (L3 / Proj-like)'], preds['B + speed figure history']
    resid = te.wpr_dm - a
    diff = b - a
    print('slope of A residual on (B - A):', round(np.polyfit(diff, resid, 1)[0], 3), '| corr(A, B pred):', round(np.corrcoef(a, b)[0, 1], 4), flush=True)
    # winner picking: does adding speed change the top pick, and who wins when they differ
    te['pa'], te['pb'] = a.values, b.values
    top = lambda col: te.loc[te.groupby('race_id')[col].idxmax()].set_index('race_id')
    ta, tb = top('pa'), top('pb')
    j = ta[['positionFinish', 'horse_id', 'priceStarting']].join(tb[['positionFinish', 'horse_id', 'priceStarting']], lsuffix='_a', rsuffix='_b')
    dif = j[j.horse_id_a != j.horse_id_b]
    print(f'top pick A wins {(j.positionFinish_a == 1).mean():.4f}, B wins {(j.positionFinish_b == 1).mean():.4f}, races {len(j)}, top pick differs in {len(dif) / len(j):.1%}', flush=True)
    print(f'  where they differ: A wins {(dif.positionFinish_a == 1).mean():.4f}, B wins {(dif.positionFinish_b == 1).mean():.4f}, n={len(dif)}', flush=True)


if __name__ == '__main__':
    main()
