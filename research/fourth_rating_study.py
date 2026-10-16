"""Fourth rating study (16 Oct 2026): three new angles, each as a separate rating and as joint-model features, against a Proj-like baseline. No starting price.

Baseline A2 = LightGBM on the horse's prior wpr plus jockey and trainer as-of inputs (what Proj has; Nett has no history).
Families:
  trials  : last two barrier trials before the run (days ago, finishing position fraction, margin), trial since the last race
  bias    : same-day, same-venue earlier races only: where the top 3 finishers drew and how far back they were at 600m, with the runner's own draw and style
  segments: closing split into 600-400m, 400-200m and the last 200m (gain on the winner from margins at each point) plus 800-600m, all relative to the winner
Each is scored two ways on 2025-07+ (train before 2025, early stop 2025-01..06): (a) its own rating blended into A2 (weight fitted on 2025-07..12, scored 2026), paired
winner log-lik gain; (b) added to the joint model, paired gain over A2 on all test races.
usage: python research/fourth_rating_study.py
"""
import glob
import os
import sys

import lightgbm as lgb
import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(__file__))
import independent_rating_study as ir  # noqa: E402
import speed_figure_study as sf  # noqa: E402

COLS = ['race_id', 'date', 'horse_id', 'track', 'distance', 'going', 'positionFinish', 'marginFinish', 'wpr', 'field_size', 'isBarrierTrial', 'race_class', 'barrier',
        'margin800m', 'margin600m', 'margin400m', 'margin200m', 'jockey', 'trainer']


def load_all():
    fs = [f for f in sorted(glob.glob('race_results_20*.csv.gz')) if not f.endswith('_rc.csv.gz') and int(f[-11:-7]) >= 2019]
    d = pd.concat([pd.read_csv(f, usecols=lambda c: c in COLS, low_memory=False) for f in fs], ignore_index=True)
    d['date'] = pd.to_datetime(d.date)
    d['isBarrierTrial'] = d.isBarrierTrial.fillna(False).astype(bool)
    d = d[~d.race_class.astype(str).str.contains('HUR|STE|JUMP', case=False, na=False)]
    d = d.dropna(subset=['horse_id']).drop_duplicates(['race_id', 'horse_id'])
    d['gnum'] = d.going.astype(str).str.extract(r'(\d+)').astype(float)
    return d[d.isBarrierTrial].copy(), d[~d.isBarrierTrial].dropna(subset=['wpr', 'distance']).copy()


def trial_feats(runs, trials):
    t = trials.dropna(subset=['field_size']).copy()
    t['t_pos'] = (t.positionFinish - 1) / (t.field_size - 1).clip(lower=1)
    t['t_marg'] = t.marginFinish.clip(lower=0, upper=15)
    t = t[['horse_id', 'date', 't_pos', 't_marg']].sort_values('date')
    left = runs[['race_id', 'horse_id', 'date']].sort_values('date')
    m1 = pd.merge_asof(left, t.rename(columns={'date': 'td1', 't_pos': 't1_pos', 't_marg': 't1_marg'}), left_on='date', right_on='td1', by='horse_id',
                       allow_exact_matches=False)
    t2 = t.rename(columns={'date': 'td2', 't_pos': 't2_pos', 't_marg': 't2_marg'})
    m1['before'] = m1.td1 - pd.Timedelta(days=1)
    m2 = pd.merge_asof(m1.sort_values('before').dropna(subset=['before']), t2, left_on='before', right_on='td2', by='horse_id', allow_exact_matches=False)
    out = m1.merge(m2[['race_id', 'horse_id', 'td2', 't2_pos', 't2_marg']], on=['race_id', 'horse_id'], how='left')
    out['t1_days'] = (out.date - out.td1).dt.days
    out['t2_days'] = (out.date - out.td2).dt.days
    return out[['race_id', 'horse_id', 't1_days', 't1_pos', 't1_marg', 't2_days', 't2_pos', 't2_marg']]


def bias_feats(d):
    """Per race: where the top 3 drew and sat at 600m; then cumulative over EARLIER races the same day at the venue."""
    d = d.copy()
    d['bfrac'] = (d.barrier - 1) / (d.field_size - 1).clip(lower=1)
    d['m6r'] = (d.groupby('race_id').margin600m.rank(method='average') - 1) / (d.field_size - 1).clip(lower=1)
    top = d[d.positionFinish <= 3]
    rc = top.groupby('race_id').agg(b3=('bfrac', 'mean'), f3=('m6r', 'mean')).reset_index()
    rc = rc.merge(d.drop_duplicates('race_id')[['race_id', 'track', 'date']], on='race_id').sort_values(['track', 'date', 'race_id'])
    g = rc.groupby(['track', 'date'])
    rc['n_prev'] = g.cumcount()
    for c in ('b3', 'f3'):
        rc[c + '_prev'] = (g[c].cumsum() - rc[c]) / rc.n_prev.replace(0, np.nan)
    rc['n_prev'] = rc.n_prev.where(rc.n_prev >= 2)
    rc.loc[rc.n_prev.isna(), ['b3_prev', 'f3_prev']] = np.nan
    return d, rc[['race_id', 'n_prev', 'b3_prev', 'f3_prev']]


def segments(d):
    w = d[d.positionFinish == 1].groupby('race_id')[['margin800m', 'margin600m', 'margin400m', 'margin200m']].first().add_prefix('w_')
    d = d.merge(w, on='race_id', how='left')
    rel = {}
    for p in ('800', '600', '400', '200'):
        rel[p] = (d[f'margin{p}m'] - d[f'w_margin{p}m']).clip(-25, 25)
    relf = d.marginFinish.clip(lower=0, upper=25)
    d['seg_early'] = rel['800'] - rel['600']
    d['g600_400'] = rel['600'] - rel['400']
    d['g400_200'] = rel['400'] - rel['200']
    d['g200_fin'] = rel['200'] - relf
    d['seg_mid'] = d.g600_400 + d.g400_200
    for c in ('seg_early', 'g600_400', 'g400_200', 'g200_fin', 'seg_mid'):
        d[c] = d[c] - d.groupby('race_id')[c].transform('mean')
    return d


def rd(df, c1, c0, beta=0.2):
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


def main():
    trials, runs = load_all()
    print('runs', len(runs), 'trials', len(trials), flush=True)
    runs['wpr_dm'] = runs.wpr - runs.groupby('race_id').wpr.transform('mean')
    runs = ir.asof_entity(runs, 'jockey', 'jk')
    runs = ir.asof_entity(runs, 'trainer', 'tn')
    runs = runs.merge(trial_feats(runs, trials), on=['race_id', 'horse_id'], how='left')
    runs, rc = bias_feats(runs)
    runs = runs.merge(rc, on='race_id', how='left')
    runs = segments(runs)
    runs = runs.sort_values(['horse_id', 'date']).reset_index(drop=True)
    g = runs.groupby('horse_id', sort=False)
    runs['nprior'] = g.cumcount()
    runs['days'] = (runs.date - g.date.shift(1)).dt.days
    for c in ('wpr', 'seg_early', 'seg_mid', 'g200_fin', 'g600_400', 'g400_200', 'm6r'):
        for k in (1, 2, 3):
            runs[f'{c}_{k}'] = g[c].shift(k)
        runs[f'{c}_m3'] = runs[[f'{c}_1', f'{c}_2', f'{c}_3']].mean(axis=1)
    runs['wpr_m5'] = g.wpr.transform(lambda s: s.shift(1).rolling(5, min_periods=2).mean())
    runs['g200_m5'] = g.g200_fin.transform(lambda s: s.shift(1).rolling(5, min_periods=2).mean())
    runs['m6r_m5'] = g.m6r.transform(lambda s: s.shift(1).rolling(5, min_periods=2).mean())
    runs['bfrac'] = (runs.barrier - 1) / (runs.field_size - 1).clip(lower=1)
    runs['draw_fit'] = (runs.bfrac - 0.5) * (runs.b3_prev - 0.5)
    runs['style_fit'] = (runs.m6r_m5 - 0.5) * (runs.f3_prev - 0.5)
    runs['trial_since_run'] = (runs.t1_days < runs.days).astype(float).where(runs.t1_days.notna())
    d = runs[(runs.nprior >= 3) & runs.wpr_1.notna() & runs.wpr_2.notna() & runs.wpr_3.notna()].copy()
    d = d[d.seg_mid_1.notna() & d.seg_mid_2.notna() & d.seg_mid_3.notna()]
    print('rows', len(d), flush=True)
    base = ['wpr_1', 'wpr_2', 'wpr_3', 'wpr_m3', 'wpr_m5']
    conn = ['jk', 'jk_n', 'tn', 'tn_n']
    fam = {
        'trials': ['t1_days', 't1_pos', 't1_marg', 't2_days', 't2_pos', 't2_marg', 'trial_since_run'],
        'bias': ['n_prev', 'b3_prev', 'f3_prev', 'bfrac', 'm6r_m5', 'draw_fit', 'style_fit'],
        'segments': ['seg_early_1', 'seg_early_2', 'seg_early_3', 'seg_early_m3', 'g200_fin_1', 'g200_fin_2', 'g200_fin_3', 'g200_fin_m3', 'g200_m5',
                     'seg_mid_1', 'seg_mid_2', 'seg_mid_3', 'seg_mid_m3', 'g600_400_m3', 'g400_200_m3'],
    }
    dm = set(base + ['jk', 'tn'] + [c for c in fam['segments']])
    for c in dm:
        d[c + '_dm'] = d[c] - d.groupby('race_id')[c].transform('mean')
    cols = lambda l: [c + '_dm' if c in dm else c for c in l] + ['days', 'field_size']
    trn, va, te = d[d.date < '2025-01-01'], d[(d.date >= '2025-01-01') & (d.date < '2025-07-01')], d[d.date >= '2025-07-01'].copy()
    print('train/valid/test', len(trn), len(va), len(te), flush=True)
    P = dict(objective='l2', learning_rate=0.05, num_leaves=63, min_data_in_leaf=200, feature_fraction=0.8, bagging_fraction=0.8, bagging_freq=1, lambda_l2=20,
             verbose=-1, num_threads=4)

    def fit(feats):
        m = lgb.train(P, lgb.Dataset(trn[feats], trn.wpr_dm), 3000, valid_sets=[lgb.Dataset(va[feats], va.wpr_dm)], callbacks=[lgb.early_stopping(50, verbose=False)])
        return m.predict(te[feats], num_iteration=m.best_iteration)
    te['A2'] = fit(cols(base + conn))
    rm = lambda c: np.sqrt(((te.wpr_dm - te[c]) ** 2).mean())
    dmean = lambda c: te[c] - te.groupby('race_id')[c].transform('mean')
    te['A2d'] = dmean('A2')
    print(f'A2 (prior ratings + jockey/trainer): RMSE {rm("A2"):.4f}, winner log-lik {sf.winner_ll(te, "A2")[0]:.4f}', flush=True)
    half = te.date < '2026-01-01'
    for nm, l in fam.items():
        te[nm] = fit(cols(l))
        te[nm + 'd'] = dmean(nm)
        te[nm + '_j'] = fit(cols(base + conn + l))
        corr = te.A2d.corr(te[nm + 'd'])
        best = (-9, 0.0)
        for w in (0.0, 0.1, 0.2, 0.3, 0.4, 0.5, 0.75, 1.0):
            te['bl'] = te.A2d + w * te[nm + 'd']
            r = sf.winner_ll(te[half], 'bl')[0]
            if r > best[0]:
                best = (r, w)
        te['bl'] = te.A2d + best[1] * te[nm + 'd']
        d1 = rd(te[~half], 'bl', 'A2d')
        dj = rd(te, nm + '_j', 'A2')
        print(f'{nm}: own rating alone RMSE {rm(nm):.4f}, corr with A2 {corr:.3f}; blended into A2 (w={best[1]}, second half {len(d1)} races): paired {d1.mean():+.4f} (se {d1.std() / np.sqrt(len(d1)):.4f}); '
              f'joint model: RMSE {rm(nm + "_j"):.4f}, paired {dj.mean():+.4f} (se {dj.std() / np.sqrt(len(dj)):.4f}, {len(dj)} races)', flush=True)
    te['all_j'] = fit(cols(base + conn + sum(fam.values(), [])))
    da = rd(te, 'all_j', 'A2')
    print(f'all three joint: RMSE {rm("all_j"):.4f} (A2 {rm("A2"):.4f}), paired {da.mean():+.4f} (se {da.std() / np.sqrt(len(da)):.4f})', flush=True)


if __name__ == '__main__':
    main()
