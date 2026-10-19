"""Horse-by-condition suitability study (19 Oct 2026). The shipped Proj is a formula on the horse's last runs and ignores conditions. Does a horse's OWN as-of record
at today's going, distance band and spell status (residual of its rating vs its recent form, shrunk) improve rating prediction? Held-out RMSE and paired winner
log-lik, no price. Baseline B = prior ratings + jockey/trainer + barrier, field, distance, track, going, days (what a model has). Train before 2025, early stop
2025-01..06, test 2025-07+. usage: PYTHONPATH=. python research/horse_condition_study.py"""
import os
import sys

import lightgbm as lgb
import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(__file__))
import fourth_rating_study as fr  # noqa: E402
import independent_rating_study as ir  # noqa: E402
import speed_figure_study as sf  # noqa: E402

SHR = 2.0


def asof_mean(runs, key, name, val='res'):
    """Per horse and condition key: mean of `val` over EARLIER runs with the same key, shrunk to 0 by SHR runs. Vectorised cumulative sums."""
    sid = runs.groupby(['horse_id', key], sort=False).ngroup()
    ok = runs[val].notna().astype(int)
    v0 = runs[val].fillna(0.0)
    cs = v0.groupby(sid).cumsum() - v0
    n = ok.groupby(sid).cumsum() - ok
    runs[name] = (cs / (n + SHR)).where(n > 0)
    runs[name + '_n'] = n


def main():
    trials, runs = fr.load_all()
    runs['wpr_dm'] = runs.wpr - runs.groupby('race_id').wpr.transform('mean')
    runs = ir.asof_entity(runs, 'jockey', 'jk')
    runs = ir.asof_entity(runs, 'trainer', 'tn')
    runs['bfrac'] = (runs.barrier - 1) / (runs.field_size - 1).clip(lower=1)
    runs['tcode'] = runs.track.astype('category').cat.codes
    runs = runs.sort_values(['horse_id', 'date']).reset_index(drop=True)
    g = runs.groupby('horse_id', sort=False)
    runs['nprior'] = g.cumcount()
    runs['days'] = (runs.date - g.date.shift(1)).dt.days
    for k in (1, 2, 3):
        runs[f'wpr_{k}'] = g.wpr.shift(k)
    runs['wpr_m3'] = runs[['wpr_1', 'wpr_2', 'wpr_3']].mean(axis=1)
    runs['wpr_m5'] = g.wpr.transform(lambda s: s.shift(1).rolling(5, min_periods=2).mean())
    runs['res'] = runs.wpr - runs.wpr_m5
    runs['gb'] = pd.cut(runs.gnum, [0, 4, 7, 11], labels=False).astype('float')           # good, soft, heavy
    runs['db'] = pd.cut(runs.distance, [0, 1150, 1450, 1850, 9999], labels=False).astype('float')
    runs['spell'] = pd.cut(runs.days, [-1, 21, 60, 120, 9999], labels=False).astype('float')  # quick, normal, spell, long
    runs['fu'] = (runs.days > 60).astype(float)
    runs['gd'] = runs.gb.astype(str) + '|' + runs.db.astype(str)
    for key, nm in (('gb', 'h_go'), ('db', 'h_di'), ('spell', 'h_sp'), ('gd', 'h_gd')):
        asof_mean(runs, key, nm)
    d = runs[(runs.nprior >= 3) & runs.wpr_1.notna() & runs.wpr_2.notna() & runs.wpr_3.notna()].copy()
    base = ['wpr_1', 'wpr_2', 'wpr_3', 'wpr_m3', 'wpr_m5']
    conn = ['jk', 'jk_n', 'tn', 'tn_n']
    dm = set(base + ['jk', 'tn'])
    for c in dm:
        d[c + '_dm'] = d[c] - d.groupby('race_id')[c].transform('mean')
    d['dist_f'] = d.distance
    d['gnum_f'] = d.gnum
    raw = ['days', 'field_size', 'barrier', 'bfrac', 'dist_f', 'gnum_f', 'tcode']
    cols = lambda l: [c + '_dm' if c in dm else c for c in l]
    fam = {
        'horse at going': ['h_go', 'h_go_n'],
        'horse at distance band': ['h_di', 'h_di_n'],
        'horse after this spell length': ['h_sp', 'h_sp_n'],
        'horse at going x distance': ['h_gd', 'h_gd_n'],
    }
    trn, va, te = d[d.date < '2025-01-01'], d[(d.date >= '2025-01-01') & (d.date < '2025-07-01')], d[d.date >= '2025-07-01'].copy()
    print('train/valid/test', len(trn), len(va), len(te), flush=True)
    P = dict(objective='l2', learning_rate=0.05, num_leaves=63, min_data_in_leaf=200, feature_fraction=0.8, bagging_fraction=0.8, bagging_freq=1, lambda_l2=20, verbose=-1, num_threads=4)

    def fit(feats):
        m = lgb.train(P, lgb.Dataset(trn[feats], trn.wpr_dm), 3000, valid_sets=[lgb.Dataset(va[feats], va.wpr_dm)], callbacks=[lgb.early_stopping(50, verbose=False)])
        return m.predict(te[feats], num_iteration=m.best_iteration)
    rm = lambda c: np.sqrt(((te.wpr_dm - te[c]) ** 2).mean())
    te['B'] = fit(cols(base + conn) + raw)
    print(f'B: RMSE {rm("B"):.4f}, winner LL {sf.winner_ll(te, "B")[0]:.4f}', flush=True)
    for nm, l in fam.items():
        te['j'] = fit(cols(base + conn) + raw + l)
        dj = fr.rd(te, 'j', 'B')
        print(f'{nm}: RMSE {rm("j"):.4f} ({100 * (rm("j") / rm("B") - 1):+.2f}%), paired winner LL {dj.mean():+.4f} (se {dj.std() / np.sqrt(len(dj)):.4f}, {len(dj)} races)', flush=True)
    allf = sum(fam.values(), [])
    te['j'] = fit(cols(base + conn) + raw + allf)
    dj = fr.rd(te, 'j', 'B')
    print(f'all: RMSE {rm("j"):.4f} ({100 * (rm("j") / rm("B") - 1):+.2f}%), paired winner LL {dj.mean():+.4f} (se {dj.std() / np.sqrt(len(dj)):.4f})', flush=True)


if __name__ == '__main__':
    main()
