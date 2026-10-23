"""Model-only accuracy (23 Oct 2026, no price anywhere). Does race shape add to WINNING and TOP-4 chances beyond what the Proj says, when the model is trained on the
outcome itself rather than on the rating? Runner-level LightGBM (binary win, binary top 4) on out-of-sample Huber-4 Proj plus pre-race shape inputs (the horse's usual settle,
gap, early speed and lane from results/GPS history, barrier, and field contention counts built from the full field), trained on 2025 races, scored on 2026 races.
Partial fields (runners with a Proj in the page store, >= 5 per race, the winner among them). Compared with Proj alone (softmax, sharpness fitted on 2025).
Needs /tmp/train_ctx_gps_oos.parquet. Run: PYTHONPATH=. python analysis/trip_map/direct_winner_model.py"""
import os, sys
import numpy as np, pandas as pd, lightgbm as lgb
from scipy.optimize import minimize_scalar
from sklearn.metrics import roc_auc_score, log_loss
sys.path.insert(0, os.path.dirname(__file__)); sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'projection'))
import gps_feats as GF
import build_trip_map as B
rr, FL, HIST, CONT = GF.build()
pg = pd.read_parquet('/tmp/train_ctx_gps_oos.parquet'); pg['date'] = pd.to_datetime(pg.date)
pg = pg[pg.rid.notna() & (pg.n >= 3)].copy()
pg['win'] = (pg.positionFinish == 1).astype(int); pg['top4'] = (pg.positionFinish <= 4).astype(int)
gb = pg.groupby('rid')
pg = pg[(gb.win.transform('sum') == 1) & (gb.win.transform('size') >= 5)].copy()
g = pg.groupby('rid')
for c in ['proj0', 'settle_h3', 'gap800_h3', 'early_z_h3', 'lane_rel_h3', 'extra_rel_h3', 'barr_f', 'std4', 'mean3', 'max4']:
    if c in pg.columns:
        pg['rel_' + c] = pg[c] - g[c].transform('mean')
pg['proj_rank'] = g.proj0.rank(ascending=False, method='first'); pg['nrun'] = g.proj0.transform('size')
pg['gap_to_top'] = g.proj0.transform('max') - pg.proj0
ctx_cols = [c for c in CONT if c.startswith('c_')]
SHAPE = ['settle_h3', 'gap800_h3', 'early_z_h3', 'lane_rel_h3', 'extra_rel_h3', 'rel_settle_h3', 'rel_gap800_h3', 'rel_early_z_h3', 'rel_lane_rel_h3', 'barr_f', 'rel_barr_f', 'bf', 'bar_x_early', 'n_gps', 'burn_h'] + ctx_cols
SHAPE = [c for c in dict.fromkeys(SHAPE) if c in pg.columns]
BASE = ['rel_proj0', 'proj0', 'gap_to_top', 'proj_rank', 'nrun', 'n', 'rel_std4', 'rel_mean3', 'rel_max4', 'distance', 'field_size', 'going_n']
BASE = [c for c in BASE if c in pg.columns]
tr, te = pg[pg.date < '2026-01-01'], pg[pg.date >= '2026-01-01'].copy()
print('train (2025) races', tr.rid.nunique(), 'runners', len(tr), '| test (2026) races', te.rid.nunique(), 'runners', len(te), flush=True)
def softmax_ll(df, score):
    s = pd.Series(score, index=df.index); mx = s.groupby(df.rid).transform('max'); ex = np.exp(s - mx); den = ex.groupby(df.rid).transform('sum')
    return np.log(ex / den)[df.win == 1]
# Proj alone: sharpness from 2025
beta = minimize_scalar(lambda b: -softmax_ll(tr, b * tr.rel_proj0.values).sum(), bounds=(0.01, 1), method='bounded').x
base_ll = softmax_ll(te, beta * te.rel_proj0.values)
def top4_overlap(df, score):
    big = df[df.nrun >= 8]; sc = pd.Series(score, index=df.index).reindex(big.index)
    rk = sc.groupby(big.rid).rank(ascending=False, method='first'); fin = big.groupby('rid').positionFinish.rank(method='first')
    return ((rk <= 4) & (fin <= 4)).groupby(big.rid).sum()
base_t4 = top4_overlap(te, te.rel_proj0.values)
print(f'Proj alone: beta {beta:.3f}, winner LL {base_ll.mean():.4f}, top pick wins {100 * (te[te.proj_rank == 1].win.mean()):.1f}%, top-4 overlap {base_t4.mean():.4f} of 4 (races {len(base_t4)})', flush=True)
P = dict(objective='binary', learning_rate=0.03, num_leaves=7, min_data_in_leaf=60, feature_fraction=0.7, bagging_fraction=0.8, bagging_freq=1, lambda_l2=20, verbose=-1, num_threads=4)
def run(name, feats, rounds):
    out = {}
    for tgt in ('win', 'top4'):
        ps = []
        for sd in range(3):
            m = lgb.train(dict(P, seed=sd, bagging_seed=sd, feature_fraction_seed=sd), lgb.Dataset(tr[feats], tr[tgt]), rounds); ps.append(m.predict(te[feats]))
        out[tgt] = np.mean(ps, 0)
    # winner LL: normalise the win probabilities within race
    p = pd.Series(out['win'], index=te.index); ll = np.log(p / p.groupby(te.rid).transform('sum'))[te.win == 1]
    t4 = top4_overlap(te, out['top4'])
    auc = roc_auc_score(te.top4, out['top4'])
    d = (ll.values - base_ll.values); d4 = (t4 - base_t4).dropna()
    print(f'  {name:34s} winner LL {ll.mean():.4f} (gain over Proj alone {d.mean():+.4f}, se {d.std() / np.sqrt(len(d)):.4f}) | top-4 overlap {t4.mean():.4f} (gain {d4.mean():+.4f}, se {d4.std() / np.sqrt(len(d4)):.4f}) | top-4 AUC {auc:.4f}')
    return out
# reference: Proj as a plain feature set (the GBM re-learning the Proj; any gain of the shape sets is measured against this)
for rounds in (150,):
    r0 = run('Proj and context only (GBM)', BASE, rounds)
    r1 = run('+ usual shape and contention', BASE + SHAPE, rounds)
    r2 = run('+ shape, no contention counts', BASE + [c for c in SHAPE if c not in ctx_cols], rounds)
    r3 = run('+ contention counts only', BASE + ctx_cols, rounds)
print('\ntop-4 AUC of Proj alone: %.4f' % roc_auc_score(te.top4, te.rel_proj0))
# which shape inputs matter
m = lgb.train(P, lgb.Dataset(tr[BASE + SHAPE], tr.win), 150)
imp = pd.Series(m.feature_importance('gain'), index=BASE + SHAPE).sort_values(ascending=False)
print('win model top inputs by gain:', ', '.join(f'{i} {100 * v / imp.sum():.0f}%' for i, v in imp.head(10).items()))
