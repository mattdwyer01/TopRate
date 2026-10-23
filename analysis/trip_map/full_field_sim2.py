"""Full-field joint race simulation (23 Oct 2026). Rating signal = the rebuilt Spd's held-out 2026 predictions (every runner of ~12k races has one; the Proj has no full-field history before the live log).
Pipeline per race: (1) forecast each runner's settle score and early speed from pre-race history, barrier, field size and contention (trained on results before 2026);
(2) sample the field JOINTLY many times: settle scores with runner noise, ranked together so positions are exclusive; early speeds with a race-wide pace shock, pace = mean of the three fastest;
(3) map each sampled shape to a performance adjustment with a model fitted on ACTUAL shapes (settle position share, early speed, pace, early speed minus pace, barrier, field size) against the figure residual;
(4) performance = Spd + shape adjustment + noise, winner = best performer, win chance = share of simulations won. Cross-fitted by date halves (adjustment model and noise sd fitted on one half, scored on the other).
Variants: softmax on the Spd; Monte Carlo with noise only; point-forecast shape (no shape randomness); joint shape. Model only, no price.
Needs /tmp/spd_model_profile_te.parquet (spd_model_profile.py) and /tmp/gps_pressure_feats.parquet. Run: PYTHONPATH=. python analysis/trip_map/full_field_sim.py"""
import os, sys, warnings
import numpy as np, pandas as pd, lightgbm as lgb
from scipy.optimize import minimize_scalar
warnings.filterwarnings('ignore')
sys.path.insert(0, os.path.dirname(__file__)); sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'projection'))
import gps_feats as GF
import build_trip_map as B
rng = np.random.default_rng(11)
rr, FL, HIST, CONT = GF.build()
res = B.add_result_features(B.load_results())[['hn', 'date', 'distance', 'going_s', 'barfrac', 'fs']].drop_duplicates(['hn', 'date'])
res['date'] = pd.to_datetime(res.date).astype('datetime64[ns]'); rr['date'] = pd.to_datetime(rr.date).astype('datetime64[ns]')
rr = rr.merge(res, on=['hn', 'date'], how='left')
PRE = ['bf', 'barfrac', 'fs', 'distance', 'going_s', 'settle_h3', 'gap800_h3', 'early_z_h3', 'early_z_h8', 'extra_rel_h3', 'lane_rel_h3', 'n_gps', 'burn_h', 'bar_x_early'] + [c for c in CONT if c.startswith('c_')]
PRE = [c for c in dict.fromkeys(PRE) if c in rr.columns]
tr0 = rr[(rr.date >= '2022-01-01') & (rr.date < '2026-01-01')]
PR = dict(objective='regression', learning_rate=0.05, num_leaves=31, min_data_in_leaf=100, feature_fraction=0.8, verbose=-1, num_threads=4)
fs_m = lgb.train(PR, lgb.Dataset(tr0[tr0.settle.notna()][PRE], tr0[tr0.settle.notna()].settle), 250)
fe_m = lgb.train(PR, lgb.Dataset(tr0[tr0.h_early.notna() if False else tr0.early_z.notna()][PRE], tr0[tr0.early_z.notna()].early_z), 250)
sd_settle = float((tr0[tr0.settle.notna()].settle - fs_m.predict(tr0[tr0.settle.notna()][PRE])).std())
sd_early = float((tr0[tr0.early_z.notna()].early_z - fe_m.predict(tr0[tr0.early_z.notna()][PRE])).std())
print(f'forecast residual sd: settle {sd_settle:.3f}, early speed {sd_early:.3f}', flush=True)
te = pd.read_parquet('/tmp/spd_model_profile_te.parquet'); te['date'] = pd.to_datetime(te.date).astype('datetime64[ns]')
te = te.merge(rr[['hn', 'date', 'settle', 'early_z', 'pace', 'gps'] + PRE].drop_duplicates(['hn', 'date']), on=['hn', 'date'], how='left', suffixes=('', '_rr'))
te['f_settle'] = fs_m.predict(te[PRE]); te['f_early'] = np.where(te.gps.fillna(False).astype(bool) | te.n_gps.notna(), fe_m.predict(te[PRE]), np.nan)
te = te.dropna(subset=['positionFinish', 'p_base', 'bf']).copy()
te['win'] = (te.positionFinish == 1).astype(int)
sz = te.groupby('race_id').win.transform('size'); te = te[sz >= 6]
g = te.groupby('race_id'); te = te[g.win.transform('sum') == 1].copy()
# keep races where most of the field is present (the original field size is in fs)
te = te[te.groupby('race_id').win.transform('size') >= 0.85 * te.fs]
te = te.sort_values(['race_id']).reset_index(drop=True)
te['resid'] = te.wpr - te.p_base; te['resid_c'] = te.resid - te.groupby('race_id').resid.transform('mean')
te['settle_rank_pct'] = (te.groupby('race_id').settle.rank(method='first') - 1) / (te.groupby('race_id').settle.transform('count') - 1).replace(0, np.nan)
print('races', te.race_id.nunique(), 'runners', len(te), flush=True)
d0 = te.date.sort_values().iloc[len(te) // 2]
GF_ = ['settle_pct', 'early_z', 'pace', 'early_minus_pace', 'bf', 'fs']
def actual_X(d):
    return pd.DataFrame({'settle_pct': d.settle_rank_pct.values, 'early_z': d.early_z.values, 'pace': d.pace.values, 'early_minus_pace': (d.early_z - d.pace).values, 'bf': d.bf.values, 'fs': d.fs.values})
def fit_g(d):
    return lgb.train(dict(PR, num_leaves=7, min_data_in_leaf=300, learning_rate=0.03, lambda_l2=20), lgb.Dataset(actual_X(d), d.resid_c), 200)
def sim_probs(d, gmodel, sigma, S, mode):
    """mode: 'none' (noise only), 'point' (shape at its forecast, only performance noise), 'joint' (shape sampled jointly)."""
    d = d.sort_values('race_id').reset_index(drop=True); n = len(d)
    sizes = d.groupby('race_id').size().values; starts = np.r_[0, np.cumsum(sizes)[:-1]]; ridx = np.repeat(np.arange(len(sizes)), sizes)
    base = d.p_base.values; wins = np.zeros(n)
    fset, fear, bf, fsz = d.f_settle.values, d.f_early.values, d.bf.values, d.fs.values
    has_e = ~np.isnan(fear)
    if mode == 'point':
        dd = d.assign(settle_rank_pct=(d.groupby('race_id').f_settle.rank(method='first') - 1) / (d.groupby('race_id').f_settle.transform('count') - 1).replace(0, np.nan))
        e = fear; pace = pd.Series(np.where(has_e, e, -9)).groupby(ridx).transform(lambda s: s.nlargest(3).mean()).values; pace = np.where(np.isfinite(pace) & (pace > -8), pace, np.nan)
        Xp = pd.DataFrame({'settle_pct': dd.settle_rank_pct.values, 'early_z': e, 'pace': pace, 'early_minus_pace': e - pace, 'bf': bf, 'fs': fsz})
        shape_adj = gmodel.predict(Xp)
    for _ in range(S):
        if mode == 'none': adj = 0.0
        elif mode == 'point': adj = shape_adj
        else:
            sc = fset + rng.normal(0, sd_settle, n)
            rk = pd.Series(sc).groupby(ridx).rank(method='first').values; cnt = np.repeat(sizes, sizes)
            sp = (rk - 1) / np.maximum(cnt - 1, 1)
            shock = rng.normal(0, 0.35, len(sizes))[ridx]
            e = np.where(has_e, fear + rng.normal(0, sd_early, n) + shock, np.nan)
            tmp = pd.Series(np.where(has_e, e, -9.0)); top3 = tmp.groupby(ridx).transform(lambda s: s.nlargest(3).mean()).values
            pace = np.where(top3 > -8, top3, np.nan)
            adj = gmodel.predict(pd.DataFrame({'settle_pct': sp, 'early_z': e, 'pace': pace, 'early_minus_pace': e - pace, 'bf': bf, 'fs': fsz}))
        perf = base + adj + rng.normal(0, sigma, n)
        mx = np.maximum.reduceat(perf, starts); wins += (perf == np.repeat(mx, sizes))
    p = (wins + 0.5) / (S + 0.5 * np.repeat(sizes, sizes))
    return d.assign(prob=p)
def mc_ll(d, gmodel, sigma, S, mode):
    o = sim_probs(d, gmodel, sigma, S, mode); return np.log(o.prob[o.win == 1]).values, o
def softmax_ll(df, beta):
    s = beta * (df.p_base - df.groupby('race_id').p_base.transform('mean')); mx = s.groupby(df.race_id).transform('max'); ex = np.exp(s - mx); den = ex.groupby(df.race_id).transform('sum')
    return np.log(ex / den)[df.win == 1]

# fair comparison: put the shape adjustment into the analytic softmax instead of Monte Carlo
from scipy.optimize import minimize
def point_adj(d, gm):
    d = d.sort_values('race_id').reset_index(drop=True); ridx = pd.factorize(d.race_id)[0]
    rk = (d.groupby('race_id').f_settle.rank(method='first') - 1) / (d.groupby('race_id').f_settle.transform('count') - 1).replace(0, np.nan)
    e = d.f_early.values; has = ~np.isnan(e)
    pace = pd.Series(np.where(has, e, -9.0)).groupby(ridx).transform(lambda x: x.nlargest(3).mean()).values; pace = np.where(pace > -8, pace, np.nan)
    d['adj'] = gm.predict(pd.DataFrame({'settle_pct': rk.values, 'early_z': e, 'pace': pace, 'early_minus_pace': e - pace, 'bf': d.bf.values, 'fs': d.fs.values}))
    return d
def sm_ll(df, beta, k):
    sc = df.p_base + k * df.adj; s = beta * (sc - sc.groupby(df.race_id).transform('mean')); mx = s.groupby(df.race_id).transform('max'); ex = np.exp(s - mx); den = ex.groupby(df.race_id).transform('sum')
    return np.log(ex / den)[df.win == 1]
res_ = {'base': [], 'shape': []}
for a, b in ((te[te.date < d0], te[te.date >= d0]), (te[te.date >= d0], te[te.date < d0])):
    gm = fit_g(a); a = point_adj(a, gm); b = point_adj(b, gm)
    r0 = minimize_scalar(lambda x: -sm_ll(a, x, 0).sum(), bounds=(0.001, 1), method='bounded').x
    r1 = minimize(lambda p: -sm_ll(a, p[0], p[1]).sum(), [r0, 0.5], method='Nelder-Mead').x
    print('fit: beta', round(r0, 4), '| with shape: beta %.4f, shape weight k %.3f' % tuple(r1), flush=True)
    res_['base'].append(sm_ll(b, r0, 0).values); res_['shape'].append(sm_ll(b, r1[0], r1[1]).values)
b0, b1 = np.concatenate(res_['base']), np.concatenate(res_['shape']); d = b1 - b0
print(f'\nANALYTIC SOFTMAX, full fields, cross-fitted: Spd alone {b0.mean():.4f} | Spd + forecast shape adjustment {b1.mean():.4f} | gain {d.mean():+.4f} (se {d.std() / np.sqrt(len(d)):.4f}) over {len(d)} races')
