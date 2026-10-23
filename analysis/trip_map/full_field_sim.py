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
out = {k: [] for k in ('softmax', 'noise MC', 'point shape', 'joint shape')}
for a, b in ((te[te.date < d0], te[te.date >= d0]), (te[te.date >= d0], te[te.date < d0])):
    gm = fit_g(a)
    # tune noise sd on a sample of the fitting half
    ra = a.race_id.drop_duplicates().sample(min(700, a.race_id.nunique()), random_state=1); sub = a[a.race_id.isin(ra)]
    sig = {}
    for mode in ('none', 'point', 'joint'):
        best = max(((mc_ll(sub, gm, s, 40, mode)[0].mean(), s) for s in (2.5, 3.5, 4.5, 5.5, 6.5)))
        sig[mode] = best[1]
    print('fit half', len(a), 'races', a.race_id.nunique(), '| noise sd chosen', sig, flush=True)
    beta = minimize_scalar(lambda x: -softmax_ll(a, x).sum(), bounds=(0.001, 1), method='bounded').x
    out['softmax'].append(softmax_ll(b, beta).values)
    out['noise MC'].append(mc_ll(b, gm, sig['none'], 150, 'none')[0])
    out['point shape'].append(mc_ll(b, gm, sig['point'], 150, 'point')[0])
    out['joint shape'].append(mc_ll(b, gm, sig['joint'], 150, 'joint')[0])
    print('scored half', b.race_id.nunique(), 'races', flush=True)
print('\nWINNER LOG-LIKELIHOOD (full fields, model only, cross-fitted)')
base = np.concatenate(out['softmax'])
for k in out:
    v = np.concatenate(out[k]); dlt = v - base
    print(f'  {k:14s} LL {v.mean():.4f}  vs softmax {dlt.mean():+.4f} (se {dlt.std() / np.sqrt(len(dlt)):.4f})  races {len(v)}')
v0 = np.concatenate(out['noise MC']); 
for k in ('point shape', 'joint shape'):
    dd = np.concatenate(out[k]) - v0; print(f'  {k} minus noise-only MC: {dd.mean():+.4f} (se {dd.std() / np.sqrt(len(dd)):.4f})')
