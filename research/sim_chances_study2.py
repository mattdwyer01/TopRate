"""Improved scenario simulation (S3b) and calibrated noise, 14 Oct 2026. Follows sim_chances_study.py (same data, split, base model C and pace-fit model E).

Why the first scenario simulation (S3) failed: it moved every horse by its raw 8-run slope times a drawn shape, and those slopes are mostly noise, so it added far too much
random movement (win log-lik -2.63). Fixes here:
  1. The pace loadings are FITTED, not assumed: on the validation half-year, regress the base model's residual on (realised shape - predicted shape) interacted with the
     horse's slope, its early and late speed history. Coefficients are small and shrunk by construction. Printed with t-values so a null result shows.
  2. The simulated race draws shape = predicted + N(0, shape_sd); each horse moves by loading x the drawn deviation, and its independent noise is reduced by the variance
     the loading explains.
  3. A noise scale tau (applied to all simulated methods) is fitted on the validation winners, which also tests whether widening the noise fixes the longshot understatement.
usage: python research/sim_chances_study2.py
"""
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(__file__))
import sim_chances_study as M  # noqa: E402

rng = np.random.default_rng(11)


def win_ll(df, draws_fn, nsim=1500):
    ll, n = 0.0, 0
    for _, g in df.groupby('race_id', sort=False):
        w = (g.positionFinish == 1).values
        if len(g) < 4 or w.sum() != 1:
            continue
        sim = draws_fn(g, nsim)
        win = np.bincount(np.argmax(sim, axis=1), minlength=len(g)) / nsim
        pw = (win + 1e-3) / (win + 1e-3).sum()
        ll += np.log(pw[w][0]); n += 1
    return ll / n


def main():
    d, me, shape_sd = M.prepare()
    base_c = ['wpr_1', 'wpr_2', 'wpr_3', 'wpr_m3', 'wpr_m5', 'days']
    style_c = ['e_1', 'e_2', 'e_3', 'e_m3', 'e_m5', 'l_1', 'l_2', 'l_3', 'l_m3', 'l_m5', 'close_m3', 'sect_i_time_m3', 'sect_i_l200_1']
    C = [c + '_dm' for c in base_c + style_c] + ['distance', 'field_size', 'gnum', 'pace_pressure', 'e_rank', 'l_rank']
    E = C + ['slope_e_dm', 'fit_e_pred_dm', 'n_slope', 'pred_sh_e']
    tr, va, te = d[d.date < '2025-01-01'], d[(d.date >= '2025-01-01') & (d.date < '2025-07-01')].copy(), d[d.date >= '2025-07-01'].copy()
    mC, mE = M.fit(tr, va, C), M.fit(tr, va, E)
    for m, f, nm in ((mC, C, 'pC'), (mE, E, 'pE')):
        va[nm] = m.predict(va[f], num_iteration=m.best_iteration)
        te[nm] = m.predict(te[f], num_iteration=m.best_iteration)
    sdC = np.array([float((va.wpr_dm - va.pC)[M.bucket(va.nprior.values) == b].std()) for b in range(3)])
    sdE = np.array([float((va.wpr_dm - va.pE)[M.bucket(va.nprior.values) == b].std()) for b in range(3)])
    print('noise sd C', sdC.round(2), 'E', sdE.round(2), 'shape sd', round(shape_sd, 2), flush=True)

    # 1. fit the pace loadings on validation residuals of the base model
    for df in (va, te):
        df['dev'] = df.sh_e - df.pred_sh_e
        df['x_slope'] = np.nan_to_num(df.slope_e) * df.dev
        df['x_e'] = df.e_m3_dm * df.dev
        df['x_l'] = df.l_m3_dm * df.dev
        df['x_rank'] = (df.e_rank - 0.5) * df.dev
    v = va.dropna(subset=['dev', 'pC'])
    X = v[['x_slope', 'x_e', 'x_l', 'x_rank']].values
    y = (v.wpr_dm - v.pC).values
    beta, *_ = np.linalg.lstsq(X, y, rcond=None)
    res = y - X @ beta
    cov = np.linalg.inv(X.T @ X) * res.var()
    t = beta / np.sqrt(np.diag(cov))
    print('pace loadings (slope, early hist, late hist, early rank):', beta.round(4), 't', t.round(1), 'R2 gain', round(1 - res.var() / y.var(), 5), flush=True)

    def loading(g):
        return (beta[0] * np.nan_to_num(g.slope_e.values) + beta[1] * g.e_m3_dm.values + beta[2] * g.l_m3_dm.values + beta[3] * (g.e_rank.values - 0.5))

    def indep(col, sds, tau):
        def f(g, nsim=M.NSIM):
            s = sds[M.bucket(g.nprior.values)] * tau
            return g[col].values[None, :] + M.rng.normal(size=(nsim, len(g))) * s[None, :]
        return f

    def scenario(tau):
        def f(g, nsim=M.NSIM):
            ld = loading(g)
            s = sdC[M.bucket(g.nprior.values)]
            s = np.sqrt(np.maximum(s ** 2 - (ld * shape_sd) ** 2, (0.9 * s) ** 2)) * tau
            dev = M.rng.normal(size=(nsim, 1)) * shape_sd
            return g.pC.values[None, :] + ld[None, :] * dev + M.rng.normal(size=(nsim, len(g))) * s[None, :]
        return f

    # 3. fit tau on validation winners
    taus = (0.95, 1.0, 1.05, 1.1, 1.2)
    fit_tau = {}
    for name, mk in (('S1', lambda t: indep('pC', sdC, t)), ('S2', lambda t: indep('pE', sdE, t)), ('S3b', scenario)):
        res_t = [(win_ll(va, mk(t_)), t_) for t_ in taus]
        fit_tau[name] = max(res_t)[1]
        print(name, 'validation win LL by tau', {t_: round(ll, 4) for ll, t_ in res_t}, '-> tau', fit_tau[name], flush=True)

    # test
    M.score_method(te, indep('pC', sdC, 1.0), 'S1 independent noise (base model)')
    M.score_method(te, indep('pC', sdC, fit_tau['S1']), f"S1c same, noise x {fit_tau['S1']}")
    M.score_method(te, indep('pE', sdE, fit_tau['S2']), f"S2c pace-fit feature model, noise x {fit_tau['S2']}")
    M.score_method(te, scenario(1.0), 'S3b scenario sim, fitted loadings')
    M.score_method(te, scenario(fit_tau['S3b']), f"S3c scenario sim, noise x {fit_tau['S3b']}")


if __name__ == '__main__':
    main()
