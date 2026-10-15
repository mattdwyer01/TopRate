"""Phase 1 ceiling check for a 'total race' simulation (15 Oct 2026, read-only).

Question: does giving runners of the same running style a SHARED random term (leaders move together, closers move together) improve the joint chances
(quinella, trifecta, first-four) or place chances beyond independent noise? Same data, split and base rating model (C) as sim_chances_study.py.

Each runner is put in a style group within its race by early-speed rank (front third, middle, back third). A simulated race draws one normal term per group
(sd rho) and adds it to every runner in the group; the runner's own independent noise sd is cut so the total variance is unchanged (sd_ind = sqrt(sd^2 - rho^2)),
so the marginal spread of each runner stays the same and only the CORRELATION changes. rho is scanned 0..4; rho 0 is the current independent simulation.
Scored on the held-out races (2025-07 onward): winner, place, quinella, trifecta log-likelihood (smoothed), and the paired gain over rho 0 with a standard error.
Stop rule from the scope note: if the best rho adds under about 0.01 nats a race on quinella, the total-race simulation is not worth building.
usage: python research/phase1_shared_noise.py
"""
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(__file__))
import sim_chances_study as M  # noqa: E402

NS = 3000
rng = np.random.default_rng(23)
RHOS = (0.0, 1.0, 2.0, 3.0, 4.0)


def race_scores(g, sd, rho, mu):
    n = len(g)
    grp = np.digitize(g.e_rank.values, [1 / 3, 2 / 3])          # 0 = front third (rank pct small = fast)
    base = np.sqrt(np.maximum(sd ** 2 - rho ** 2, 1e-6))
    shared = rng.normal(size=(NS, 3)) * rho
    sim = mu[None, :] + shared[:, grp] + rng.normal(size=(NS, n)) * base[None, :]
    order = np.argsort(-sim, axis=1)
    pos = g.positionFinish.values
    out = {}
    w = np.where(pos == 1)[0]
    if len(w) != 1:
        return None
    win = np.bincount(order[:, 0], minlength=n) / NS
    pw = (win + 1e-4) / (win + 1e-4).sum()
    out['win'] = float(np.log(pw[w[0]]))
    k = M.places_for(n)
    if k:
        pl = np.zeros(n)
        for j in range(k):
            pl += np.bincount(order[:, j], minlength=n)
        pl = np.clip(pl / NS, 1e-3, 1 - 1e-3)
        placed = (pos <= k) & (pos >= 1)
        out['place'] = float(np.sum(np.where(placed, np.log(pl), np.log(1 - pl))) / n)
    a, b, c, d4 = (np.where(pos == i)[0] for i in (1, 2, 3, 4))
    if len(a) == 1 and len(b) == 1:
        key = np.sort(order[:, :2], axis=1)
        cnt = np.bincount(key[:, 0] * n + key[:, 1], minlength=n * n)
        x, y = sorted((a[0], b[0]))
        out['quin'] = float(np.log((cnt[x * n + y] + 0.5) / (NS + 0.5 * n * (n - 1) / 2)))
        if len(c) == 1 and n >= 5:
            t3 = np.sort(order[:, :3], axis=1)
            key3 = t3[:, 0] * n * n + t3[:, 1] * n + t3[:, 2]
            u, ct = np.unique(key3, return_counts=True)
            tri = sorted((a[0], b[0], c[0]))
            kk = tri[0] * n * n + tri[1] * n + tri[2]
            cc = ct[u == kk][0] if (u == kk).any() else 0
            out['tri'] = float(np.log((cc + 0.5) / (NS + 0.5 * n * (n - 1) * (n - 2) / 6)))
    return out


def main():
    d, me, shape_sd = M.prepare()
    base_c = ['wpr_1', 'wpr_2', 'wpr_3', 'wpr_m3', 'wpr_m5', 'days']
    style_c = ['e_1', 'e_2', 'e_3', 'e_m3', 'e_m5', 'l_1', 'l_2', 'l_3', 'l_m3', 'l_m5', 'close_m3', 'sect_i_time_m3', 'sect_i_l200_1']
    C = [c + '_dm' for c in base_c + style_c] + ['distance', 'field_size', 'gnum', 'pace_pressure', 'e_rank', 'l_rank']
    tr, va, te = d[d.date < '2025-01-01'], d[(d.date >= '2025-01-01') & (d.date < '2025-07-01')], d[d.date >= '2025-07-01'].copy()
    m = M.fit(tr, va, C)
    va = va.assign(pC=m.predict(va[C], num_iteration=m.best_iteration))
    te['pC'] = m.predict(te[C], num_iteration=m.best_iteration)
    sdC = np.array([float((va.wpr_dm - va.pC)[M.bucket(va.nprior.values) == b].std()) for b in range(3)])
    print('rows', len(d), 'test races', te.race_id.nunique(), 'noise sd by bucket', np.round(sdC, 2), flush=True)
    res = {r: {} for r in RHOS}
    for rid, g in te.groupby('race_id', sort=False):
        if len(g) < 4:
            continue
        mu, sd = g.pC.values, sdC[M.bucket(g.nprior.values)]
        for r in RHOS:
            o = race_scores(g, sd, r, mu)
            if o is None:
                break
            res[r][rid] = o
    for r in RHOS:
        print(f'rho {r:3.1f}', {k: round(float(np.mean([v[k] for v in res[r].values() if k in v])), 4) for k in ('win', 'place', 'quin', 'tri')}, flush=True)
    print('\npaired gain over rho 0 (mean, standard error, races):')
    for r in RHOS[1:]:
        row = {}
        for k in ('win', 'place', 'quin', 'tri'):
            ids = [i for i in res[0] if i in res[r] and k in res[0][i] and k in res[r][i]]
            dlt = np.array([res[r][i][k] - res[0][i][k] for i in ids])
            row[k] = f'{dlt.mean():+.4f} +-{dlt.std() / np.sqrt(len(dlt)):.4f}'
        print(f'rho {r:3.1f}', row, flush=True)


if __name__ == '__main__':
    main()
