"""How did the win model (research/cup_winner_test.py, fitted on 2800m+ races that are NOT Cups) pick the top 4 of the 2020-25 Cups?  (2 Nov 2026)
Run with: PYTHONPATH=.:projection python research/cup_top4_model_test.py
Per Cup: model rank of the 1st..4th finishers among the gradable runners (3+ earlier results-file rated runs), how many of the real top 4 sit in the model's top 4 / 6 / 8,
against last-3 average alone and the starting price (ranked over the same runners), and what random would give.  Ungradable finishers (mostly internationals) are counted separately.
Read-only."""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..')); sys.path.insert(0, os.path.join(HERE, '..', 'projection'))
os.environ.setdefault('PROJECTION_RATINGS', 'toprate')
import numpy as np, pandas as pd
import cup_group_test as G
import cup_winner_test as W
from sklearn.linear_model import LogisticRegression
from sklearn.preprocessing import StandardScaler

t = G.build(); t['act'] = t.wpr + t.off; t = W.prep(t)
N = t[~t.cup & (t.n >= 3)].dropna(subset=['gap3', 'last_frac', 'wt_rel']).copy()
F = W.FEATS; med = N[F].median()
sc = StandardScaler().fit(N[F].fillna(med)); lr = LogisticRegression(C=0.3, max_iter=500).fit(sc.transform(N[F].fillna(med)), N.win)
allC = t[t.cup].copy()
C = allC[allC.n >= 3].dropna(subset=['gap3', 'last_frac', 'wt_rel']).copy()
C['s'] = lr.decision_function(sc.transform(C[F].fillna(med)))
C['rk_model'] = C.groupby('date').s.rank(ascending=False, method='min')
C['rk_l3'] = C.groupby('date').last3.rank(ascending=False, method='min')
C['rk_sp'] = C.groupby('date').priceStarting.rank(ascending=True, method='min')
rows = []
print(f'{"Cup":6s} {"gradable":>8s} {"top4 gradable":>13s} | model rank of 1st..4th | in model top 4/6/8 | last-3 top 4/6/8 | SP top 4/6/8 | random top 4/6/8')
tot = {k: np.zeros(3) for k in ('model', 'l3', 'sp', 'rand')}; ntop = 0
for dt, g in C.groupby('date'):
    fin = g[g.positionFinish <= 4].sort_values('positionFinish')
    ung = int(allC[(allC.date == dt) & (allC.n < 3) & (allC.positionFinish <= 4)].shape[0])
    def cap(col):
        return np.array([int((fin[col] <= k).sum()) for k in (4, 6, 8)])
    m, l, s = cap('rk_model'), cap('rk_l3'), cap('rk_sp')
    r = np.array([len(fin) * k / len(g) for k in (4, 6, 8)])
    for k, v in (('model', m), ('l3', l), ('sp', s), ('rand', r)):
        tot[k] += v
    ntop += len(fin)
    print(f'{dt.year:<6d} {len(g):8d} {len(fin):13d} | {" ".join(str(int(x)) for x in fin.rk_model):>22s} | {m[0]}/{m[1]}/{m[2]:<2d}              | {l[0]}/{l[1]}/{l[2]:<2d}          | {s[0]}/{s[1]}/{s[2]:<2d}      | {r[0]:.1f}/{r[1]:.1f}/{r[2]:.1f}   (ungradable top-4: {ung})')
print(f'\nTotal over 6 Cups, top-4 finishers that were gradable: {ntop}')
for k, lab in (('model', 'win model'), ('l3', 'last-3 average'), ('sp', 'starting price'), ('rand', 'random')):
    v = tot[k]
    print(f'  {lab:15s} captured in its top 4 / 6 / 8: {v[0]:.1f} / {v[1]:.1f} / {v[2]:.1f}   ({100 * v[0] / ntop:.0f}% / {100 * v[1] / ntop:.0f}% / {100 * v[2] / ntop:.0f}% of the gradable top-4 finishers)')
# exact first-four and quinella / trifecta
print('\nBoxed bets inside the model\'s top N (gradable runners only): all of the first 2 / 3 / 4 finishers in the top N')
for N_ in (4, 6, 8):
    out = []
    for need in (2, 3, 4):
        h = 0; n = 0
        for dt, g in C.groupby('date'):
            fin = g[g.positionFinish <= need]
            if len(fin) < need or int(allC[(allC.date == dt) & (allC.positionFinish <= need)].shape[0]) > len(fin):
                continue           # an ungradable runner is among them: cannot be tested
            n += 1; h += int((fin.rk_model <= N_).all())
        out.append(f'{h}/{n}')
    print(f'  top {N_}: quinella {out[0]}, trifecta {out[1]}, first four {out[2]} (Cups where every placegetter was gradable)')
