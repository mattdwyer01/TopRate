"""Winner test for a draw term on the live Proj (27 Oct 2026). Uses the held-out misses saved by proj_draw_residual.py.
Draw slopes (pooled and venue x distance band, shrunk K=400) are fitted on the 2026-01..06 misses; the softmax scale is fitted on 2026-01..06 too; races of 2026-07 on are scored.
A race here is the group of page-store runners of the same date, venue and distance (the store holds only part of each field); only groups of 4+ runners with exactly one winner count.
Run: python research/proj_draw_winner_test.py OUTDIR"""
import sys, numpy as np, pandas as pd
te = pd.read_pickle(sys.argv[1] + '/proj_resid_te.pkl')
te['proj'] = te.f + te.c1
te['won'] = (pd.to_numeric(te.positionFinish, errors='coerce') == 1).astype(int)
g = te.groupby('grp'); te = te[(g.won.transform('sum') == 1) & (g.won.transform('size') >= 4)].copy()
a, b = te[te.date < '2026-07-01'], te[te.date >= '2026-07-01'].copy()
def slope(x):
    xc = x.bf - x.bf.mean(); return (xc * x.ed).sum() / (xc ** 2).sum()
K = 400.0
tab = {k: slope(z) * len(z) / (len(z) + K) for k, z in a.groupby(['vk', 'band']) if len(z) >= 30}
gb = slope(a)
def ll(x, col, beta):
    s = 0; per = []
    for _, z in x.groupby('grp'):
        e = beta * z[col].values; e = e - e.max(); p = np.exp(e) / np.exp(e).sum(); v = np.log(p[z.won.values == 1][0]); per.append(v)
    return np.array(per)
a = a.copy(); a['p0'] = a.proj
beta = max(np.linspace(0.05, 0.4, 36), key=lambda t: ll(a, 'p0', t).sum())
b['p0'] = b.proj
b['p1'] = b.proj + gb * b.bf
b['p2'] = b.proj + np.array([tab.get((v, bd), 0.0) * x for v, bd, x in zip(b.vk, b.band, b.bf)])
base = ll(b, 'p0', beta)
print(f'{b.grp.nunique()} scored races, {len(b)} runners, softmax beta {beta:.2f} (fit on 2026-01..06); pooled slope {gb:+.2f}')
print(f'winner log-lik per race: Proj {base.mean():.4f}')
for lab, col in (('+ pooled draw term', 'p1'), ('+ venue x band draw term', 'p2')):
    d = ll(b, col, beta) - base
    print(f'{lab}: {ll(b, col, beta).mean():.4f}  paired gain {d.mean():+.4f} (se {d.std() / np.sqrt(len(d)):.4f})')
