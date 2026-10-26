"""Race-level scoring of the converted-history Proj test (26 Oct 2026): winner log-lik, top pick, finishing-order and margin agreement, within race.
Reads the pickle written by proj_converted_history.py. Races are proxied by (date, venue, distance, field size, class); the page store holds only some runners
of each race, so only races with 4+ stored runners and the winner among them are used (same convention as the other store-race tests).
Run: python research/proj_converted_score.py /tmp/proj_conv_test_1.0.pkl"""
import sys
import numpy as np, pandas as pd
from scipy.stats import spearmanr

d = pd.read_pickle(sys.argv[1])
d = d.dropna(subset=['positionFinish', 'marginFinish']).copy()
d['g'] = d.groupby(['date', 'vn', 'distance', 'field_size', 'cls'], dropna=False).ngroup()
d['win'] = (d.positionFinish == 1).astype(int)
d['mbeh'] = d.marginFinish.clip(lower=0)
k = d.groupby('g').agg(n=('win', 'size'), w=('win', 'sum'))
d = d[d.g.isin(k[(k.n >= 4) & (k.w == 1)].index)]
print('races', d.g.nunique(), 'runners', len(d))
MOD = ['p_formula', 'p_page', 'p_conv', 'p_both', 'p_live']
half = d.date >= d.date.median()
betas = np.arange(0.05, 0.5, 0.025)


def probs(df, col, beta):
    z = df[col] * beta
    z = z - z.groupby(df.g).transform('max')
    e = np.exp(z)
    return e / e.groupby(df.g).transform('sum')


def ll(df, col, beta):
    return float(np.log(probs(df, col, beta)[df.win == 1]).mean())


def per_race(m):
    out = []
    for a_, b_ in ((d[~half], d[half]), (d[half], d[~half])):
        bb = max(betas, key=lambda b: ll(a_, m, b))
        p = probs(b_, m, bb)
        w = b_.win == 1
        out.append(np.log(p[w]).set_axis(b_.g[w]))
    return pd.concat(out)


rows = []
for m in MOD:
    llv = per_race(m).mean()
    top = d.loc[d.groupby('g')[m].idxmax()]
    r = d.groupby('g')[m].rank(ascending=False, method='first')
    in3 = d[r <= 3].groupby('g').win.max().mean()
    dm = d[m] - d.groupby('g')[m].transform('mean')
    t = d.assign(dm=dm, fin=-d.positionFinish, mm=-(d.mbeh - d.groupby('g').mbeh.transform('mean')))
    sp = t.groupby('g').apply(lambda x: spearmanr(x.dm, x.fin)[0] if x.dm.nunique() > 1 and x.fin.nunique() > 1 else np.nan).mean()
    cm = float(np.corrcoef(t.dm, t.mm)[0, 1])
    sl = np.polyfit(t.dm, t.mm, 1)
    res = t.mm - np.polyval(sl, t.dm)
    rows.append(dict(model=m, winner_ll=llv, top_pick=top.win.mean(), win_in_top3=in3, spearman_finish=sp, margin_corr=cm, margin_rmse_L=float(np.sqrt((res ** 2).mean())), margin_mae_L=float(res.abs().mean())))
print(pd.DataFrame(rows).set_index('model').round(4).to_string())
base = per_race('p_page')
for m in ('p_conv', 'p_both', 'p_formula'):
    diff = per_race(m) - base
    print(f'{m} minus page-trained: winner ll {diff.mean():+.4f} (se {diff.std() / np.sqrt(len(diff)):.4f}) over {len(diff)} races')
