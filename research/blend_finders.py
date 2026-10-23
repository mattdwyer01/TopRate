"""Rank blends judged on FINDING WINNERS AND THE TOP FOUR (22 Oct 2026), not log-likelihood over the whole field. Input: the dashboard-race frame dumped by blend_refit_final.py (DUMP_D): Proj out of sample (p_rel),
Nett, Spd today (spd, SPD_MODEL=0) and Spd rebuilt out of sample (spd2, falling back to today's where missing; spd2_real marks the real ones), finish_position and won. Each score ranks the runners of a race; a blend is a fixed
weighted mean of the within-race z-scores. Per race: winner is the #1 pick, winner in the top 2 / 3 / 4, how many of the actual first four finishers are in the model's top 4, and the share of races with 3+ of them, the quinella
(first two both in the top 4), the trifecta box (first three all in the top 5) and the first four box (all in the top 6). Only races where positions 1 to 4 are all known. Paired bootstrap over races for differences from the live 50/30/20.
Run: BLEND_D=<pickle> SPD_COV=0|0.9 python research/blend_finders.py"""
import os
import numpy as np, pandas as pd
d = pd.read_pickle(os.environ['BLEND_D'])
cov = float(os.environ.get('SPD_COV', '0'))
d['fp'] = pd.to_numeric(d.finish_position, errors='coerce')
g = d.groupby('rk')
d['pc'] = g.p_rel.transform(lambda s: s.notna().mean()); d['nc'] = g.nett.transform(lambda s: s.notna().mean()); d['sc'] = g.spd2_real.transform('mean')
D = d[(d.pc >= .8) & (d.nc >= .8) & (d.sc >= cov)].copy()
need = D.groupby('rk').fp.transform(lambda s: set([1, 2, 3, 4]).issubset(set(s.dropna().astype(int))))
D = D[need].copy()
for c in ('p_rel', 'nett', 'spd', 'spd2'):
    gm = D.groupby('rk')[c]; D['z_' + c] = ((D[c] - gm.transform('mean')) / gm.transform('std').replace(0, np.nan)).fillna(0.0)
print(f"{D.rk.nunique()} races with a known first four ({len(D)} runners), formula and Nett coverage 80%+, rebuilt Spd coverage >= {cov:.0%}\n")
def blend(wp, wn, ws, spd='spd2'):
    return wp * D.z_p_rel + wn * D.z_nett + ws * D['z_' + spd]
scores = {'Proj alone': D.z_p_rel, 'Nett alone': D.z_nett, 'Spd rebuilt alone': D.z_spd2, 'Spd today alone': D.z_spd,
          'Proj 50 / Nett 50': blend(.5, .5, 0), 'Proj 70 / Spd 30': blend(.7, 0, .3), 'Proj 60 / Spd 40': blend(.6, 0, .4), 'Proj 80 / Spd 20': blend(.8, 0, .2),
          '50/30/20 (live)': blend(.5, .3, .2), '45/30/25': blend(.45, .3, .25), '40/30/30': blend(.4, .3, .3), '40/35/25': blend(.4, .35, .25), '35/30/35': blend(.35, .3, .35),
          '60/25/15': blend(.6, .25, .15), '33/33/33': blend(1/3, 1/3, 1/3), '50/30/20 (Spd today)': blend(.5, .3, .2, 'spd')}
keys = D.rk.values; order = pd.Series(range(len(D)), index=D.index)
def per_race(score):
    t = pd.DataFrame({'rk': keys, 's': score.values, 'fp': D.fp.values})
    t['rank'] = t.groupby('rk').s.rank(ascending=False, method='first')
    out = {}
    for r_, x in t.groupby('rk', sort=False):
        top = x[x.fp.between(1, 4)].sort_values('fp')
        rk = dict(zip(top.fp.astype(int), top['rank'].astype(int)))
        hits = sum(1 for p in (1, 2, 3, 4) if rk[p] <= 4)
        out[r_] = (rk[1] == 1, rk[1] <= 2, rk[1] <= 3, rk[1] <= 4, hits, hits >= 3, rk[1] <= 4 and rk[2] <= 4, max(rk[1], rk[2], rk[3]) <= 5, max(rk.values()) <= 6)
    return pd.DataFrame.from_dict(out, orient='index', columns=['win1', 'win_t2', 'win_t3', 'win_t4', 'hits4', 'hits3p', 'quin', 'tri', 'f4']).astype(float)
res = {k: per_race(v) for k, v in scores.items()}
base = res['50/30/20 (live)']; rng = np.random.default_rng(1); idx = rng.integers(0, len(base), (500, len(base)))
cols = ['win1', 'win_t2', 'win_t3', 'win_t4', 'hits4', 'hits3p', 'quin', 'tri', 'f4']
print(f"{'blend':24s} {'#1 wins':>8s} {'win top2':>9s} {'win top3':>9s} {'win top4':>9s} {'of first 4 in top 4':>20s} {'3+ of 4':>8s} {'quinella':>9s} {'tri box 5':>10s} {'first4 box 6':>13s}")
for k, r in res.items():
    m = r[cols].mean()
    print(f"{k:24s} {100*m.win1:7.1f}% {100*m.win_t2:8.1f}% {100*m.win_t3:8.1f}% {100*m.win_t4:8.1f}% {m.hits4:19.3f} {100*m.hits3p:7.1f}% {100*m.quin:8.1f}% {100*m.tri:9.1f}% {100*m.f4:12.1f}%")
print('\ndifference from the live 50/30/20 in races-per-100 (paired bootstrap 90% range): #1 wins, winner in top 4, first four hits in top 4 (hits, not %), quinella')
for k, r in res.items():
    if k == '50/30/20 (live)': continue
    out = []
    for c, sc in (('win1', 100), ('win_t4', 100), ('hits4', 1), ('quin', 100)):
        dd = (r[c].values - base[c].values); bs = dd[idx].mean(axis=1) * sc
        out.append(f"{dd.mean()*sc:+6.2f} [{np.percentile(bs,5):+5.2f},{np.percentile(bs,95):+5.2f}]")
    print(f"{k:24s} " + '  '.join(out))
