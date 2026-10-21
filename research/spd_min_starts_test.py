"""Speed rating for a horse with ONE earlier figure, and the Rank weights when Spd is missing (21 Oct 2026). Run with PYTHONPATH=.
Part A: target = the run's wpr minus the race mean (results files, plain wpr: this tests the speed rating itself, not Proj); predictor = the speed rating before the run,
demeaned in race, by the number of earlier figures the horse has (1, 2, 3 to 5, 6+). Fit before 2025, scored 2025-07+: slope (how much of a point of rating shows up in the next
run), correlation and RMSE gain. A slope well under the 6+ slope at 1 earlier figure means the rating should be shrunk there, not dropped.
Part B: race-level conditional logit on Proj + Nett only (no Spd) over every race that has both, against the shipped 0.65 / 0.25 weights renormalised (0.722 / 0.278)."""
import os, sys
import numpy as np
import pandas as pd
sys.path.insert(0, os.path.dirname(__file__))
import speed_extras_study as ex
import speed_figure_study as sf
import speed_figure_study2 as s2
SEC = sf.SEC

def part_a():
    d = sf.load()
    r = s2.races_table(d)
    r['par'] = s2.fit_par(r)
    dev = r.winners_time - r.par
    r['fast'] = -(dev - ex.variant(r, dev)) / SEC
    d = d.merge(r[['race_id', 'fast']], on='race_id', how='left')
    d['sp'] = d.fast - d.marginFinish.clip(lower=0, upper=25)
    d = d.dropna(subset=['sp']).sort_values(['horse_id', 'date']).reset_index(drop=True)
    g = d.groupby('horse_id', sort=False)
    d['n'] = g.cumcount()
    d['R'] = g['sp'].transform(lambda s: s.shift(1).ewm(halflife=4.0, min_periods=1).mean())
    d['T'] = d.wpr - d.groupby('race_id').wpr.transform('mean')
    sz = d.groupby('race_id').race_id.transform('size')
    u = d[(sz >= 5) & d['T'].notna() & d.R.notna()].copy()
    u['R_d'] = u.R - u.groupby('race_id').R.transform('mean')
    u['b'] = pd.cut(u.n, [0, 1, 2, 5, 10_000], labels=['1 earlier', '2 earlier', '3-5 earlier', '6+ earlier'])
    print('Part A: slope of next-run rating (race-demeaned) on the speed rating (race-demeaned, lengths); rating pts per length expected ~1')
    for lab, a in (('fit before 2025', u[u.date < '2025-01-01']), ('test 2025-07+', u[u.date >= '2025-07-01'])):
        print(' ', lab)
        for b, x in a.groupby('b', observed=True):
            xx = x.R_d.values; yy = x['T'].values
            slope = float((xx * yy).sum() / (xx * xx).sum()); c = float(np.corrcoef(xx, yy)[0, 1])
            rm0 = float(np.sqrt(np.mean(yy ** 2))); rm1 = float(np.sqrt(np.mean((yy - slope * xx) ** 2)))
            print(f'    {str(b):12s} n={len(x):7d} slope {slope:5.2f} corr {c:5.3f} RMSE {rm0:5.2f} -> {rm1:5.2f} ({100*(rm0-rm1)/rm0:4.1f}%)')

def part_b():
    import runpy
    src = open(os.path.join(os.path.dirname(__file__), 'rank_weights.py')).read().split('SIG = {')[0]
    ns = {'__name__': 'rw'}
    exec(compile(src, 'rank_weights_head', 'exec'), ns)
    d = ns['d']
    from scipy.optimize import minimize
    for c in ('wpr_nett', 'wprp_proj'):
        d[c] = pd.to_numeric(d[c], errors='coerce')
    d = d.dropna(subset=['wpr_nett', 'wprp_proj'])
    d = d[d.groupby('rk').won.transform('size') >= 5].copy()
    for k, c in (('Nett', 'wpr_nett'), ('Proj', 'wprp_proj')):
        g = d.groupby('rk')[c]
        d['z_' + k] = (d[c] - g.transform('mean')) / g.transform('std').replace(0, np.nan)
    d = d.dropna(subset=['z_Nett', 'z_Proj']).copy()
    d['rkid'] = d.rk.astype('category').cat.codes
    print(f'\nPart B: {d.rkid.nunique()} races with Proj and Nett (no Spd required)')
    def nll(w, df):
        s = df[['z_Proj', 'z_Nett']].values @ w
        t = df.assign(s=s); m = t.groupby('rkid').s.transform('max'); e = np.exp(t.s - m)
        lse = np.log(e.groupby(t.rkid).transform('sum')) + m
        return -(t.s - lse)[t.won == 1].mean()
    def top(w, df):
        t = df.assign(s=df[['z_Proj', 'z_Nett']].values @ w)
        return t.loc[t.groupby('rkid').s.idxmax()].won.mean() * 100
    dates = sorted(d.date.unique()); half = dates[len(dates) // 2]
    A, B = d[d.date < half], d[d.date >= half]
    # scale: fitted logit scale k times the share; compare shares at the best common scale
    def fit(df):
        return minimize(nll, np.array([0.3, 0.1]), args=(df,), method='L-BFGS-B').x
    res = {}
    for lab, share in (('shipped renormalised 0.722 / 0.278', 0.278), ('Nett 0.35', 0.35), ('Nett 0.40', 0.40), ('Nett 0.50', 0.50), ('Nett 0.00 (Proj only)', 0.0)):
        out = []
        for tr, te in ((A, B), (B, A)):
            w0 = fit(tr); k = w0.sum()
            w = np.array([k * (1 - share), k * share])   # keep the fitted overall scale, set the split
            out.append((-nll(w, te), top(w, te)))
        res[lab] = (np.mean([o[0] for o in out]), np.mean([o[1] for o in out]))
        print(f'  {lab:36s} winner LL {res[lab][0]:.4f}  top pick {res[lab][1]:.1f}%')
    wf = [fit(tr) for tr in (A, B)]
    print('  freely fitted Nett share of the Proj + Nett weight (each half):', [round(float(w[1] / w.sum()), 3) for w in wf], 'all:', round(float(fit(d)[1] / fit(d).sum()), 3))

if __name__ == '__main__':
    part_a()
    part_b()
