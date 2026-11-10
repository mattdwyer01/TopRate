import json, gzip, glob, numpy as np, pandas as pd
from scipy.optimize import minimize
W = './'  # run from the repo root on a current main
r = pd.read_csv(W + 'runners.csv', low_memory=False, usecols=['run_id','race_id','date','venue','race','horse','tab_number','start_time','scratched','finish_position','won','starting_price_sp','fixed_win_price','wprp_proj','wprp_made','wprp_model','weight_carried'])
r = r[(r.date >= '2026-10-16') & (r.date <= '2026-11-09')]
r = r[pd.to_numeric(r.scratched, errors='coerce').fillna(0) == 0]
r['fin'] = pd.to_numeric(r.finish_position, errors='coerce'); r['sp'] = pd.to_numeric(r.starting_price_sp, errors='coerce')
r['P'] = pd.to_numeric(r.wprp_proj, errors='coerce')
st = pd.to_datetime(r.start_time, errors='coerce', utc=True); mk = pd.to_datetime(r.wprp_made, errors='coerce', utc=True)
r['pre'] = (mk <= st) | mk.isna()
# direct scores
dm = {}
for f in glob.glob(W + 'data/direct_scores/*.json*'):
    x = json.load(gzip.open(f)) if f.endswith('gz') else json.load(open(f))
    for rid, d in x.get('races', {}).items():
        for tab, p in d.items(): dm[(int(rid), int(tab))] = p
r['dm'] = [dm.get((int(a), int(b))) if pd.notna(a) and pd.notna(b) else None for a, b in zip(r.race_id, r.tab_number)]
r['dm'] = pd.to_numeric(r.dm, errors='coerce')
# early prices
ph = pd.read_csv(W + 'toprate_price_history.csv', low_memory=False); ph['t'] = pd.to_datetime(ph.snapshot_time, errors='coerce', utc=True)
ph = ph.merge(r[['run_id']].assign(st=st), on='run_id'); ph['mins'] = (ph.st - ph.t).dt.total_seconds() / 60
def early(m):
    q = ph[(ph.mins >= m) & (ph.fixed_win_price > 1)].sort_values('t').groupby('run_id').fixed_win_price.last(); return q
r['e30'] = r.run_id.map(early(30)); r['e10'] = r.run_id.map(early(10)); r['e60'] = r.run_id.map(early(60))
# race filter: one winner, every runner a Proj and SP, 5+ runners
g = r.groupby('race_id')
ok = (g.fin.transform(lambda s: (s == 1).sum()) == 1) & g.P.transform(lambda s: s.notna().all()) & (g.P.transform('size') >= 5) & g.sp.transform(lambda s: (s > 1).all())
R = r[ok].copy(); R['won'] = (R.fin == 1).astype(int)
R['book'] = R.groupby('race_id').sp.transform(lambda s: (1 / s).sum()); R = R[(R.book >= 1.05) & (R.book <= 2.0)]
print(f'live races 16 Oct to 9 Nov with Proj, SP, one winner: {R.race_id.nunique()}, runners {len(R)}; Proj made before the jump {R.pre.mean():.1%}')
R['half'] = (pd.to_datetime(R.date) >= pd.to_datetime(R.date).median()).astype(int)
def cl(S, X):
    gid = S.race_id.astype('category').cat.codes.values; y = S.won.values; X = np.column_stack(X); out = []; bs = []
    for h in (0, 1):
        tr = np.where(S.half.values != h)[0]; te = np.where(S.half.values == h)[0]
        def ll(b, idx):
            z = X[idx] @ b; z = z - pd.Series(z).groupby(gid[idx]).transform('max').values; e = np.exp(z)
            return -(np.log(e / pd.Series(e).groupby(gid[idx]).transform('sum').values)[y[idx] == 1]).mean()
        b = minimize(ll, np.r_[1.0 if X.shape[1] and abs(X[:,0]).max() < 20 else 0.2, np.zeros(X.shape[1] - 1)], args=(tr,), method='L-BFGS-B').x; bs.append(b)
        z = X[te] @ b; z = z - pd.Series(z).groupby(gid[te]).transform('max').values; e = np.exp(z)
        p = e / pd.Series(e).groupby(gid[te]).transform('sum').values
        out.append(pd.Series(np.log(p)[y[te] == 1], index=gid[te][y[te] == 1]))
    return pd.concat(out).sort_index(), bs
G = lambda a, b: f'{(b - a).mean():+.4f} (se {(b - a).std() / np.sqrt(len(a)):.4f})'
dem = lambda S, c: (S[c] - S.groupby('race_id')[c].transform('mean')).values

print('\n=== TEST 4: finishing-position blend on live races ===')
D = R[R.groupby('race_id').dm.transform(lambda s: s.notna().all())].copy()
D['ldm'] = np.log(D.dm.clip(1e-4))
print(f'races where every runner has a direct score: {D.race_id.nunique()}')
p0, b0 = cl(D, [dem(D, 'P')]); print(f'  Proj alone {p0.mean():.4f} (scale {b0[0][0]:.3f})')
d0, _ = cl(D, [dem(D, 'ldm')]); print(f'  direct alone {d0.mean():.4f}  vs Proj {G(p0, d0)}')
for s in (0.3, 0.5, 0.7):
    v = (1 - s) * dem(D, 'P') + s * 5 * dem(D, 'ldm'); D['v'] = v
    q, _ = cl(D, [v]); print(f'  blend {int(s*100)}% direct (dashboard formula) {q.mean():.4f}  vs Proj {G(p0, q)}')
f2, b2 = cl(D, [dem(D, 'P'), dem(D, 'ldm')]); print(f'  free fit both {f2.mean():.4f} vs Proj {G(p0, f2)}  weights {np.round(b2[0],3)}')
for nm, c in (('Proj', 'P'), ('direct', 'dm')):
    top = D.loc[D.groupby('race_id')[c].idxmax()]; print(f'  top pick {nm}: wins {top.won.mean():.1%}, avg SP {top.sp.mean():.2f}, flat ROI at SP {(top.won * top.sp).sum() / len(top) - 1:+.1%}')
D['lm'] = np.log((1 / D.sp) / D.groupby('race_id').sp.transform(lambda s: (1 / s).sum()))
m0, _ = cl(D, [dem(D, 'lm')]); m1, _ = cl(D, [dem(D, 'lm'), dem(D, 'P')]); m2, _ = cl(D, [dem(D, 'lm'), dem(D, 'P'), dem(D, 'ldm')])
print(f'  against SP: market {m0.mean():.4f}; + Proj {G(m0, m1)}; + Proj + direct {G(m0, m2)}')

print('\n=== TEST 2: market keener than Proj, at early prices (3 to 9 Nov price snapshots) ===')
for col, lab in (('e60', '60 min'), ('e30', '30 min'), ('e10', '10 min')):
    E = R[R.groupby('race_id')[col].transform(lambda s: s.notna().all())].copy()
    if E.race_id.nunique() < 50: print(lab, 'too few races', E.race_id.nunique()); continue
    E['ip'] = 1 / E[col]; E['mp'] = E.ip / E.groupby('race_id').ip.transform('sum')
    E['Prank'] = E.groupby('race_id').P.rank(ascending=False, method='min'); E['Mrank'] = E.groupby('race_id')[col].rank(method='min')
    E['firm'] = np.log(E[col] / E.sp)   # + = shortened from early to SP
    print(f'\n {lab} before: {E.race_id.nunique()} races, {len(E)} runners')
    for nm, m in (('market 3+ places keener than Proj', (E.Prank - E.Mrank) >= 3), ('market 1-2 keener', (E.Prank - E.Mrank).between(1, 2)),
                  ('agree', E.Prank == E.Mrank), ('Proj 3+ places keener than market', (E.Mrank - E.Prank) >= 3),
                  ('Proj top pick', E.Prank == 1), ('Proj top pick, market keener on another', (E.Prank == 1) & (E.Mrank >= 3))):
        s = E[m]
        if len(s) < 30: continue
        print(f'   {nm:42s} n {len(s):4d} wins {s.won.mean():5.1%} vs early-implied {s.mp.mean():5.1%} | ROI early {(s.won * s[col]).sum() / len(s) - 1:+6.1%}  at SP {(s.won * s.sp).sum() / len(s) - 1:+6.1%}  (ex3 early {((s.won * s[col]).sum() - s[s.won == 1][col].nlargest(3).sum()) / len(s) - 1:+.1%})')
    # firming
    print('   price move from early to SP (shortened = firmed):')
    E['mv'] = pd.cut(E.firm, [-9, -0.2, -0.05, 0.05, 0.2, 9], labels=['drifted 20%+', 'drifted 5-20%', 'steady', 'firmed 5-20%', 'firmed 20%+'])
    for k, s in E.groupby('mv', observed=True):
        print(f'     {k:14s} n {len(s):4d} wins {s.won.mean():5.1%} vs early-implied {s.mp.mean():5.1%}  ROI at early price {(s.won * s[col]).sum() / len(s) - 1:+6.1%}')
    a, _ = cl(E, [dem(E, 'mp').clip(-1, 1) * 0 + np.log(E.mp.values) - pd.Series(np.log(E.mp.values)).groupby(E.race_id.values).transform('mean').values])
    lme = np.log(E.mp.values) - pd.Series(np.log(E.mp.values)).groupby(E.race_id.values).transform('mean').values
    a1, _ = cl(E, [lme, dem(E, 'P')])
    print(f'   early market {a.mean():.4f}; + Proj {G(a, a1)}')
    if E.dm.notna().all() or E.groupby('race_id').dm.transform(lambda s: s.notna().all()).mean() > 0.5:
        E2 = E[E.groupby('race_id').dm.transform(lambda s: s.notna().all())].copy(); E2['ldm'] = np.log(E2.dm.clip(1e-4))
        lme2 = np.log(E2.mp.values) - pd.Series(np.log(E2.mp.values)).groupby(E2.race_id.values).transform('mean').values
        b_, _ = cl(E2, [lme2]); b1, _ = cl(E2, [lme2, dem(E2, 'P'), dem(E2, 'ldm')])
        print(f'   ({E2.race_id.nunique()} races with direct scores) early market {b_.mean():.4f}; + Proj + direct {G(b_, b1)}')
