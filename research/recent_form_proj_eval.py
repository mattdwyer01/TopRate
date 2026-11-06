"""6 Nov 2026: held-out cost of the recent-form Proj (projection/breakdown.rf_parts) against the transparent formula, on 2026 page runs with 3+ earlier runs (breakdown.training_frame).
The deduction coefficients come from models_tr/transparent.json (fitted to 2026-11-05), so this slightly flatters both rows equally. Run: PYTHONPATH=.:projection python research/recent_form_proj_eval.py"""
import json, sys, numpy as np, pandas as pd
sys.path.insert(0, 'projection'); import breakdown as BK
mdl = json.load(open(BK.MODEL)); X = BK.training_frame(); X = X[X.date >= pd.Timestamp('2026-01-01')].copy()
co = np.array([mdl['coef'][f] for f in BK.FE])
def tf(f):
    parts = {g: sum(mdl['coef'][k] * f[k] for k in ks) for g, ks in BK.GROUPS.items()}
    parts = {g: (np.clip(v, -BK.CAPS[g], BK.CAPS[g]) if g in BK.CAPS else v) for g, v in parts.items()}
    return sum(mdl['coef'][f'c{k}'] * f[f'c{k}'] for k in range(1, 7)) + mdl['intercept'] + sum(parts.values())
X['tf'] = X.apply(tf, axis=1); X['rf'] = X.apply(lambda f: BK.rf_parts(f, mdl)[3], axis=1)
for nm in ('tf', 'rf'):
    e = X.y - X[nm]
    print(f'{nm}: n={len(X)} RMSE {np.sqrt((e**2).mean()):.3f} MAE {e.abs().mean():.3f} mean miss {e.mean():+.2f} median {e.median():+.2f} within 6 {100*(e.abs()<=6).mean():.1f}%')
g = X.c1 - X[['c4', 'c5', 'c6']].mean(axis=1)
for lo, hi in ((-99, 0), (0, 5), (5, 10), (10, 99)):
    a = X[g.between(lo, hi, inclusive='left')]
    print(f'  last clean run minus runs 4-6 in [{lo},{hi}): n={len(a):6d}  median miss tf {(a.y-a.tf).median():+.2f}  rf {(a.y-a.rf).median():+.2f} | mean tf {(a.y-a.tf).mean():+.2f} rf {(a.y-a.rf).mean():+.2f}')
