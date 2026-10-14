"""Out-of-sample projection-model predictions for 2025-07 onward (14 Oct 2026), for the selective-value comparison.
Same recipe as projection/train_main.py validation: main model (linear anchor + LightGBM correction, 179 features) trained on runs before 2025,
early-stopped on 2025-01..06, scored on 2025-07 onward. ONE seed (the shipped model uses 5), no suitability or weight term, runners with fewer than
3 prior rated runs are not projected. Writes a pickle with race_id, horse_id, date, proj. usage: python wpr_projection_oos_preds.py out.pkl"""
import os, sys
import numpy as np, pandas as pd
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'projection'))
import features as F
import train_main as TM

out = sys.argv[1]
feats = TM.ORIGINAL + F.LADDER_FEATURES
L = TM.assemble()
L = L[(L.nruns >= 3) & L[TM.BASE].notna().all(axis=1) & L.wpr.notna() & (L.date >= '2018-01-01')].copy()
tr, va, te = L[L.date < '2025-01-01'], L[(L.date >= '2025-01-01') & (L.date < '2025-07-01')], L[L.date >= '2025-07-01'].copy()
print('rows', len(L), 'train/valid/test', len(tr), len(va), len(te), flush=True)
m, coef = TM.fit(tr, feats, None, 1, valid=va)
te['proj'] = np.c_[np.ones(len(te)), te[TM.BASE].values] @ coef + m.predict(te[feats], num_iteration=m.best_iteration)
err = te.wpr - te.proj
print(f'RMSE {np.sqrt((err ** 2).mean()):.4f} bias {err.mean():+.3f} best_iter {m.best_iteration}', flush=True)
cols = [c for c in ('race_id', 'horse_id', 'run_id', 'date', 'proj', 'wpr') if c in te.columns]
te[cols].to_pickle(out)
print('saved', len(te), cols)
