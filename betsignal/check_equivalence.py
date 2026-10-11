"""Proves serve_features (state-based, used live) reproduces batch_features (reference, used for training) on the first race day
after a cutoff. usage: python betsignal/check_equivalence.py"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import numpy as np, pandas as pd
from betsignal import features as F

H = F.load_history()
cats = F.categories(H)
last = H.date.max()
cut = last - pd.Timedelta(days=30)
hist = H[H.date <= cut]
nxt = H[H.date > cut].date.min()
day = H[H.date == nxt]
print('history through', hist.date.max().date(), 'test day', nxt.date(), 'rows', len(day), 'races', day.race_id.nunique())
state = F.build_state(hist)
B = F.batch_features(H, cats)
B = B[B.date == nxt].set_index(['race_id', 'horse_id'])
U = day.copy()
U['horse_age'] = np.nan; U['horse_sex'] = np.nan   # force the live fallback for age/sex
S = F.serve_features(U, state, cats).set_index(['race_id', 'horse_id'])
bad = 0
for c in F.FEATURES:
    a, b = B[c].reindex(S.index), S[c]
    both = a.notna() & b.notna()
    mism = (a.notna() != b.notna()).sum()
    diff = (a[both] - b[both]).abs()
    tol = 1e-6 * (1 + a[both].abs())
    nbad = int((diff > tol).sum())
    flag = '' if (mism == 0 and nbad == 0) else '   <-- DIFF'
    if flag: bad += 1
    print(f'{c:16} null-mismatch {mism:4d}  value-mismatch {nbad:4d}  max|diff| {diff.max() if len(diff) else 0:.2e}{flag}')
print('\nFEATURES WITH DIFFERENCES:', bad)
