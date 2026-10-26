"""Per-horse trouble rate (26 Oct 2026): is getting into trouble a horse trait, and does a horse's earlier trouble rate predict a bad run beyond the live inputs?

Trouble flags come from the steward and video comments of each PAST run (slow away, checked or blocked, resented or keen, vet or lame, tailed off).  They are post-race
facts, so for today's run only the horse's EARLIER flags are used (strictly before the date, shrunk toward the field rate).
Part 1: persistence. Corr of a horse's earlier trouble rate with the NEXT run carrying the same flag (if low, trouble is run-day luck, not a trait).
Part 2: bad-run classifier (rating more than 12 below the formula) and mean model with the trouble rates added to the live inputs + bad-run history families (A B C D F),
same split as bad_run_risk.py (fit before 2025-10, early stop to 2026-01, scored on 2026).
  PYTHONPATH=. python research/trouble_rate_test.py
"""
import os
import re
import sys

import lightgbm as lgb
import numpy as np
import pandas as pd
from sklearn.metrics import roc_auc_score

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import bad_run_risk as B  # noqa: E402
C = B.C

FAM = {
    'slow': r'slow(ly)? (to )?(begin|away|out)|slowly away|missed the start|began awkwardly|dwelt|jumped (late|awkward)|awkward(ly)? (start|away)|fumbled|a bit slow out',
    'block': r'check(ed)?\b|blocked|held up|no room|shut off|denied a run|hampered|interfer|bumped|crowded|squeezed|clipped',
    'keen': r'resent|failed to|raced (very )?keen|over.?rac|pulled hard|laboured|fought|did not (try|extend|respond)|ungenuine',
    'vet': r'\bvet|lame|bled|bleed|arrhythm|cardiac|sore|broke down|pulled up|eased down|tailed off|\bfell\b|lost (its )?rider|unseat|tongue',
}
K = 5.0


def main():
    pg, fam = B.build()
    txt = pg.cmt.fillna('').str.lower()
    for k, p in FAM.items():
        pg['t_' + k] = txt.str.contains(p, regex=True).astype(float)
    pg['t_any'] = pg[['t_' + k for k in FAM]].max(axis=1)
    has = txt.str.len() > 0
    print(f'{len(pg):,} runs, with a comment {100*has.mean():.0f}%; trouble flag rate: ' + ', '.join(f'{k} {100*pg["t_"+k].mean():.1f}%' for k in list(FAM) + ['any']))
    pg = pg.sort_values(['horse_id', 'date']).reset_index(drop=True)
    g = pg.groupby('horse_id')
    new = []
    for k in list(FAM) + ['any']:
        f = pg['t_' + k]
        cs = g['t_' + k].cumsum() - f
        cn = g.cumcount()
        base = f.mean()
        pg['r_' + k] = (cs + base * K) / (cn + K)
        pg['n_' + k] = cs
        new += ['r_' + k, 'n_' + k]
    pg['r_last'] = g.t_any.shift(1)
    new.append('r_last')
    # part 1: persistence
    print('\npart 1: does an earlier trouble rate predict the NEXT run carrying the flag? (runs with 4+ earlier runs)')
    z = pg[g.cumcount() >= 4]
    for k in list(FAM) + ['any']:
        y = z['t_' + k]
        x = z['r_' + k]
        q = pd.qcut(x.rank(method='first'), 5, labels=False)
        rates = y.groupby(q).mean() * 100
        print(f'  {k:6s} corr {np.corrcoef(x, y)[0,1]:+.3f}   flag rate by earlier-rate quintile: ' + ' / '.join(f'{v:.1f}' for v in rates) + '%')
    # part 2
    classes = sorted(pg.cls.dropna().unique().tolist())
    pg['cls_c'] = C._cls(pg.cls, classes)
    cut, es = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')
    tr, va, te = pg[pg.date < es], pg[(pg.date >= es) & (pg.date < cut)], pg[pg.date >= cut].copy()
    P = dict(learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1)
    yb = pg.bad.astype(int)
    allf = list(C.FEATS) + fam['A'] + fam['B'] + fam['C'] + fam['D'] + fam['F']
    print(f'\ntrain {len(tr)}, valid {len(va)}, test {len(te)}')

    def run(cols, label):
        m = lgb.LGBMClassifier(n_estimators=3000, **P).fit(tr[cols], yb[tr.index], eval_set=[(va[cols], yb[va.index])], callbacks=[lgb.early_stopping(100, verbose=False)])
        p = m.predict_proba(te[cols])[:, 1]
        auc = roc_auc_score(te.bad.astype(int), p)
        t = te.assign(p=p)
        print(f'  {label:36s} AUC {auc:.4f}  riskiest decile {100*t.nlargest(len(t)//10,"p").bad.mean():5.1f}%  safest {100*t.nsmallest(len(t)//10,"p").bad.mean():4.1f}%  trees {m.best_iteration_}')
        return m
    print('bad-run classifier')
    run(allf, 'live inputs + A B C D F')
    run(allf + new, '+ trouble rates (all)')
    run(allf + ['r_any', 'n_any', 'r_last'], '+ any-trouble rate only')
    for k in FAM:
        run(allf + ['r_' + k, 'n_' + k], f'+ {k} rate')
    print('\nmean model (resid)')
    for cols, label in ((allf, 'live + A B C D F'), (allf + new, '+ trouble rates')):
        mr = lgb.LGBMRegressor(n_estimators=3000, objective='huber', alpha=4.0, **P).fit(tr[cols], tr.resid, eval_set=[(va[cols], va.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
        e = te.resid - mr.predict(te[cols])
        print(f'  {label:24s} RMSE {np.sqrt((e**2).mean()):.4f}  MAE {e.abs().mean():.4f}  median {e.median():+.2f}  trees {mr.best_iteration_}')


if __name__ == '__main__':
    main()
