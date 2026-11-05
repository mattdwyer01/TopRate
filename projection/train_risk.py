"""Bad-run risk model (5 Nov 2026): the chance a runner's rating comes in more than BAD points below its formula figure (the heavy lower tail of the Proj's miss).
Same runner-page ATW inputs as the context model (ctx.FEATS, no price: the owner's rule is no market in Proj), LightGBM classifier. Display only: it is not part of Proj or the Rating.
Held-out check (fit before --fit-end, early stop on the three months before it, report on the rest) then a refit on every run; writes models_tr/risk_model.txt and risk.json.
Basis: research/bad_run_risk.py (AUC 0.696 with the live inputs, 0.712 with the early price, which is not used here).
Run: PYTHONPATH=. python projection/train_risk.py"""
import argparse, json, os, sys
import lightgbm as lgb
import numpy as np
import pandas as pd
from sklearn.metrics import roc_auc_score

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ctx as C  # noqa: E402

BAD = 12.0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--fit-end', default='2026-01-01')
    ap.add_argument('--es-from', default='2025-10-01')
    a = ap.parse_args()
    rp = C.training_frame_rel(False)
    pg = rp[rp.f.notna()].copy()
    meta = json.load(open(os.path.join(C.M, 'ctx.json')))
    pg['cls_c'] = C._cls(pg.cls, meta['classes'])
    feats = [c for c in C.FEATS]
    pg['bad'] = (pg.resid < -BAD).astype(int)
    cut, es = pd.Timestamp(a.fit_end), pd.Timestamp(a.es_from)
    tr, va, te = pg[pg.date < es], pg[(pg.date >= es) & (pg.date < cut)], pg[pg.date >= cut]
    params = dict(n_estimators=3000, learning_rate=0.03, num_leaves=15, min_child_samples=200, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=10, verbose=-1)
    m = lgb.LGBMClassifier(**params).fit(tr[feats], tr.bad, eval_set=[(va[feats], va.bad)], callbacks=[lgb.early_stopping(100, verbose=False)])
    p = m.predict_proba(te[feats])[:, 1]
    print(f'trees {m.best_iteration_} base rate {te.bad.mean():.3f} AUC {roc_auc_score(te.bad, p):.3f} predicted mean {p.mean():.3f} (held out n={len(te)})')
    q = pd.qcut(p, 10, labels=False, duplicates='drop')
    cal = pd.DataFrame({'q': q, 'p': p, 'y': te.bad.values}).groupby('q').agg(pred=('p', 'mean'), actual=('y', 'mean'), n=('y', 'size')).round(3)
    print(cal.to_string())
    for lab, sel in (('3-5 runs', te.n.between(3, 5)), ('6-9', te.n.between(6, 9)), ('10+', te.n >= 10), ('1-2', te.n <= 2)):
        s = sel.values
        if s.sum() > 500 and te.bad[s].nunique() > 1:
            print(f'{lab:9s} n={s.sum():6d} AUC {roc_auc_score(te.bad[s], p[s]):.3f} base {te.bad[s].mean():.3f} pred {p[s].mean():.3f}')
    fin = lgb.LGBMClassifier(**{**params, 'n_estimators': int(m.best_iteration_ * 1.15)}).fit(pg[feats], pg.bad)
    fin.booster_.save_model(os.path.join(C.M, 'risk_model.txt'))
    json.dump({'feats': feats, 'bad_points': BAD, 'base_rate': round(float(pg.bad.mean()), 4), 'trained_to': str(pg.date.max().date()),
               'held_out_auc': round(float(roc_auc_score(te.bad, p)), 4), 'held_out_base_rate': round(float(te.bad.mean()), 4)}, open(os.path.join(C.M, 'risk.json'), 'w'), indent=1)
    print('written risk_model.txt, risk.json')


if __name__ == '__main__':
    main()
