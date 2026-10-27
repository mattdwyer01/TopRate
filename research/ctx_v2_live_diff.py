"""Which feature values make the live path differ from the training frame for the ~1% of runs that differ by more than 0.01 (27 Oct 2026). Same setup as ctx_v2_live_check.py,
but wraps lgb.Booster.predict to capture the frames the live path passes to the models and compares them with the training frame column by column.
Run: PYTHONPATH=.:projection:research python research/ctx_v2_live_diff.py [--days 12]"""
import argparse, json, os, sys
import numpy as np, pandas as pd, lightgbm as lgb
sys.path.insert(0, 'projection')
import ctx as C

ap = argparse.ArgumentParser(); ap.add_argument('--days', type=int, default=12); a = ap.parse_args()
meta = json.load(open(os.path.join(C.M, 'ctx.json')))
rp = C.training_frame_rel('jw' in meta['feats'])
sub = rp[rp.date > rp.date.max() - pd.Timedelta(days=a.days)].copy().reset_index(drop=True)
sub['cls_c'] = C._cls(sub.cls, meta['classes'])
has = sub.f.notna().values
use = has & (sub.n >= C.REL_MIN_RUNS).values
m0 = lgb.Booster(model_file=os.path.join(C.M, 'ctx_model.txt'))
m1 = lgb.Booster(model_file=os.path.join(C.M, 'ctx_rel_model.txt'))
train_corr = np.full(len(sub), np.nan)
train_corr[has] = m0.predict(sub.loc[has, meta['feats']])
train_corr[use] = m1.predict(sub.loc[use, meta['rel_feats']])
base = C.page_frame(); base['f'] = C.formula_pred(base, C.coefs()); base = C.context_columns(base); base['resid'] = base.wpr - base.f
T = sub[['horse_id', 'date', 'jockey', 'trainer', 'vn', 'distance', 'going', 'weightCarried', 'barrier', 'field_size', 'race_class', 'trackGrading', 'prize']].rename(columns={'vn': 'venue'})
cap = []
orig = lgb.Booster.predict
def spy(self, data, *args, **kw):
    cap.append(data.copy() if hasattr(data, 'copy') else data)
    return orig(self, data, *args, **kw)
lgb.Booster.predict = spy
f2, corr = C.predict(T, meta=meta, rp=base)
lgb.Booster.predict = orig
d = np.abs(corr - train_corr)
bad = np.where(d > 0.01)[0]
print('runs', len(sub), 'differing >0.01:', len(bad), 'max', np.nanmax(d))
for name, X, feats, ref_mask in (('plain', cap[0], meta['feats'], has), ('relevance', cap[1], meta['rel_feats'], use)):
    X = X.reindex(sub.index)
    print(f'--- {name} model: features whose live value differs from the training frame (all rows, then the {len(bad)} differing rows) ---')
    rows = []
    for c in feats:
        lv = pd.to_numeric(X[c], errors='coerce').values.astype(float)
        tv = pd.to_numeric(sub[c], errors='coerce').values.astype(float)
        both = ref_mask & ~np.isnan(lv) & ~np.isnan(tv)
        nan_mismatch = ref_mask & (np.isnan(lv) != np.isnan(tv))
        diff = np.abs(lv - tv)
        n_all = int((diff[both] > 1e-6).sum()) + int(nan_mismatch.sum())
        sel = np.isin(np.arange(len(sub)), bad) & ref_mask
        n_bad = int((diff[sel & both] > 1e-6).sum()) + int(nan_mismatch[sel].sum())
        if n_all:
            rows.append((c, n_all, n_bad, float(np.nanmax(diff[both])) if both.any() else np.nan))
    for r in sorted(rows, key=lambda r: -r[2])[:15]:
        print(f'{r[0]:18s} rows differing {r[1]:6d}  among the differing runs {r[2]:4d}  max abs diff {r[3]:.4f}')
    if not rows:
        print('no feature differs')
