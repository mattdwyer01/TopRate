"""Live path equals training path for the option 2 context model (27 Oct 2026). Takes every page run of the last N days (whole races, so the field-relative block sees the same
runners), runs ctx.predict() on them as upcoming targets and compares the correction with the training frame's, using the models in projection/models_tr/.
Run: PYTHONPATH=.:projection:research python research/ctx_v2_live_check.py [--days 12]"""
import argparse, json, os, sys
import numpy as np, pandas as pd, lightgbm as lgb
sys.path.insert(0, 'projection')
import ctx as C

ap = argparse.ArgumentParser(); ap.add_argument('--days', type=int, default=12); a = ap.parse_args()
meta = json.load(open(os.path.join(C.M, 'ctx.json')))
v2 = 'jw' in meta['feats']
rp = C.training_frame_rel(v2)
last = rp.date.max()
# whole fields, first starters included: the field-relative block ranks a runner against every runner of the race, as the live path sees the declared field
sub = rp[rp.date > last - pd.Timedelta(days=a.days)].copy()
classes = meta['classes']
sub['cls_c'] = C._cls(sub.cls, classes)
has = sub.f.notna().values
use = has & (sub.n >= C.REL_MIN_RUNS).values
m0 = lgb.Booster(model_file=os.path.join(C.M, 'ctx_model.txt'))
m1 = lgb.Booster(model_file=os.path.join(C.M, 'ctx_rel_model.txt'))
train_corr = np.full(len(sub), np.nan)
train_corr[has] = m0.predict(sub.loc[has, meta['feats']])
train_corr[use] = m1.predict(sub.loc[use, meta['rel_feats']])
# upcoming-style targets: only the page rows' declared facts, history rebuilt from runs strictly before each date
base = C.page_frame()
base['f'] = C.formula_pred(base, C.coefs())
base = C.context_columns(base)
base['resid'] = base.wpr - base.f
T = sub[['horse_id', 'date', 'jockey', 'trainer', 'vn', 'distance', 'going', 'weightCarried', 'barrier', 'field_size', 'race_class', 'trackGrading', 'prize']].rename(columns={'vn': 'venue'}).reset_index(drop=True) if 'trainer' in sub.columns else None
if T is None:
    sys.exit('no trainer column on the training frame (needs --v2)')
f2, corr = C.predict(T, meta=meta, rp=base)
d = np.abs(corr - train_corr)
ok = ~np.isnan(corr) & ~np.isnan(train_corr)
print(f'runs {len(sub)}, with correction {ok.sum()}, max |live - training| correction {np.nanmax(d[ok]):.6f}, mean {np.nanmean(d[ok]):.6f}, share over 0.01: {np.mean(d[ok] > 0.01):.4f}')
fd = np.abs(f2 - sub.f.values)
print(f'formula max diff {np.nanmax(fd):.8f}')
sys.exit(0 if np.nanmax(d[ok]) < 1e-3 else 1)
