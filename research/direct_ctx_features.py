"""Builds Proj's context (ctx.FEATS), relevance (ctx.REL_FEATS) and speed-figure (ctx.SPD_FEATS) inputs for every results-file run 2019-06 to 2025-12, on the converted
(per-row ATW shift) full-field frame, so the direct finishing-position model can use them (26 Oct 2026). Saved to /tmp/direct_ctx_feats.pkl keyed (horse_id, date).
Run: PYTHONPATH=.:projection:research python research/direct_ctx_features.py"""
import os, sys
import numpy as np, pandas as pd
sys.path.insert(0, 'projection'); sys.path.insert(0, 'research')
import ctx as C
import features as F
import conv_history as CH

conv = CH.build(2019, '2025-12-31', 1.0, per_row=True)
F._TR_CACHE['rows'] = conv
rp = C.training_frame_rel()
print('frame', rp.shape, flush=True)
rp = C.add_speed(rp)
sp = C.speed_features(rp, rp)
rp = pd.concat([rp, sp], axis=1)
keep = [c for c in C.FEATS + C.REL_FEATS + C.SPD_FEATS if c not in ('cls_c',)]
keep = list(dict.fromkeys(keep))
out = rp[['horse_id', 'date'] + keep].copy()
out.columns = ['horse_id', 'date'] + ['x_' + c for c in keep]
out.to_pickle('/tmp/direct_ctx_feats.pkl')
print('saved', out.shape, 'f known on', out.x_f.notna().mean().round(3), 'speed block on', out.x_sp1.notna().mean().round(3))
