"""One-off artifacts for the ladder-review features: the going slope (within-horse WPR change per step of going number) and the frozen
'expected finish from tempo and position' model behind lad_r11_*. Both are fitted on runs before 2025 only, as in the held-out test.

usage: python projection/setup_ladder.py   (writes projection/models/ladder.json and pvj_model.txt)
"""
import json
import os
import sys

import lightgbm as lgb
import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(__file__))
import features as F  # noqa: E402

CUT = '2025-01-01'


def main():
    H = F.load_history()
    H = H[H.date < CUT].copy()
    gn = F._num(H.going)
    t = pd.DataFrame({'h': H.horse_id, 'w': H.wpr, 'g': gn}).dropna()
    dm = t.groupby('h')[['w', 'g']].transform(lambda s: s - s.mean())
    slope = float((dm.w * dm.g).sum() / (dm.g ** 2).sum())
    ff = ((H.positionFinish - 1) / (H.field_size - 1).clip(lower=1)).clip(0, 1)
    front = 1 - ((H.position800m - 1) / (H.field_size - 1).clip(lower=1))
    Z = pd.DataFrame({'ff': ff, 'p8': 1 - front, 'm8': H.margin800m.clip(0, 40), 'se': H.raceShapeEarly, 'sl': H.raceShapeLate,
                      'bf': (H.barrier - 1) / (H.field_size - 1).clip(lower=1)}).dropna()
    cols = ['p8', 'm8', 'se', 'sl', 'bf']
    m = lgb.train(dict(objective='regression', learning_rate=0.1, num_leaves=15, min_child_samples=200, verbose=-1, num_threads=4), lgb.Dataset(Z[cols], Z.ff), 150)
    m.save_model(os.path.join(F.MODELS, 'pvj_model.txt'))
    json.dump(dict(going_slope=round(slope, 4), pvj_rows=int(len(Z)), fitted_before=CUT), open(os.path.join(F.MODELS, 'ladder.json'), 'w'), indent=1)
    print('going slope', slope, 'pvj rows', len(Z))


if __name__ == '__main__':
    main()
