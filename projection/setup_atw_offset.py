"""Trains the modelled ATW offset (atw_offset_model.py) from models/atw_offset_train.csv, one row per horse with a measured offset (atw_offsets.py)
and the weight, distance, month, age and sex of the race it was measured for (5,772 horses, 7 Oct 2026). Rebuild the csv from a fresh run if the form
feed's scale ever changes.

Usage: python projection/setup_atw_offset.py
"""
import json
import os
import sys

import lightgbm as lgb
import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(__file__))
import atw_offset_model as AM  # noqa: E402


def main():
    d = pd.read_csv(os.path.join(AM.M, 'atw_offset_train.csv'))
    sexes = sorted(d.sex.dropna().unique().tolist())
    X = AM.frame(d.w, d.dist, pd.to_datetime(dict(year=2026, month=d.month, day=1)), d.age, d.sex, sexes)
    idx = np.random.RandomState(0).permutation(len(d)); k = int(len(d) * 0.8)
    P = dict(objective='regression', learning_rate=0.05, num_leaves=15, min_data_in_leaf=20, feature_fraction=0.9, verbose=-1)
    m = lgb.train(P, lgb.Dataset(X.iloc[idx[:k]][AM.FEATS], d.off.values[idx[:k]], categorical_feature=['sex']), 400)
    rmse = float(np.sqrt(((m.predict(X.iloc[idx[k:]][AM.FEATS]) - d.off.values[idx[k:]]) ** 2).mean()))
    print(f'rows {len(d)}, held-out rmse {rmse:.3f}, spread {d.off.std():.2f}')
    lgb.train(P, lgb.Dataset(X[AM.FEATS], d.off.values, categorical_feature=['sex']), 400).save_model(AM.MODEL)
    json.dump(sexes, open(AM.SEXES, 'w'))
    print('saved', AM.MODEL)


if __name__ == '__main__':
    main()
