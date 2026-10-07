"""Modelled ATW offset for a runner with no measured one (see atw_offsets.py).

A measured offset needs 2+ of the horse's runs in both the form feed and the results files with a constant gap. About 13% of runners have none
(debutants, one prior run, an inconsistent gap). The offset is a function of the weight carried, age, sex and distance (held-out rmse about 0.7
WPR against a spread of 2.5), so a small LightGBM model trained on the measured ones fills the gap. Trained by setup_atw_offset.py.
"""
import json
import os

import lightgbm as lgb
import numpy as np
import pandas as pd

M = os.path.join(os.path.dirname(__file__), 'models')
MODEL = os.path.join(M, 'atw_offset_model.txt')
SEXES = os.path.join(M, 'atw_offset_sexes.json')
FEATS = ['w', 'dist', 'age', 'sex']  # month was tested and left out: the training horses all come from Sep and Oct, so it cannot extrapolate


def frame(weight, dist, date, age, sex, sexes):
    return pd.DataFrame(dict(w=pd.to_numeric(weight, errors='coerce').values, dist=pd.to_numeric(dist, errors='coerce').values,
                             month=pd.to_datetime(date).dt.month.values, age=pd.to_numeric(age, errors='coerce').values,
                             sex=pd.Series(sex).map({c: i for i, c in enumerate(sexes)}).fillna(0).values))


def predict(weight, dist, date, age, sex):
    """Array of modelled offsets (NaN where weight or age is unknown). Returns all NaN if the model file is missing."""
    n = len(weight)
    if not (os.path.exists(MODEL) and os.path.exists(SEXES)):
        return np.full(n, np.nan)
    sexes = json.load(open(SEXES))
    X = frame(weight, dist, date, age, sex, sexes)
    out = lgb.Booster(model_file=MODEL).predict(X[FEATS])
    out = np.where(X.w.isna() | X.age.isna(), np.nan, out)
    return np.round(out, 1)
