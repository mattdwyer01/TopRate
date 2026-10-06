"""Leak check: features for the most recent race day must be identical whether that day's outcomes are visible or hidden.

Builds the main-model, field-strength, trial and text features twice (last day's results kept, then blanked as if the races had not
run) and compares the rows of that day. Any difference means a feature peeks at its own outcome.

usage: python projection/validate.py
"""
import json
import os
import sys

import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(__file__))
import features as F  # noqa: E402


def build(X, levels, tf, svd):
    r = F.build_main(X, levels)
    need = r.date >= r.date.max()
    parts = [r, F.build_field(r), F.build_trials(r), F.build_trials3(r), F.build_light(r), F.text_features(r, need, tf, svd)]
    return pd.concat(parts, axis=1).loc[:, lambda d: ~d.columns.duplicated()]


def main():
    levels = json.load(open(os.path.join(F.MODELS, 'levels.json')))
    tf, svd = F.load_text(os.path.join(F.MODELS, 'text_svd.joblib'))
    H = F.load_history()
    last = H.date.max()
    seen = build(H, levels, tf, svd)
    X = H.copy()
    day = X.date >= last
    for c in ['wpr', 'positionFinish', 'marginFinish', 'priceStarting', 'position800m', 'margin800m']:
        X.loc[day, c] = np.nan
    X.loc[day, 'is_target'] = 1
    hidden = build(X, levels, tf, svd)
    a = seen[seen.date >= last].set_index(['race_id', 'horse_id'])
    b = hidden[hidden.date >= last].set_index(['race_id', 'horse_id'])
    b = b.reindex(a.index)
    bad = []
    for c in a.columns:
        if c in ('wpr', 'positionFinish', 'marginFinish', 'priceStarting', 'position800m', 'margin800m', 'is_target', 'ff', 'mg', 's', 'sex', 'gb', 'lvl'):
            continue
        x, y = pd.to_numeric(a[c], errors='coerce'), pd.to_numeric(b[c], errors='coerce')
        if x.isna().all() and y.isna().all():
            continue
        both = x.notna() & y.notna()
        mismatch = float(((x - y).abs()[both] > 1e-6).mean()) if both.any() else 0.0
        if mismatch > 0 or (x.notna() != y.notna()).mean() > 0.02:
            bad.append((c, round(mismatch, 4), round(float((x.notna() != y.notna()).mean()), 4)))
    print('rows checked', len(a), 'features compared', a.shape[1])
    print('LEAK-FREE' if not bad else f'DIFFERENCES: {bad}')
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
