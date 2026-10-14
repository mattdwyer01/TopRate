"""Artifacts for the TopRate-rating models (14 Oct 2026): copies projection/models to models_tr (the comment vectoriser, suitability inputs, jockey
impute and the model shells do not depend on the rating scale), then refits what does: the frozen class/track levels and the ladder going slope.
Run with PROJECTION_RATINGS=toprate, then train_main.py, train_suit.py and train_light.py with the same variable.

usage: PROJECTION_RATINGS=toprate python projection/setup_tr_artifacts.py
"""
import json
import os
import shutil
import sys

sys.path.insert(0, os.path.dirname(__file__))
import features as F  # noqa: E402
import pandas as pd  # noqa: E402


def main():
    assert F.RATINGS_SOURCE == 'toprate', 'set PROJECTION_RATINGS=toprate'
    src = os.path.join(os.path.dirname(__file__), 'models')
    if not os.path.isdir(F.MODELS):
        shutil.copytree(src, F.MODELS)
    H = F.load_history()
    tr = H[H.date.dt.year <= 2022]
    cm = tr.groupby('race_class').wpr.agg(['mean', 'count'])
    cm = cm[cm['count'] >= 200]['mean']
    tm = tr.groupby('track').wpr.agg(['mean', 'count'])
    tm = tm[tm['count'] >= 500]['mean']
    levels = dict(sex=sorted(H.horse_sex.dropna().unique().tolist()), **{'class': cm.to_dict(), 'track': tm.to_dict()})
    json.dump(levels, open(os.path.join(F.MODELS, 'levels.json'), 'w'))
    print('levels written', len(cm), 'classes', len(tm), 'tracks')
    # ladder going slope on this scale (the expected-finish model pvj_model.txt reads race-shape columns that are blank in both modes, so it is not refitted)
    Hb = H[H.date < '2025-01-01']
    t = pd.DataFrame({'h': Hb.horse_id, 'w': Hb.wpr, 'g': F._num(Hb.going)}).dropna()
    dm = t.groupby('h')[['w', 'g']].transform(lambda s: s - s.mean())
    slope = float((dm.w * dm.g).sum() / (dm.g ** 2).sum())
    info = json.load(open(os.path.join(F.MODELS, 'ladder.json')))
    info['going_slope'] = round(slope, 4)
    json.dump(info, open(os.path.join(F.MODELS, 'ladder.json'), 'w'), indent=1)
    print('going slope', slope)


if __name__ == '__main__':
    main()
