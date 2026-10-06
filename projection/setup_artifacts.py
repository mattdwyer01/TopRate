"""One-off artifact setup: frozen class/track levels, the comment-text vectoriser, and the shipped main-model seeds.

usage: python setup_artifacts.py <dir holding lgb_seed1..5.txt and model_info.json from the research run>
"""
import gzip
import json
import os
import shutil
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(__file__))
import features as F  # noqa: E402

M = F.MODELS


def main(src):
    os.makedirs(M, exist_ok=True)
    H = F.load_history()
    tr = H[H.date.dt.year <= 2022]
    cm = tr.groupby('race_class').wpr.agg(['mean', 'count'])
    cm = cm[cm['count'] >= 200]['mean']
    tm = tr.groupby('track').wpr.agg(['mean', 'count'])
    tm = tm[tm['count'] >= 500]['mean']
    levels = dict(sex=sorted(H.horse_sex.dropna().unique().tolist()), **{'class': cm.to_dict(), 'track': tm.to_dict()})
    json.dump(levels, open(os.path.join(M, 'levels.json'), 'w'))
    F.fit_text(os.path.join(M, 'text_svd.joblib'))
    for i in range(1, 6):
        with open(os.path.join(src, f'lgb_seed{i}.txt'), 'rb') as f, gzip.open(os.path.join(M, f'main_seed{i}.txt.gz'), 'wb') as g:
            shutil.copyfileobj(f, g)
    shutil.copy(os.path.join(src, 'model_info.json'), os.path.join(M, 'main_info.json'))
    print('artifacts written to', M)


if __name__ == '__main__':
    main(sys.argv[1])
