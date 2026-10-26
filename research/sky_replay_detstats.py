"""Compare detectors by field coverage. usage: python research/sky_replay_detstats.py DIR   (DIR holds det_frcnn_{race}.json and det_yolo_{race}.json)
Per race, over frames where a detector sees 3+ horses: mean share of the field detected, share of frames with 80%+ of the field, mean horses per frame."""
import glob, json, os, sys
import numpy as np
MAP = {'20261024FLER': ('Flemington', '2026-10-24'), '20261024MOPR': ('Morphettville', '2026-10-24'), '20261017CAUR': ('Caulfield', '2026-10-17')}


def load_field(venue, date, race):
    for r in json.load(open('toprate_history.json'))['RACES']:
        if r['venue'] == venue and r['date'] == date and r['race'] == race:
            return [x for x in r['runners'] if not x.get('scr')]
    return []


def stat(d, n, thr):
    c = [len([r for r in rows if r[5] == 'horse' and r[4] >= thr]) for rows in d.values()]
    c = [x for x in c if x >= 3]
    if not c:
        return 0, 0, 0
    rec = [min(x / n, 1) for x in c]
    return float(np.mean(rec)), float(np.mean([r >= 0.8 for r in rec])), float(np.mean(c))


rows = []
for f in sorted(glob.glob(sys.argv[1] + '/**/det_yolo_*.json', recursive=True)):
    b = os.path.basename(f)[9:-5]
    g = f.replace('det_yolo_', 'det_frcnn_')
    if not os.path.exists(g):
        continue
    venue, date = MAP[b[:12]]
    n = len(load_field(venue, date, int(b[12:])))
    if not n:
        continue
    y, fr = stat(json.load(open(f)), n, 0.3), stat(json.load(open(g)), n, 0.5)
    rows.append((b, n, fr, y))
    print(b, 'n', n, '| frcnn recall %.2f >=80%% %.2f per-frame %.1f | yolo recall %.2f >=80%% %.2f per-frame %.1f' % (fr + y))
if rows:
    print('MEAN frcnn recall %.3f >=80%% %.3f | yolo recall %.3f >=80%% %.3f' % (
        np.mean([r[2][0] for r in rows]), np.mean([r[2][1] for r in rows]), np.mean([r[3][0] for r in rows]), np.mean([r[3][1] for r in rows])))
