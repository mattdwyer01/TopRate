"""Build per-race Hong Kong trip data from HKJC's aerial replay images (23 Oct 2026).

For one meeting: fetch each race's results page (field, placings, lengths behind, draw) and the _L aerial image, label the dots
(hk_aerial_extract.read_frame with the field, then relabel_finish), and write data/hk_aerial/<YYYYMMDD>_<HV|ST>.json:
{race: {dist, field, runners: {num: {pla, draw, lbw, frames: [{x, rail_m} x4 at 780m, 410m, 200m to go, finish]}}}}.
Rail distances are metres to the inside rail from the dot centre (scale from M_PER_PX by course); a frame where the horse is off
the picture or unlabelled has no entry (None). Run: python research/hk_aerial_build.py 2026/10/14 HV   (needs network)
"""
import html
import json
import os
import re
import sys
import urllib.request

import numpy as np
from PIL import Image

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hk_aerial_extract as X
from hk_aerial_scale_check import UA, fetch, parse

OUT = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'data', 'hk_aerial')


def season(d):
    y, m = int(d[:4]), int(d[5:7])
    y0 = y if m >= 9 else y - 1
    return '%02d_%02d' % (y0 % 100, (y0 + 1) % 100)


def field_numbers(t):
    """Every starter's horse number (non-finishers have a text placing such as PU or FE, so parse() skips them)."""
    t = re.sub(r'<script.*?</script>|<style.*?</style>', '', t, flags=re.S)
    out = set()
    for r in re.findall(r'<tr[^>]*>(.*?)</tr>', t, flags=re.S):
        cells = [re.sub(r'\s+', ' ', html.unescape(re.sub(r'<[^>]+>', ' ', c))).strip() for c in re.findall(r'<t[dh][^>]*>(.*?)</t[dh]>', r, flags=re.S)]
        if len(cells) >= 10 and cells[0] and cells[1].isdigit() and cells[7].isdigit() and 1 <= int(cells[1]) <= 16:
            out.add(int(cells[1]))
    return sorted(out)


def image(d, n):
    s = d.replace('/', '')
    u = 'https://racing.hkjc.com/general/-/media/Sites/JCRW/RaceResult/%s/%s/%sR%d_Aerial_L.jpg' % (season(d), s, s, n)
    try:
        return X.load_image(urllib.request.urlopen(urllib.request.Request(u, headers=UA), timeout=40).read())
    except Exception:
        return None


def build_race(d, course, n, bank):
    t = fetch(d, course, n)
    rows, dist = parse(t)
    field = field_numbers(t)
    if not rows or not field:
        return None
    im = image(d, n)
    if im is None or im.shape[:2] != (1800, 800):
        return dict(dist=dist, field=field, err='no image')
    mpp = X.M_PER_PX.get(course, X.M_PER_PX_DEFAULT)
    frames = [X.read_frame(im, k * X.FRAME_H, bank, field=field) for k in range(4)]
    placings = [r['num'] for r in sorted(rows, key=lambda r: (r['pla'], r['num']))]
    fixed = X.relabel_finish(frames[3], placings)
    runners = {r['num']: dict(pla=r['pla'], draw=r['dr'], lbw=r['lbw'], frames=[None] * 4) for r in rows}
    for num in field:
        runners.setdefault(num, dict(pla=None, draw=None, lbw=None, frames=[None] * 4))
    unknown = 0
    for k, res in enumerate(frames):
        fr = im[k * X.FRAME_H:(k + 1) * X.FRAME_H]
        loc = [(d_['y'] - k * X.FRAME_H, d_['x']) for d_ in res]
        for d_ in res:
            if d_['num'] is None:
                unknown += 1
                continue
            px = X.rail_scan(fr, loc, d_['y'] - k * X.FRAME_H, d_['x'])
            runners[d_['num']]['frames'][k] = dict(x=d_['x'], rail_m=None if px is None else round(px * mpp, 1))
    return dict(dist=dist, field=field, runners=runners, unlabelled_dots=unknown, finish_relabelled=fixed)


def main():
    d, course = sys.argv[1], sys.argv[2]
    bank = X.build_bank(np.asarray(Image.open(X.SEED_IMAGE).convert('RGB')).astype(int))
    races = {}
    for n in range(1, 13):
        r = build_race(d, course, n, bank)
        if r is None:
            break
        races[str(n)] = r
        print('R%d' % n, 'dots' if 'runners' in r else r.get('err'), flush=True)
    os.makedirs(OUT, exist_ok=True)
    p = os.path.join(OUT, '%s_%s.json' % (d.replace('/', ''), course))
    json.dump(dict(date=d, course=course, source='HKJC aerial replay', races=races), open(p, 'w'), separators=(',', ':'))
    print('wrote', p)


if __name__ == '__main__':
    main()
