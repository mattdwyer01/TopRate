"""Read start, finish and chute facts off the racerate.com plan maps (21 Oct 2026) so the dashboard can draw its own track pictures on the OpenStreetMap rings.
Only facts are kept (racing direction, which start distances sit on the rail and which on a chute, chute lengths), not the drawings. Per map: OCR finds the distance labels
and 'Winning post'; the running track is the largest ring of ink (its hole gives the rail line and a pixel perimeter); a label whose own ink spur leaves the ring is a chute
(length scaled by metres per pixel = OSM perimeter / ring perimeter in pixels); the others sit on the rail. Direction: going round from the post, start distances grow
backwards, so the way that distance rises is against the racing direction. Output data/track_outlines/track_marks_auto.json, in the same shape as track_marks.json.
usage: python research/racerate_marks.py --cache DIR [--slugs a,b] [--compare]"""
import io
import json
import os
import re
import sys

import cv2
import numpy as np
from PIL import Image

sys.path.insert(0, os.path.dirname(__file__))
import racerate_maps as R  # noqa: E402

OUT = os.path.join('data', 'track_outlines', 'track_marks_auto.json')
HAND = os.path.join('data', 'track_outlines', 'track_marks.json')


def read_map(gif, slug):
    im = Image.open(io.BytesIO(gif)).convert('RGB')
    for poly in R.BLANK.get(slug, []):
        from PIL import ImageDraw
        ImageDraw.Draw(im).polygon(poly, fill=(255, 255, 255))
    a = np.array(im).astype(int)
    r, g, b = a[..., 0], a[..., 1], a[..., 2]
    luma = (r * 299 + g * 587 + b * 114) // 1000
    red = (r > 140) & (g < 110) & (b < 110)
    ink = ((luma < 185) & ~red).astype(np.uint8) * 255
    erase = np.zeros_like(ink)
    labels, post = [], None
    for txt, pts, w, h, ang in R.ocr_boxes(im):
        low = txt.lower().replace(' ', '')
        parts = re.findall(r'\d{3,4}m?', txt.replace(' ', ''))
        poly = pts.astype(np.int32)
        cx, cy = pts.mean(axis=0)
        if len(parts) >= 2 and all(R.clean_label(x) for x in parts):
            for i, x in enumerate(parts):
                f = (i + 0.5) / len(parts)
                p = pts[0] + (pts[1] - pts[0]) * f + (pts[3] - pts[0]) * 0.5
                labels.append((R.clean_label(x), float(p[0]), float(p[1])))
            cv2.fillPoly(erase, [poly], 255)
        elif R.clean_label(txt):
            labels.append((R.clean_label(txt), float(cx), float(cy)))
            cv2.fillPoly(erase, [poly], 255)
        elif low in ('winning', 'post') or 'post' in low or 'winning' in low:
            post = (float(cx), float(cy)) if post is None else ((post[0] + cx) / 2, (post[1] + cy) / 2)
            cv2.fillPoly(erase, [poly], 255)
        elif 'start' in low or low in ('steeple', 'track'):
            cv2.fillPoly(erase, [poly], 255)
    erase = cv2.dilate(erase, np.ones((3, 3), np.uint8))
    ink[erase > 0] = 0
    return ink, labels, post


def analyse(ink, labels, post):
    """Returns the marks dict, or None when the map has no usable ring."""
    k = np.ones((3, 3), np.uint8)
    solid = cv2.morphologyEx(ink, cv2.MORPH_CLOSE, np.ones((9, 9), np.uint8))
    cs, hier = cv2.findContours(solid, cv2.RETR_CCOMP, cv2.CHAIN_APPROX_NONE)
    if hier is None:
        return None
    holes = [(cv2.contourArea(c), i) for i, c in enumerate(cs) if hier[0][i][3] >= 0]
    if not holes:
        return None
    _, hi = max(holes)
    hole = cs[hi].reshape(-1, 2).astype(float)
    per_px = float(cv2.arcLength(cs[hi], True))
    cx, cy = hole.mean(axis=0)
    dt = cv2.distanceTransform((ink > 0).astype(np.uint8), cv2.DIST_L2, 3)
    thick = 2 * float(np.percentile(dt[ink > 0], 90))
    holemask = np.zeros_like(ink)
    cv2.drawContours(holemask, [cs[hi]], -1, 255, -1)
    ringz = cv2.dilate(holemask, cv2.getStructuringElement(cv2.MORPH_ELLIPSE, (int(2 * 1.3 * thick) | 1,) * 2))
    spur = ink.copy()
    spur[ringz > 0] = 0
    n, lab, stats, cent = cv2.connectedComponentsWithStats(spur, connectivity=8)
    edge = cv2.distanceTransform((ringz == 0).astype(np.uint8), cv2.DIST_L2, 3)       # distance from the ring zone
    ang = np.arctan2(-(hole[:, 1] - cy), hole[:, 0] - cx)

    def t_of(x, y):
        d = np.hypot(hole[:, 0] - x, hole[:, 1] - y)
        j = int(np.argmin(d))
        return j / len(hole), float(d[j]), j

    sgn = 1.0 if (np.diff(np.unwrap(ang)).sum() > 0) else -1.0          # +1: contour index runs counter-clockwise on screen
    rail, chutes = {}, {}
    r = int(thick * 1.4)
    for d, x, y in labels:
        t, dist, j = t_of(x, y)
        sub = lab[max(int(y) - r, 0):int(y) + r + 1, max(int(x) - r, 0):int(x) + r + 1]
        best = None
        for c in np.unique(sub[sub > 0]):
            ys, xs = np.nonzero(lab == c)
            e = edge[ys, xs]
            reach = float(e.max())                      # how far the spur runs out of the ring zone
            if reach < 1.5 * thick:
                continue
            a0 = int(np.argmin(e))
            if e[a0] > 1.5 * thick:                     # does not start at the ring: an arrow or a loose mark
                continue
            if best is None or reach > best[0]:
                best = (reach, float(xs[a0]), float(ys[a0]))
        if best:
            ja = int(np.argmin(np.hypot(hole[:, 0] - best[1], hole[:, 1] - best[2])))
            chutes[d] = (best[0] + 1.3 * thick, ja / len(hole))
        else:
            rail[d] = t
    if post is None:
        return None
    tp = t_of(*post)[0]
    # direction: rail start distances grow backwards from the post. along = signed arc (0..1, counter-clockwise on screen) from the post to the label
    xs_, ys_ = [], []
    for d, t in rail.items():
        dt_ = ((t - tp) * sgn) % 1.0
        xs_.append(d)
        ys_.append(dt_)
    if len(xs_) < 2:
        return None
    # unwrap: the ring is a loop, so use the order of arc position against distance
    order = np.argsort(xs_)
    arcs = np.array(ys_)[order]
    steps = np.diff(arcs)
    steps = (steps + 0.5) % 1.0 - 0.5
    back_ccw = float(np.sum(steps)) > 0          # distance grows counter-clockwise on screen => racing runs clockwise
    direction = 'cw' if back_ccw else 'ccw'
    # winning post along the bottom straight
    home = hole[hole[:, 1] > hole[:, 1].max() - 0.12 * (hole[:, 1].max() - hole[:, 1].min())]
    fb = 0.2
    if len(home) > 4:
        xl, xr = home[:, 0].min(), home[:, 0].max()
        px = min(max(post[0], xl), xr)
        fb = (xr - px) / (xr - xl) if direction == 'cw' else (px - xl) / (xr - xl)
        fb = round(float(min(max(fb, 0.0), 0.5)), 2)
    return {'dir': direction, 'fb': fb, 'ring': sorted(rail), 'chute_px': {str(d): round(v[0] / per_px, 3) for d, v in chutes.items()}, 'per_px': round(per_px, 1)}


def main():
    cache = sys.argv[sys.argv.index('--cache') + 1] if '--cache' in sys.argv else None
    only = sys.argv[sys.argv.index('--slugs') + 1].split(',') if '--slugs' in sys.argv else None
    idx = R.get(R.BASE + 'trackinformation.htm', cache, 'index.htm').decode('latin-1')
    pages = sorted(set(re.findall(r'href="(Track%20Info/[^"]+\.htm)"', idx, flags=re.I)))
    res = {}
    for p in pages:
        base = os.path.basename(p)[:-4]
        slug = re.sub(r'[^a-z0-9]', '', base.lower().replace('%20', ''))
        if only and slug not in only:
            continue
        try:
            html = R.get(R.BASE + p, cache, base + '.htm').decode('latin-1')
            m = re.search(r'src="\.\./(TRACK_MAPS/[^"]+)"', html, flags=re.I)
            if not m:
                continue
            gif = R.get(R.BASE + m.group(1), cache, 'g_' + os.path.basename(m.group(1)))
            ink, labels, post = read_map(gif, slug)
            mk = analyse(ink, labels, post)
        except Exception as e:
            print('skip', base, e)
            continue
        if mk:
            mk['name'] = re.sub(r'(?i)\s*(racecourse|track map).*', '', base.replace('%20', ' ')).strip().lower()
            res[slug] = mk
    json.dump(res, open(OUT, 'w'), indent=0)
    print(len(res), 'maps read ->', OUT)


if __name__ == '__main__':
    main()
