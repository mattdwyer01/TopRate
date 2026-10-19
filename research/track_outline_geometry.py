"""Turn the OSM racecourse outlines (data/track_outlines/osm_horse_racing.json) into per-track geometry numbers (19 Oct 2026).
For each of our track names (results files) pick the OSM closed loop that is the main running track (longest closed leisure=track way with a perimeter of
1,000 to 4,500 m among the elements whose name matches) and measure it in a local metre projection: perimeter, area, compactness (4 pi A / P^2, 1 = circle),
elongation (major / minor axis), longest straight (resampled every 10 m, a straight is a stretch with radius above 1,000 m), bend radius (median radius of the bend
stretches below 600 m) and the share of the lap on bends. Output data/track_outlines/track_geometry.json {track: {...}}.
usage: PYTHONPATH=. python research/track_outline_geometry.py"""
import glob
import json
import math
import os
import re

import numpy as np
import pandas as pd

SRC = os.path.join('data', 'track_outlines', 'osm_horse_racing.json')
OUT = os.path.join('data', 'track_outlines', 'track_geometry.json')
STOP = {'racecourse', 'race', 'course', 'turf', 'club', 'track', 'raceway', 'racing', 'park', 'the', 'and', 'jockey', 'showgrounds', 'paceway', 'harness', 'members', 'practice'}


def toks(s):
    return [t for t in re.findall(r'[a-z]+', str(s).lower())]


def track_names():
    names = set()
    for f in sorted(glob.glob('race_results_20*.csv.gz'))[-6:]:
        names |= set(pd.read_csv(f, usecols=['track']).track.dropna().astype(str))
    return sorted(names)


def project(pts):
    lat = np.array([p['lat'] for p in pts])
    lon = np.array([p['lon'] for p in pts])
    x = (lon - lon.mean()) * 111320 * math.cos(math.radians(lat.mean()))
    y = (lat - lat.mean()) * 110574
    return x, y, float(lat.mean()), float(lon.mean())


def resample(x, y, step=10.0):
    d = np.r_[0, np.cumsum(np.hypot(np.diff(x), np.diff(y)))]
    n = max(int(d[-1] // step), 8)
    s = np.linspace(0, d[-1], n, endpoint=False)
    return np.interp(s, d, x), np.interp(s, d, y), d[-1]


def measure(pts):
    x, y, lat, lon = project(pts)
    if np.hypot(x[0] - x[-1], y[0] - y[-1]) > 30:
        return None
    area = abs(0.5 * np.sum(x[:-1] * y[1:] - x[1:] * y[:-1]))
    rx, ry, perim = resample(x, y)
    if not 1000 <= perim <= 4500:
        return None
    h = np.unwrap(np.arctan2(np.diff(np.r_[ry, ry[0]]), np.diff(np.r_[rx, rx[0]])))
    dh = np.diff(np.r_[h, h[0] + (2 * math.pi if h[-1] > h[0] else -2 * math.pi)])
    k = np.convolve(np.abs(dh), np.ones(5) / 5, mode='same') / 10.0     # curvature 1/m, smoothed over 50 m
    straight = k < 1 / 1000
    best = cur = 0
    for v in np.r_[straight, straight]:
        cur = cur + 1 if v else 0
        best = max(best, cur)
    best = min(best, len(straight)) * 10.0
    bend = k > 1 / 600
    rad = 1 / np.median(k[bend]) if bend.sum() >= 5 else np.nan
    c = np.cov(np.vstack([rx, ry]))
    ev = np.sort(np.linalg.eigvalsh(c))
    return {'perim': round(perim), 'area': round(area), 'compact': round(4 * math.pi * area / perim ** 2, 3), 'elong': round(math.sqrt(ev[1] / max(ev[0], 1e-9)), 2),
            'straight': round(best), 'bend_radius': None if np.isnan(rad) else round(rad), 'bend_share': round(float(bend.mean()), 3), 'lat': round(lat, 4), 'lon': round(lon, 4)}


def rings(ways):
    """Stitch way point lists (lat/lon dicts) into closed rings by shared end points."""
    key = lambda p: (round(p['lat'], 7), round(p['lon'], 7))
    left = [list(w) for w in ways if len(w) >= 2]
    out = []
    while left:
        cur = left.pop()
        grew = True
        while grew and key(cur[0]) != key(cur[-1]):
            grew = False
            for i, w in enumerate(left):
                if key(w[0]) == key(cur[-1]):
                    cur = cur + w[1:]
                elif key(w[-1]) == key(cur[-1]):
                    cur = cur + w[::-1][1:]
                elif key(w[-1]) == key(cur[0]):
                    cur = w + cur[1:]
                elif key(w[0]) == key(cur[0]):
                    cur = w[::-1] + cur[1:]
                else:
                    continue
                left.pop(i)
                grew = True
                break
        if key(cur[0]) == key(cur[-1]):
            out.append(cur)
    return out


def main():
    els = json.load(open(SRC))['elements']
    loops = []
    for e in els:
        if e['tags'].get('leisure') != 'track':
            continue
        if e['type'] == 'way' and 'geometry' in e:
            cand = [(e['geometry'], 'way')]
        elif e['type'] == 'relation':
            inner = rings([m['geometry'] for m in e.get('members', []) if m.get('type') == 'way' and m.get('role') == 'inner' and m.get('geometry')])
            outer = rings([m['geometry'] for m in e.get('members', []) if m.get('type') == 'way' and m.get('role') in ('outer', '') and m.get('geometry')])
            cand = [(g, 'inner') for g in inner] + [(g, 'outer') for g in outer]
        else:
            continue
        for g, kind in cand:
            m = measure(g)
            if m:
                m['name'] = e['tags'].get('name', '')
                m['osm_id'] = e['id']
                m['kind'] = kind
                loops.append(m)
    print(len(loops), 'usable closed loops')
    named = [e for e in els if e['tags'].get('name')]
    out = {}
    for tr in track_names():
        tt = [t for t in toks(tr) if t not in STOP]
        if not tt:
            continue
        cands = [e for e in named if all(t in toks(e['tags']['name']) for t in tt)]
        if not cands:
            continue
        # centre of the matched named elements, then closed loops within 3 km of it
        cl = []
        for e in cands:
            g = e.get('geometry') or [m for mem in e.get('members', []) for m in (mem.get('geometry') or [])]
            if g:
                cl.append((np.mean([p['lat'] for p in g]), np.mean([p['lon'] for p in g])))
        if not cl:
            continue
        ids = {e['id'] for e in cands}
        own = [m for m in loops if m['osm_id'] in ids]
        la, lo = np.median([c[0] for c in cl]), np.median([c[1] for c in cl])
        near = own or [m for m in loops if abs(m['lat'] - la) * 110574 < 800 and abs(m['lon'] - lo) * 111320 * math.cos(math.radians(la)) < 800]
        if not near:
            continue
        inn = [m for m in near if m['kind'] == 'inner']
        main = max(inn or near, key=lambda m: m['perim'])
        out[tr] = dict(main, n_loops=len(near))
    json.dump(out, open(OUT, 'w'), indent=0)
    print(len(out), 'of', len(track_names()), 'tracks matched ->', OUT)
    for k in ('Flemington', 'Caulfield', 'Moonee Valley', 'Randwick', 'Rosehill', 'Eagle Farm', 'Doomben', 'Morphettville', 'Ascot', 'Echuca', 'Bendigo'):
        print(k, out.get(k))


if __name__ == '__main__':
    main()
