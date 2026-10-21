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
GC = os.path.join('data', 'track_outlines', 'geocode.json')
VARIANT = re.compile(r'\b(synthetic|inner|heath|parks?|scarpside|lakeside|hillside|fibre sand|kensington)\b', re.I)
STOP = {'racecourse', 'race', 'course', 'turf', 'club', 'track', 'raceway', 'racing', 'park', 'the', 'and', 'jockey', 'showgrounds', 'paceway', 'harness', 'members', 'practice'}


def base_name(t):
    return re.sub(r'\s+', ' ', re.sub(r'\bgh\b', '', t.replace('-', ' '), flags=re.I)).strip()


def dist_m(la1, lo1, la2, lo2):
    return math.hypot((la1 - la2) * 110574, (lo1 - lo2) * 111320 * math.cos(math.radians(la1)))


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
    best_end = 0
    for i, v in enumerate(np.r_[straight, straight]):
        cur = cur + 1 if v else 0
        if cur > best:
            best, best_end = cur, i
    best = min(best, len(straight))
    srun = ((best_end - best + 1) % len(straight), best)      # start index and length (10 m samples) of the longest straight
    runs = []                                                 # every straight of 150 m or more as (start, length), longest first
    n_s = len(straight)
    for i0 in range(n_s):
        if straight[i0] and not straight[i0 - 1]:
            ln = 0
            while straight[(i0 + ln) % n_s] and ln < n_s:
                ln += 1
            if ln >= 15:
                runs.append((i0, ln))
    runs.sort(key=lambda r: -r[1])
    best = best * 10.0
    bend = k > 1 / 600
    rad = 1 / np.median(k[bend]) if bend.sum() >= 5 else np.nan
    c = np.cov(np.vstack([rx, ry]))
    ev = np.sort(np.linalg.eigvalsh(c))
    return {'perim': round(perim), 'area': round(area), 'compact': round(4 * math.pi * area / perim ** 2, 3), 'elong': round(math.sqrt(ev[1] / max(ev[0], 1e-9)), 2),
            'straight': round(best), 'bend_radius': None if np.isnan(rad) else round(rad), 'bend_share': round(float(bend.mean()), 3), 'lat': round(lat, 4), 'lon': round(lon, 4),
            '_ring': (rx, ry), '_srun': srun, '_runs': runs}


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


NOT_SHOWN = {'Rosehill', 'Eagle Farm'}      # ring pick known to be wrong (3,083 m and 2,019 m against 2,040 m and 1,800 m)
SHOWN_OUT = 'track_outlines.json'            # repo root, fetched by the dashboard


MARKS = os.path.join('data', 'track_outlines', 'track_marks.json')


def place_marks(ring, runs, mk, per):
    """Finish post, start points and chute spurs in the ring's own metres from the hand-read notes in track_marks.json (read off the racerate.com plan maps:
    racing direction, where the post sits on the home straight, and which starts are on the rail or on a chute). Back distance is measured along the ring from the post
    against the racing direction; a chute is a straight spur leaving the rail tangentially. Returns None if the notes cannot be applied."""
    rx, ry = ring
    n = len(rx)
    if not runs:
        return None
    area = 0.5 * float(np.sum(rx * np.roll(ry, -1) - np.roll(rx, -1) * ry))
    sgn = 1 if (mk['dir'] == 'ccw') == (area > 0) else -1          # +1: racing follows the point order
    hi = min(mk.get('home', 0), len(runs) - 1)
    a, ln = runs[hi]
    end = a + ln if sgn > 0 else a                                  # end of the home straight in the racing direction
    fin = (end - sgn * mk['fb'] * ln) % n
    pt = lambda i: (float(np.interp(i % n, np.arange(n + 1), np.r_[rx, rx[0]])), float(np.interp(i % n, np.arange(n + 1), np.r_[ry, ry[0]])))
    back = lambda d: (fin - sgn * (d % per) / (per / n)) % n         # ring index d metres behind the post
    r = lambda p: [int(round(p[0])), int(round(p[1]))]
    starts = {str(d): r(pt(back(d))) for d in mk['ring']}
    chutes = {}
    for d, lc in mk['chute'].items():
        # a chute leaves the rail lc metres before the start (the join is at back distance d - lc) and continues the straight that runs on from the join:
        # the direction is from the rail 100 m further on (towards the post) back through the join, so a bend behind the join does not swing it
        t = back(int(d) - lc)
        p0, p1 = pt(t), pt(t + sgn * 100 / (per / n))
        v = np.array([p0[0] - p1[0], p0[1] - p1[1]])
        # a chute that leaves near the back end of the HOME straight runs on collinear with it (Flemington's 800 to 1200 and 3200 chute); a bend behind the join must not swing it
        best = None
        for ra, rl in (runs if mk.get('chute_any') else [runs[hi]]):
            be = ra if sgn > 0 else ra + rl                         # back end of the run (against the racing direction)
            fe = ra + rl if sgn > 0 else ra
            gap = min(abs((t - be) % n), abs((be - t) % n)) * per / n
            if gap <= 250 and (best is None or gap < best[0]):
                best = (gap, np.array(pt(be)) - np.array(pt(fe)))
        if best is not None and np.hypot(*best[1]) > 1:
            v = best[1]
        v = v / (np.hypot(*v) or 1.0)
        chutes[d] = [r(p0), [int(round(p0[0] + v[0] * lc)), int(round(p0[1] + v[1] * lc))]]
    return {'dir': mk['dir'], 'fin': r(pt(fin)), 'starts': starts, 'chutes': chutes, 's0': int(a), 'sn': int(ln), 'sgn': sgn}


def export_outlines(out, rings_out, step=2):
    """Write the dashboard file: per track the running-rail ring every 20 m in whole metres (north up, x east, y north), the longest straight as a start index and length,
    and the measured numbers. Both name keys are lowercase."""
    tracks = {}
    marks = json.load(open(MARKS)) if os.path.exists(MARKS) else {}
    for tr, (ring, srun, runs) in rings_out.items():
        if tr in NOT_SHOWN:
            continue
        rx, ry = ring
        px = [int(round(v)) for v in rx[::step]]
        py = [int(round(v)) for v in ry[::step]]
        m = out[tr]
        tracks[tr.lower()] = {'name': tr, 'perim': m['perim'], 'straight': m['straight'], 'radius': m['bend_radius'], 'by': m['by'],
                              's0': int(srun[0] // step), 'sn': int(srun[1] // step), 'pts': [[a, b] for a, b in zip(px, py)]}
        mk = marks.get(tr.lower())
        pm = place_marks(ring, runs, mk, m['perim']) if mk else None
        if pm:
            hs0, hsn = pm.pop('s0'), pm.pop('sn')
            tracks[tr.lower()].update(pm, s0=int(hs0 // step), sn=int(hsn // step))
    json.dump({'source': 'OpenStreetMap contributors (ODbL)', 'step': step * 10, 'tracks': tracks}, open(SHOWN_OUT, 'w'), separators=(',', ':'))
    print(len(tracks), 'outlines ->', SHOWN_OUT, round(os.path.getsize(SHOWN_OUT) / 1024), 'KB')


def main():
    els = json.load(open(SRC))['elements']
    xp = os.path.join('data', 'track_outlines', 'osm_extra.json')
    if os.path.exists(xp):
        seen = {(e['type'], e['id']) for e in els}
        els += [e for e in json.load(open(xp))['elements'].values() if (e['type'], e['id']) not in seen]
    loops = []
    for e in els:
        if e.get('tags', {}).get('leisure') not in ('track', 'racetrack'):
            continue          # running-track elements only (the sport=horse_racing areas are whole course boundaries)
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
    gc = json.load(open(GC)) if os.path.exists(GC) else {}
    out = {}
    rings_out = {}
    for tr in track_names():
        if VARIANT.search(tr):
            continue          # alternative circuit at a venue (synthetic, inner, heath...): the base loop would be the wrong track
        bs = base_name(tr)
        pts = [(g['lat'], g['lon']) for g in gc.get(bs, [])]
        tt = [t for t in toks(bs) if t not in STOP]
        cands = [e for e in named if tt and all(t in toks(e['tags']['name']) for t in tt)]
        ids = {e['id'] for e in cands}
        best = None
        for la, lo in pts:
            near = [m for m in loops if dist_m(m['lat'], m['lon'], la, lo) < 1500]
            if near and (best is None or len(near) > len(best)):
                best = near
        if best is None and ids:
            best = [m for m in loops if m['osm_id'] in ids]
        if not best:
            continue
        named_loops = [m for m in best if m['osm_id'] in ids]
        pool = named_loops or best
        inn = [m for m in pool if m['kind'] == 'inner']      # inner ring = running rail; fall back to ways / outer rings
        main = max(inn or pool, key=lambda m: m['perim'])
        out[tr] = dict(main, n_loops=len(best), by='name' if named_loops else 'location')
        rings_out[tr] = (main['_ring'], main['_srun'], main['_runs'])
        out[tr].pop('_ring'), out[tr].pop('_srun'), out[tr].pop('_runs')
    json.dump(out, open(OUT, 'w'), indent=0)
    export_outlines(out, rings_out)
    print(len(out), 'of', len(track_names()), 'tracks matched ->', OUT)
    import glob as _g
    rr = pd.concat([pd.read_csv(f, usecols=['track']) for f in sorted(_g.glob('race_results_20*.csv.gz'))[-3:]]).track.value_counts()
    print('share of recent runs at matched tracks', round(rr[rr.index.isin(out)].sum() / rr.sum(), 3))
    for k in ('Flemington', 'Caulfield', 'Moonee Valley', 'Randwick', 'Rosehill', 'Eagle Farm', 'Doomben', 'Morphettville', 'Ascot', 'Echuca', 'Bendigo'):
        print(k, out.get(k))


if __name__ == '__main__':
    main()
