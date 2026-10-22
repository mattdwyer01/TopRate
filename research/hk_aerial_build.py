"""Build per-race Hong Kong trip data from HKJC's aerial replay images (23 Oct 2026).

For one meeting: fetch each race's results page (field, placings, lengths behind, draw) and the _L aerial image, label the dots
(hk_aerial_extract.read_frame with the field, then relabel_finish), and write data/hk_aerial/<YYYYMMDD>_<HV|ST>.json:
{race: {dist, field, runners: {num: {pla, draw, lbw, frames: [{x, rail_m} x4 at 780m, 410m, 200m to go, finish]}}}}.
Rail distances are metres to the inside rail from the dot centre (scale from M_PER_PX by course); a frame where the horse is off
the picture or unlabelled has no entry (None). Run: python research/hk_aerial_build.py 2026/10/14 HV   (needs network)
`--auto [days]` (default 21) builds every meeting of the last N days that has an image for race 1 and no output file yet
(used by .github/workflows/hk_aerial.yml).
"""
import html
import json
import os
import re
import sys
import urllib.request

import numpy as np
import pandas as pd
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
    runners = {r['num']: dict(horse=r['horse'], pla=r['pla'], draw=r['dr'], lbw=r['lbw'], time=r['time'], frames=[None] * 4) for r in rows}
    for num in field:
        runners.setdefault(num, dict(horse=None, pla=None, draw=None, lbw=None, time=None, frames=[None] * 4))
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


GPS_DIR = os.path.join(os.path.dirname(OUT), 'gps')
VENUE = {'HV': 'Happy Valley', 'ST': 'Sha Tin'}
TO_GO_M = [780, 410, 200, 0]          # where the leader is in each snapshot (metres from the finish)
LENGTH_M = 2.4
KEYS = {'hk_gps_runs': ['meet_code', 'race_no', 'tab_no'], 'hk_gps_sections': ['meet_code', 'race_no', 'tab_no', 'to_go_m']}


def _secs(t):
    """'1:38.25' -> 98.25"""
    try:
        m, sec = str(t).split(':')
        return int(m) * 60 + float(sec)
    except Exception:
        return None


def gps_tables(meeting):
    """Per runner and per snapshot rows in the data/gps layout (like rc_gps_runs / rc_gps_sections, with lengths and metres off the rail)."""
    d, course = meeting['date'], meeting['course']
    code = '%s_%s' % (d.replace('/', ''), course)
    runs, secs = [], []
    for rn, race in meeting['races'].items():
        if 'runners' not in race:
            continue
        mpp = X.M_PER_PX.get(course, X.M_PER_PX_DEFAULT)
        px_len = LENGTH_M / mpp                     # pixels per length
        n_field = len(race['field'])
        win_t = next((_secs(v['time']) for v in race['runners'].values() if v.get('pla') == 1), None)
        pos_by_frame = []
        for k in range(4):
            vis = [(num, v['frames'][k]) for num, v in race['runners'].items() if v['frames'][k]]
            right = k < 2                            # the camera follows the leader at the right in snapshots 0 and 1, the left in 2 and 3
            lead = (max if right else min)([f['x'] for _, f in vis]) if vis else None
            order = sorted(vis, key=lambda t: -t[1]['x'] if right else t[1]['x'])
            pos_by_frame.append({num: (i + 1, abs(f['x'] - lead) / px_len, len(vis)) for i, (num, f) in enumerate(order)})
        for num, v in race['runners'].items():
            if v.get('horse') is None:
                continue
            rails = [f['rail_m'] for f in v['frames'] if f and f['rail_m'] is not None]
            runs.append(dict(
                meet_code=code, race_no=int(rn), venue=VENUE.get(course, course), race_date=d.replace('/', '-'),
                race_distance='%sm' % race['dist'] if race.get('dist') else None, tab_no=int(num), horse=v['horse'],
                barrier=float(v['draw']) if str(v.get('draw') or '').isdigit() else None, finish=v['pla'],
                time_s=_secs(v['time']), race_time_s=win_t, beaten_margin_l=v['lbw'],
                rail_avg_m=round(sum(rails) / len(rails), 2) if len(rails) >= 2 else None, n_snapshots=len(rails),
                field_size=n_field, source='hkjc_aerial'))
            for k in range(4):
                f = v['frames'][k]
                if not f:
                    continue
                pos, gap, nv = pos_by_frame[k][num]
                secs.append(dict(meet_code=code, race_no=int(rn), tab_no=int(num), horse=v['horse'], to_go_m=TO_GO_M[k], snapshot=k,
                                 pos=pos, n_visible=nv, gap_l=round(gap, 2), gap_m=round(gap * LENGTH_M, 1), rail_m=f['rail_m'], x_px=f['x']))
    return pd.DataFrame(runs), pd.DataFrame(secs)


def write_gps(meeting):
    """Merge one meeting into data/gps/hk_gps_{runs,sections}_<year>.parquet (key columns de-duplicated, only a changed year rewritten)."""
    runs, secs = gps_tables(meeting)
    year = meeting['date'][:4]
    os.makedirs(GPS_DIR, exist_ok=True)
    for name, new in (('hk_gps_runs', runs), ('hk_gps_sections', secs)):
        if new.empty:
            continue
        path = os.path.join(GPS_DIR, '%s_%s.parquet' % (name, year))
        old = pd.read_parquet(path) if os.path.exists(path) else None
        all_ = pd.concat([old, new], ignore_index=True) if old is not None else new
        all_ = all_.drop_duplicates(KEYS[name], keep='last').sort_values(KEYS[name]).reset_index(drop=True)
        if old is None or not all_.equals(old.sort_values(KEYS[name]).reset_index(drop=True)):
            all_.to_parquet(path, index=False)
        print('%s %s: %d rows' % (name, year, len(all_)))


def build_meeting(d, course, bank):
    races = {}
    for n in range(1, 13):
        r = build_race(d, course, n, bank)
        if r is None:
            break
        races[str(n)] = r
        print('R%d' % n, 'dots' if 'runners' in r else r.get('err'), flush=True)
    os.makedirs(OUT, exist_ok=True)
    p = os.path.join(OUT, '%s_%s.json' % (d.replace('/', ''), course))
    meeting = dict(date=d, course=course, source='HKJC aerial replay', races=races)
    json.dump(meeting, open(p, 'w'), separators=(',', ':'))
    print('wrote', p)
    write_gps(meeting)


def auto(days):
    import datetime
    bank = X.build_bank(np.asarray(Image.open(X.SEED_IMAGE).convert('RGB')).astype(int))
    today = datetime.date.today()
    for back in range(days, 0, -1):
        d = (today - datetime.timedelta(days=back)).strftime('%Y/%m/%d')
        for course in ('HV', 'ST'):
            if os.path.exists(os.path.join(OUT, '%s_%s.json' % (d.replace('/', ''), course))):
                continue
            rows, _ = parse(fetch(d, course, 1))
            if not rows:
                continue            # no meeting at this course that day
            if image(d, 1) is None:
                print(d, course, 'no image yet')
                continue
            print(d, course, 'building', flush=True)
            build_meeting(d, course, bank)


def main():
    if sys.argv[1] == '--gps-only':        # rebuild the data/gps tables from the saved meeting files
        for f in sorted(os.listdir(OUT)):
            write_gps(json.load(open(os.path.join(OUT, f))))
        return
    if sys.argv[1] == '--auto':
        auto(int(sys.argv[2]) if len(sys.argv) > 2 else 21)
        return
    d, course = sys.argv[1], sys.argv[2]
    bank = X.build_bank(np.asarray(Image.open(X.SEED_IMAGE).convert('RGB')).astype(int))
    build_meeting(d, course, bank)


if __name__ == '__main__':
    main()
