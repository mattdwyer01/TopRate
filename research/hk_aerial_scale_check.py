"""Scale check for the HKJC aerial image extractor (22 Oct 2026): pixels per length, race by race, against HKJC's own results.

For each race of the 2026-27 meetings listed in MEETINGS, fetch the results page (placings, lengths behind) and the _L aerial image,
read the finish frame with hk_aerial_extract, and fit dot x offset from the winner against official lengths behind (with intercept).
Prints the per course median slope. Run: python research/hk_aerial_scale_check.py   (needs network, about 2 minutes)
"""
import concurrent.futures as cf
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

UA = {'User-Agent': 'Mozilla/5.0'}
MEETINGS = {'2026/09/06': 'ST', '2026/09/09': 'HV', '2026/09/13': 'ST', '2026/09/16': 'HV', '2026/09/23': 'HV',
            '2026/09/27': 'ST', '2026/10/04': 'ST', '2026/10/07': 'HV', '2026/10/11': 'ST', '2026/10/14': 'HV'}
def fetch(d, course, n):
    u=f"https://racing.hkjc.com/en-us/local/information/localresults?racedate={d}&Racecourse={course}&RaceNo={n}"
    for _ in range(3):
        try: return urllib.request.urlopen(urllib.request.Request(u,headers=UA),timeout=40).read().decode('utf8','ignore')
        except Exception as e: err=e
    return ''
FR={'N':0.25,'SH':0.1,'HD':0.2,'SN':0.05,'NOSE':0.05,'NS':0.05}
def lbw(s):
    s=s.strip().upper()
    if s in('---','-',''): return 0.0
    if s.startswith('DH'): return 0.0
    tot=0.0
    for part in s.replace('-',' ').split():
        if part in FR: tot+=FR[part]
        elif '/' in part:
            a,b=part.split('/'); tot+=int(a)/int(b)
        else:
            try: tot+=float(part)
            except: return None
    return tot
def parse(t):
    t=re.sub(r'<script.*?</script>|<style.*?</style>','',t,flags=re.S)
    out=[]
    for r in re.findall(r'<tr[^>]*>(.*?)</tr>',t,flags=re.S):
        cells=[re.sub(r'\\s+',' ',html.unescape(re.sub(r'<[^>]+>',' ',c))).strip() for c in re.findall(r'<t[dh][^>]*>(.*?)</t[dh]>',r,flags=re.S)]
        cells=[re.sub(r'\s+',' ',c) for c in cells]
        if len(cells)>=10 and cells[0].isdigit() and cells[1].isdigit() and re.match(r'^[\d ]+$',cells[9] or 'x'):
            out.append(dict(pla=int(cells[0]),num=int(cells[1]),horse=cells[2],dr=cells[7],lbw=lbw(cells[8]),lbw_raw=cells[8],run=cells[9],time=cells[10]))
    dist=re.search(r'(\d{3,4})M',t)
    return out, dist.group(1) if dist else None


def load(d, n):
    s = d.replace('/', '')
    u = f"https://racing.hkjc.com/general/-/media/Sites/JCRW/RaceResult/26_27/{s}/{s}R{n}_Aerial_L.jpg"
    try:
        return X.load_image(urllib.request.urlopen(urllib.request.Request(u, headers=UA), timeout=40).read())
    except Exception:
        return None


def one(args, bank):
    d, n = args
    c = MEETINGS[d]
    rows, dist = parse(fetch(d, c, n))
    if not rows:
        return None
    im = load(d, n)
    if im is None or im.shape[:2] != (1800, 800):
        return dict(date=d, course=c, race=n, err='no image')
    try:
        fin = X.read_frame(im, 3 * X.FRAME_H, bank)
    except Exception as e:
        return dict(date=d, course=c, race=n, err='read failed: %s' % type(e).__name__)
    byn = {r['num']: r for r in rows}
    win = [r for r in rows if r['pla'] == 1][0]
    dots = {f['num']: f for f in fin}
    if win['num'] not in dots:
        return dict(date=d, course=c, race=n, err='winner dot missing')
    pts = [(byn[k]['lbw'], abs(dots[k]['x'] - dots[win['num']]['x'])) for k in dots if k in byn and byn[k]['lbw'] is not None]
    if len(pts) < 4:
        return dict(date=d, course=c, race=n, err='few points')
    L = np.array([p[0] for p in pts])
    dx = np.array([p[1] for p in pts])
    (a, b), _, _, _ = np.linalg.lstsq(np.c_[np.ones_like(L), L], dx, rcond=None)
    return dict(date=d, course=c, race=n, dist=dist, n=len(pts), a=round(float(a), 1), b=round(float(b), 1),
                r=round(float(np.corrcoef(L, dx)[0, 1]), 3), maxL=float(L.max()), unknown=[k for k in dots if k not in byn])


if __name__ == '__main__':
    bank = X.build_bank(np.asarray(Image.open(X.SEED_IMAGE).convert('RGB')).astype(int))
    jobs = [(d, n) for d in MEETINGS for n in range(1, 12)]
    with cf.ThreadPoolExecutor(6) as ex:
        res = [r for r in ex.map(lambda j: one(j, bank), jobs) if r]
    ok = [r for r in res if 'err' not in r and r['maxL'] <= 16]    # a field spread over 16 lengths runs off the frame
    print(len(res), 'races,', sum('err' in r for r in res), 'failed,', len(ok), 'used')
    for c in ('HV', 'ST'):
        b = np.array([r['b'] for r in ok if r['course'] == c])
        print(c, len(b), 'races: median %.1f mean %.1f sd %.1f px per length' % (np.median(b), b.mean(), b.std()), '=> %.4f m/px at 2.4 m a length' % (2.4 / np.median(b)))
    json.dump(res, open('hk_aerial_scale_check.json', 'w'))
