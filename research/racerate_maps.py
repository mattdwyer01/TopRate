"""Vectorise the racerate.com track plan maps (21 Oct 2026, owner's request: use those maps, better visual quality).
www.racerate.com/trackinformation.htm links a page per course; each page carries a small black-and-white GIF plan map (home straight at the bottom, winning post,
start posts with distances, chutes). The GIFs are 300 to 450 px and pixelated, so each is traced into a smooth SVG (4x upscale, blur, threshold, contours smoothed
with quadratic curves) in two layers, ink (black) and accent (red text such as 'Winning Post'), written to track_maps/<slug>.svg with an index track_maps.json
{slug: {name, w, h}} at the repo root; the dashboard inlines the SVG and colours the layers from its theme. Source: racerate.com (copyright notice on the site).
usage: python research/racerate_maps.py [--cache DIR]   (needs opencv-python-headless, numpy, pillow, requests)"""
import json
import os
import re
import sys
import time

import cv2
import numpy as np
import requests
from PIL import Image

BASE = 'https://www.racerate.com/'
UP = 8                      # upscale before tracing
BLUR = 0.2                  # blur sigma as a share of UP (light: heavier smoothing turns the small text into blobs)
EPS = 0.12                  # contour simplification in source pixels
OUT = 'track_maps'
UA = {'User-Agent': 'Mozilla/5.0'}


def get(url, cache=None, name=None):
    if cache and name and os.path.exists(os.path.join(cache, name)):
        return open(os.path.join(cache, name), 'rb').read()
    r = requests.get(url, headers=UA, timeout=30)
    r.raise_for_status()
    time.sleep(0.3)
    if cache and name:
        os.makedirs(cache, exist_ok=True)
        open(os.path.join(cache, name), 'wb').write(r.content)
    return r.content


def smooth_path(c, scale):
    """Closed quadratic-curve path through the midpoints of a simplified contour (a cheap Chaikin-style smoothing)."""
    p = c.reshape(-1, 2).astype(float) / scale
    n = len(p)
    if n < 3:
        return ''
    mid = (p + np.roll(p, -1, axis=0)) / 2
    d = f'M{mid[-1][0]:.1f} {mid[-1][1]:.1f}'
    for i in range(n):
        d += f'Q{p[i][0]:.1f} {p[i][1]:.1f} {mid[i][0]:.1f} {mid[i][1]:.1f}'
    return d + 'Z'


def layer(mask, min_area):
    big = cv2.resize(mask, None, fx=UP, fy=UP, interpolation=cv2.INTER_CUBIC)
    big = cv2.GaussianBlur(big, (0, 0), UP * BLUR)
    _, bw = cv2.threshold(big, 127, 255, cv2.THRESH_BINARY)
    cs, hier = cv2.findContours(bw, cv2.RETR_CCOMP, cv2.CHAIN_APPROX_NONE)
    parts = []
    for c in cs:
        if abs(cv2.contourArea(c)) < min_area * UP * UP:
            continue
        c = cv2.approxPolyDP(c, UP * EPS, True)
        d = smooth_path(c, UP)
        if d:
            parts.append(d)
    return ''.join(parts)


# Parts of a map to wipe before tracing (source pixel polygons): things that no longer exist on the course. Flemington's steeple track (outer loop and its labels) is gone.
BLANK = {
    'flemington': [[(50, 0), (165, 0), (158, 22), (140, 30), (122, 50), (113, 75), (112, 100), (116, 125), (124, 140), (60, 140), (50, 100)],
                   [(131, 80), (184, 80), (184, 104), (131, 104)]],
}


def trace(gif_bytes, slug=''):
    import io
    im = Image.open(io.BytesIO(gif_bytes)).convert('RGB')
    for poly in BLANK.get(slug, []):
        from PIL import ImageDraw
        ImageDraw.Draw(im).polygon(poly, fill=(255, 255, 255))
    a = np.array(im).astype(int)
    r, g, b = a[..., 0], a[..., 1], a[..., 2]
    luma = (r * 299 + g * 587 + b * 114) // 1000
    red = (r > 140) & (g < 110) & (b < 110)
    ink = ((luma < 185) & ~red).astype(np.uint8) * 255
    acc = red.astype(np.uint8) * 255
    h, w = ink.shape
    return w, h, layer(ink, 1.5), layer(acc, 1.5) if acc.any() else ''


def main():
    cache = sys.argv[sys.argv.index('--cache') + 1] if '--cache' in sys.argv else None
    idx = get(BASE + 'trackinformation.htm', cache, 'index.htm').decode('latin-1')
    pages = sorted(set(re.findall(r'href="(Track%20Info/[^"]+\.htm)"', idx, flags=re.I)))
    os.makedirs(OUT, exist_ok=True)
    out = {}
    for p in pages:
        base = os.path.basename(p)[:-4]
        slug = re.sub(r'[^a-z0-9]', '', base.lower().replace('%20', ''))
        try:
            html = get(BASE + p, cache, base + '.htm').decode('latin-1')
            m = re.search(r'src="\.\./(TRACK_MAPS/[^"]+)"', html, flags=re.I)
            if not m:
                continue
            gif = get(BASE + m.group(1), cache, 'g_' + os.path.basename(m.group(1)))
            w, h, ink, acc = trace(gif, slug)
        except Exception as e:
            print('skip', base, e)
            continue
        svg = (f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {w} {h}">'
               f'<path class="ink" fill-rule="evenodd" d="{ink}"/>' + (f'<path class="acc" fill-rule="evenodd" d="{acc}"/>' if acc else '') + '</svg>')
        open(os.path.join(OUT, slug + '.svg'), 'w').write(svg)
        title = re.sub(r'\s+', ' ', re.sub(r'(?i)\s*(racecourse|track map).*', '', base.replace('_', ' ').replace('%20', ' '))).strip().title()
        out[slug] = {'name': title, 'w': w, 'h': h}
    json.dump({'source': 'racerate.com, traced', 'maps': out}, open('track_maps.json', 'w'), separators=(',', ':'))
    print(len(out), 'maps ->', OUT, sum(os.path.getsize(os.path.join(OUT, f)) for f in os.listdir(OUT)) // 1024, 'KB')


if __name__ == '__main__':
    main()
