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


_OCR = None
THICK = 7.0                 # every map is scaled so its main track strip is this many SVG units wide (consistent line weight)
DIST = re.compile(r'^(\d{3,4})m?$')


def ocr_boxes(im):
    """Text found on a map by RapidOCR (3x upscale): list of (text, centre x, centre y, width, height, angle) in source pixels."""
    global _OCR
    if _OCR is None:
        from rapidocr_onnxruntime import RapidOCR
        _OCR = RapidOCR()
    big = im.resize((im.width * 3, im.height * 3), Image.LANCZOS)
    res, _ = _OCR(np.array(big)[:, :, ::-1])
    out = []
    for box, txt, conf in res or []:
        pts = np.array(box, float) / 3
        w = np.hypot(*(pts[1] - pts[0]))
        h = np.hypot(*(pts[3] - pts[0]))
        ang = float(np.degrees(np.arctan2(pts[1][1] - pts[0][1], pts[1][0] - pts[0][0])))
        out.append((txt.strip(), pts, float(w), float(h), ang))
    return out


def clean_label(txt):
    t = txt.replace(' ', '').replace('O', '0').replace('o', '0').replace('d', '0').replace('l', '1').replace('I', '1')
    m = re.fullmatch(r'(\d{3,4})m?', t, flags=re.I)
    return int(m.group(1)) if m and 800 <= int(m.group(1)) <= 3600 else None


def trace(gif_bytes, slug=''):
    """Clean, consistent vector map: text is read with OCR and removed, the track strokes are traced and scaled to a common stroke width, and the distance labels,
    'Winning post' and the arrows are redrawn in one typeface at one size. A label OCR cannot read as a distance (or a known word) is left as it was drawn."""
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
    h0, w0 = ink.shape
    labels = []        # (text, x, y, angle, kind)
    erase = np.zeros_like(ink)
    words = {}
    for txt, pts, w, h, ang in ocr_boxes(im):
        low = txt.lower().replace(' ', '')
        parts = re.findall(r'\d{3,4}m?', txt.replace(' ', ''))
        poly = pts.astype(np.int32)
        cx, cy = pts.mean(axis=0)
        if len(parts) >= 2 and all(clean_label(x) for x in parts):
            for i, x in enumerate(parts):          # two labels glued together: split the box between them
                f = (i + 0.5) / len(parts)
                p = pts[0] + (pts[1] - pts[0]) * f + (pts[3] - pts[0]) * 0.5
                labels.append((f'{clean_label(x)}m', p[0], p[1], ang, 'dist'))
            cv2.fillPoly(erase, [poly], 255)
        elif clean_label(txt):
            labels.append((f'{clean_label(txt)}m', cx, cy, ang, 'dist'))
            cv2.fillPoly(erase, [poly], 255)
        elif low in ('winning', 'post'):
            words.setdefault('post', []).append((cx, cy, h, ang))
            cv2.fillPoly(erase, [poly], 255)
        elif low in ('start', 'steeple', 'track', 'startt') or 'start' in low:
            cv2.fillPoly(erase, [poly], 255)       # "START" captions and steeple wording are dropped
    if 'post' in words:
        ws = words['post']
        cx = sum(x for x, _, _, _ in ws) / len(ws)
        cy = sum(y for _, y, _, _ in ws) / len(ws)
        labels.append(('Winning post', cx, cy, 0.0, 'post'))
    erase = cv2.dilate(erase, np.ones((3, 3), np.uint8))
    ink_c = ink.copy()
    ink_c[erase > 0] = 0
    red_c = np.zeros_like(ink)
    # stroke width of the main strip: 90th percentile of the distance transform over the cleaned ink
    dt = cv2.distanceTransform((ink_c > 0).astype(np.uint8), cv2.DIST_L2, 3)
    half = float(np.percentile(dt[ink_c > 0], 90)) if (ink_c > 0).any() else 3.0
    S = THICK / max(2 * half, 1.0)
    ys, xs = np.nonzero(ink_c)
    x0, x1, y0, y1 = xs.min(), xs.max(), ys.min(), ys.max()
    for t, x, y, ang, kind in labels:
        wlab = (len(t) * 5.2 / S) / 2 + 3
        x0, x1 = min(x0, x - wlab), max(x1, x + wlab)
        y0, y1 = min(y0, y - 6 / S), max(y1, y + 6 / S)
    pad = 8 / S
    x0, y0, x1, y1 = x0 - pad, y0 - pad, x1 + pad, y1 + pad
    path = layer_scaled(ink_c, S, x0, y0)
    texts = ''
    for t, x, y, ang, kind in labels:
        X, Y = (x - x0) * S, (y - y0) * S
        if ang > 90:
            ang -= 180
        if ang < -90:
            ang += 180
        ang = 0.0 if abs(ang) < 4 else max(-40.0, min(40.0, ang))
        cls = 'acc' if kind == 'post' else 'lbl'
        texts += f'<text class="{cls}" x="{X:.1f}" y="{Y:.1f}" transform="rotate({ang:.0f} {X:.1f} {Y:.1f})">{t}</text>'
    W, H = (x1 - x0) * S, (y1 - y0) * S
    return W, H, path, texts


def layer_scaled(mask, S, x0, y0):
    big = cv2.resize(mask, None, fx=UP, fy=UP, interpolation=cv2.INTER_CUBIC)
    big = cv2.GaussianBlur(big, (0, 0), UP * BLUR)
    _, bw = cv2.threshold(big, 127, 255, cv2.THRESH_BINARY)
    cs, hier = cv2.findContours(bw, cv2.RETR_CCOMP, cv2.CHAIN_APPROX_NONE)
    parts = []
    for c in cs:
        if abs(cv2.contourArea(c)) < 1.5 * UP * UP:
            continue
        c = cv2.approxPolyDP(c, UP * EPS, True)
        p = (c.reshape(-1, 2).astype(float) / UP - [x0, y0]) * S
        n = len(p)
        if n < 3:
            continue
        mid = (p + np.roll(p, -1, axis=0)) / 2
        d = f'M{mid[-1][0]:.1f} {mid[-1][1]:.1f}' + ''.join(f'Q{p[i][0]:.1f} {p[i][1]:.1f} {mid[i][0]:.1f} {mid[i][1]:.1f}' for i in range(n)) + 'Z'
        parts.append(d)
    return ''.join(parts)


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
            w, h, ink, texts = trace(gif, slug)
        except Exception as e:
            print('skip', base, e)
            continue
        svg = (f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {w:.0f} {h:.0f}">'
               f'<path class="ink" fill-rule="evenodd" d="{ink}"/>{texts}</svg>')
        open(os.path.join(OUT, slug + '.svg'), 'w').write(svg)
        title = re.sub(r'\s+', ' ', re.sub(r'(?i)\s*(racecourse|track map).*', '', base.replace('_', ' ').replace('%20', ' '))).strip().title()
        out[slug] = {'name': title, 'w': round(w), 'h': round(h)}
    json.dump({'source': 'racerate.com, traced', 'maps': out}, open('track_maps.json', 'w'), separators=(',', ':'))
    print(len(out), 'maps ->', OUT, sum(os.path.getsize(os.path.join(OUT, f)) for f in os.listdir(OUT)) // 1024, 'KB')


if __name__ == '__main__':
    main()
