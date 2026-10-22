"""Prototype (22 Oct 2026): read runner positions out of an HKJC aerial virtual replay image.

Image: https://racing.hkjc.com/general/-/media/Sites/JCRW/RaceResult/{season}/{YYYYMMDD}/{YYYYMMDD}R{n}_Aerial_L.jpg
(800x1800 = four 800x450 frames: leader at about 780m, 410m and 200m to go, and the finish; numbered blue dots, one per runner).
Output per frame: saddle number, x (pixels along the track, direction flips between frames 0-1 and 2-3) and metres to the rail.
Digit templates are harvested from the SEED dots of the 14 Oct 2026 Happy Valley R1 image, so other images need the same font only.
Run: python research/hk_aerial_extract.py aerial_L.jpg
"""
import os
import sys
import numpy as np
from PIL import Image, ImageDraw, ImageFont
from scipy import ndimage as ndi
from scipy.optimize import linear_sum_assignment
from scipy.signal import fftconvolve

FRAME_H = 450
RAD = 19.5
FONT = '/usr/share/fonts/truetype/liberation/LiberationSans-Bold.ttf'


def dot_mask(im):
    R, G, B = im[..., 0], im[..., 1], im[..., 2]
    m = (B > 170) & (R < 110) & (G > 70) & (G < 175) & (B - R > 110)
    m = ndi.binary_closing(m, iterations=2)
    return ndi.binary_fill_holes(m)


def disc(r):
    k = int(np.ceil(r)) + 1
    yy, xx = np.mgrid[-k:k + 1, -k:k + 1]
    return (yy ** 2 + xx ** 2 <= r * r).astype(float)


def est_radius(mask):
    """Dot radius from the isolated blobs (single dots are 700 to 1500 px); falls back to RAD."""
    lab, n = ndi.label(mask)
    if n == 0:
        return RAD
    a = np.asarray(ndi.sum(mask, lab, range(1, n + 1)))
    a = a[(a > 700) & (a < 1500)]
    return float(np.sqrt(np.median(a) / np.pi)) if len(a) >= 3 else RAD


def find_dots(mask):
    """Greedy disc fit: a dot is a disc lying wholly inside the (filled) blue mask that explains new pixels."""
    rad = est_radius(mask)
    d = disc(rad)
    area = d.sum()
    inside = fftconvolve(mask.astype(float), d, mode='same')   # mask pixels under the disc
    covered = np.zeros_like(mask, dtype=bool)
    dots = []
    for _ in range(40):
        new = fftconvolve((mask & ~covered).astype(float), d, mode='same')
        ok = inside >= area * 0.93
        score = np.where(ok, new, -1)
        y, x = np.unravel_index(np.argmax(score), score.shape)
        if score[y, x] < area * 0.12:
            break
        dots.append((y, x, float(score[y, x] / area)))
        yy, xx = np.ogrid[:mask.shape[0], :mask.shape[1]]
        covered |= (yy - y) ** 2 + (xx - x) ** 2 <= rad * rad
    return dots


def white_glyph(im, y, x):
    sub = im[y - 17:y + 18, x - 17:x + 18]
    if sub.shape[:2] != (35, 35):
        return None
    yy, xx = np.mgrid[-17:18, -17:18]
    inr = yy ** 2 + xx ** 2 <= 16 ** 2
    w = (sub.min(axis=2) > 165) & inr
    # keep blobs of real glyph size only (drops the white ring edge of neighbouring dots)
    lab, n = ndi.label(w)
    keep = np.zeros_like(w)
    for i in range(1, n + 1):
        if (lab == i).sum() >= 14:
            keep |= lab == i
    if keep.sum() < 20:
        return None
    ys, xs = np.where(keep)
    return keep[ys.min():ys.max() + 1, xs.min():xs.max() + 1]


def split_digits(g):
    """One or two digits: a wide glyph is cut at its sparsest column near the middle."""
    h, w = g.shape
    if w / h < 0.95:
        return [g]
    lo, hi = int(w * 0.35), int(w * 0.65) + 1
    cut = lo + int(np.argmin(g[:, lo:hi].sum(axis=0)))
    out = []
    for part in (g[:, :cut], g[:, cut:]):
        ys, xs = np.where(part)
        if len(ys):
            out.append(part[ys.min():ys.max() + 1, xs.min():xs.max() + 1])
    return out


def norm(g, size=(24, 32)):
    h, w = g.shape
    nw = max(1, int(round(w * size[1] / h)))
    img = Image.fromarray((g * 255).astype('uint8')).resize((nw, size[1]), Image.BILINEAR)
    a = np.asarray(img) > 110
    canvas = np.zeros((size[1], size[0]), bool)
    x0 = max(0, (size[0] - nw) // 2)
    canvas[:, x0:x0 + min(nw, size[0])] = a[:, :size[0]]
    return canvas


def iou(a, b):
    return (a & b).sum() / max((a | b).sum(), 1)


# seed dots for the 14 Oct 2026 Happy Valley R1 image (frame 0): digit -> (x, y), used once to harvest templates
SEED = {2: (282, 219), 3: (196, 251), 4: (82, 187), 5: (124, 218), 6: (112, 253), 7: (277, 252), 8: (202, 218), 9: (160, 184),
        1: (477, 250)}
SEED_TWO = {10: (456, 217), 12: (375, 217)}


SEED_IMAGE = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'hk_aerial_sample', '20261014_HV_R1_Aerial_L.jpg')


def build_bank(im):
    bank = {}
    for d, (x, y) in SEED.items():
        bank[d] = norm(split_digits(white_glyph(im, y, x))[0])
    for n, (x, y) in SEED_TWO.items():
        parts = split_digits(white_glyph(im, y, x))
        bank.setdefault(0 if n == 10 else 99, norm(parts[1]))
    bank.pop(99, None)
    return bank


def read_frame(im, y0, bank, maxn=16, field=None, thr=0.40):
    """Dots of one frame with their saddle numbers. With `field` (the race's horse numbers) only those numbers can be
    assigned (one dot each, Hungarian) and a dot whose best score is under `thr` is left unlabelled (num None) rather than
    forced onto a wrong number; without it numbers 1..maxn are used as before."""
    fr = im[y0:y0 + FRAME_H]
    dots = find_dots(dot_mask(fr))
    rows = []
    for (y, x, s) in dots:
        g = white_glyph(fr, y, x)
        parts = split_digits(g) if g is not None else []
        per = [{d: iou(norm(p), t) for d, t in bank.items()} for p in parts]
        sc = {}
        for n in range(1, maxn + 1):
            ds = [int(c) for c in str(n)]
            sc[n] = float(np.mean([p[d] for p, d in zip(per, ds)])) if len(ds) == len(per) and per else 0.0
        rows.append((y, x, s, sc))
    if not rows:
        return []
    nums = sorted(field) if field else list(range(1, maxn + 1))
    M = np.array([[r[3][n] for n in nums] for r in rows])
    ri, ci = linear_sum_assignment(-M)
    out = []
    for i, j in zip(ri, ci):
        num = nums[j] if (not field or M[i, j] >= thr) else None
        out.append(dict(num=num, x=int(rows[i][1]), y=int(rows[i][0] + y0), vis=round(rows[i][2], 2), iou=round(float(M[i, j]), 2)))
    return sorted(out, key=lambda d: (d['num'] is None, d['num'] or 0, d['x']))


def relabel_finish(dots, placings, sep=45):
    """Finish frame: the frame is cut at the line, so dots sorted by distance from the winner are the placings in order.
    `placings` = horse numbers in finish order. Dots at least `sep` px from every neighbour (order unambiguous) take the
    placing label, which overrides the digit reader; returns how many labels changed. The direction (winner at left or
    right) is chosen by whichever gives the smaller disagreement with the reader."""
    if len(dots) < 3 or len(placings) < 3:
        return 0
    best = None
    for rev in (False, True):
        ds = sorted(dots, key=lambda d: d['x'], reverse=rev)
        k = min(len(ds), len(placings))
        agree = sum(1 for d, n in zip(ds[:k], placings[:k]) if d['num'] == n)
        if best is None or agree > best[0]:
            best = (agree, ds[:k], placings[:k])
    agree, ds, pl = best
    if agree < max(3, len(ds) // 2):
        return 0        # reader and finish order disagree broadly: do not trust either direction
    xs = [d['x'] for d in dots]
    changed = 0
    for d, n in zip(ds, pl):
        if min([abs(d['x'] - x) for x in xs if x != d['x']] or [99]) >= sep and d['num'] != n:
            d['num'] = n
            changed += 1
    return changed


# metres per pixel at 2.4 m a length, from the official lengths-behind fit over 95 races of 2026-27 (research/hk_aerial_scale_check.py):
# Happy Valley 42.8 px a length (0.056), Sha Tin 40.8 (0.059), about 9% sd per race
M_PER_PX = {'HV': 0.056, 'ST': 0.059}
M_PER_PX_DEFAULT = 0.058
RAIL_T = 205


def rail_pixels(fr):
    """Thin white line(s) spanning the frame: the rail (straight, or an arc on a bend)."""
    w = fr.min(axis=2) > RAIL_T
    thick = ndi.binary_opening(w, structure=np.ones((9, 1), bool))
    thin = w & ~ndi.binary_dilation(thick, iterations=1)
    lab, n = ndi.label(thin, structure=np.ones((3, 3), bool))
    keep = np.zeros_like(thin)
    for i, sl in enumerate(ndi.find_objects(lab), 1):
        wd = sl[1].stop - sl[1].start
        ht = sl[0].stop - sl[0].start
        if wd >= 350 and ht <= 140 and (lab[sl] == i).sum() >= 300:
            keep |= lab == i
    return keep


def lateral(im, dots_by_frame):
    out = []
    for k, res in enumerate(dots_by_frame):
        fr = im[k * FRAME_H:(k + 1) * FRAME_H]
        rail = rail_pixels(fr)
        dist = ndi.distance_transform_edt(~rail) if rail.any() else None
        for d in res:
            y_local = d['y'] - k * FRAME_H
            px = float(dist[y_local, d['x']]) if dist is not None else None
            out.append(dict(frame=k, num=d['num'], x=d['x'], rail_px=None if px is None else round(px, 1),
                            rail_m=None if px is None else round(px * M_PER_PX_DEFAULT, 1)))
    return out


def rail_scan(fr, dots_local, y, x, thr=195, maxd=260):
    """First thin bright line met moving away from the dot (up or down), skipping other dots. Returns pixel distance."""
    H, W = fr.shape[:2]
    inside = np.zeros((H, W), bool)
    yy, xx = np.ogrid[:H, :W]
    for (dy_, dx_) in dots_local:
        inside |= (yy - dy_) ** 2 + (xx - dx_) ** 2 <= 23 ** 2
    best = None
    for sgn in (1, -1):
        run = 0
        for d in range(int(RAD) + 2, maxd):
            yy_ = y + sgn * d
            if not (0 <= yy_ < H):
                break
            col = fr[yy_, max(0, x - 2):x + 3].min(axis=1)
            white = (col > thr).all() and not inside[yy_, x]
            if white:
                run += 1
            else:
                if 1 <= run <= 8:
                    best = d - run if best is None else min(best, d - run)
                    break
                run = 0
    return best


def lateral2(im, dots_by_frame):
    out = []
    for k, res in enumerate(dots_by_frame):
        fr = im[k * FRAME_H:(k + 1) * FRAME_H]
        loc = [(d['y'] - k * FRAME_H, d['x']) for d in res]
        for d in res:
            px = rail_scan(fr, loc, d['y'] - k * FRAME_H, d['x'])
            out.append(dict(frame=k, num=d['num'], x=d['x'], rail_px=px, rail_m=None if px is None else round(px * M_PER_PX_DEFAULT, 1)))
    return out


def load_image(path_or_bytes):
    """800x1800 RGB array. The 6 Sep 2026 images are published at half size (400x900): upscale them."""
    import io
    im = Image.open(io.BytesIO(path_or_bytes) if isinstance(path_or_bytes, bytes) else path_or_bytes).convert('RGB')
    if im.size == (400, 900):
        im = im.resize((800, 1800), Image.LANCZOS)
    return np.asarray(im).astype(int)


if __name__ == '__main__':
    import json
    path = sys.argv[1]
    im = load_image(path)
    bank = build_bank(np.asarray(Image.open(SEED_IMAGE).convert('RGB')).astype(int))
    frames = [read_frame(im, k * FRAME_H, bank) for k in range(4)]
    lat = lateral2(im, frames)
    table = {}
    for r in lat:
        table.setdefault(r['num'], {})[['m780', 'm410', 'm200', 'fin'][r['frame']]] = dict(x=r['x'], rail_m=r['rail_m'])
    print(json.dumps(dict(source=path, frames=[len(f) for f in frames], runners=table), indent=1))
