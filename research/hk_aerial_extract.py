"""Prototype (22 Oct 2026): read runner positions out of an HKJC aerial virtual replay image.

Image: https://racing.hkjc.com/general/-/media/Sites/JCRW/RaceResult/{season}/{YYYYMMDD}/{YYYYMMDD}R{n}_Aerial_L.jpg
(800x1800 = four 800x450 frames: leader at about 780m, 410m and 200m to go, and the finish; numbered blue dots, one per runner).
Output per frame: saddle number, x (pixels along the track, direction flips between frames 0-1 and 2-3) and metres to the rail.
Digit templates are harvested from the SEED dots of the 14 Oct 2026 Happy Valley R1 image, so other images need the same font only.
Run: python research/hk_aerial_extract.py aerial_L.jpg
"""
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


def find_dots(mask):
    """Greedy disc fit: a dot is a disc lying wholly inside the (filled) blue mask that explains new pixels."""
    d = disc(RAD)
    area = d.sum()
    inside = fftconvolve(mask.astype(float), d, mode='same')   # mask pixels under the disc
    covered = np.zeros_like(mask, dtype=bool)
    dots = []
    for _ in range(40):
        new = fftconvolve((mask & ~covered).astype(float), d, mode='same')
        ok = inside >= area * 0.97
        score = np.where(ok, new, -1)
        y, x = np.unravel_index(np.argmax(score), score.shape)
        if score[y, x] < area * 0.12:
            break
        dots.append((y, x, float(score[y, x] / area)))
        yy, xx = np.ogrid[:mask.shape[0], :mask.shape[1]]
        covered |= (yy - y) ** 2 + (xx - x) ** 2 <= RAD * RAD
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


def build_bank(im):
    bank = {}
    for d, (x, y) in SEED.items():
        bank[d] = norm(split_digits(white_glyph(im, y, x))[0])
    for n, (x, y) in SEED_TWO.items():
        parts = split_digits(white_glyph(im, y, x))
        bank.setdefault(0 if n == 10 else 99, norm(parts[1]))
    bank.pop(99, None)
    return bank


def read_frame(im, y0, bank, maxn=16):
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
    nums = list(range(1, maxn + 1))
    M = np.array([[r[3][n] for n in nums] for r in rows])
    ri, ci = linear_sum_assignment(-M)
    out = []
    for i, j in zip(ri, ci):
        out.append(dict(num=nums[j], x=int(rows[i][1]), y=int(rows[i][0] + y0), vis=round(rows[i][2], 2), iou=round(float(M[i, j]), 2)))
    return sorted(out, key=lambda d: d['num'])


M_PER_PX = 0.057   # from the margin fit on the 14 Oct 2026 HV R1 image (40-44 px per length, 2.4 m a length)
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
                            rail_m=None if px is None else round(px * M_PER_PX, 1)))
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
            out.append(dict(frame=k, num=d['num'], x=d['x'], rail_px=px, rail_m=None if px is None else round(px * M_PER_PX, 1)))
    return out


if __name__ == '__main__':
    import json
    path = sys.argv[1]
    im = np.asarray(Image.open(path).convert('RGB')).astype(int)
    bank = build_bank(im)
    frames = [read_frame(im, k * FRAME_H, bank) for k in range(4)]
    lat = lateral2(im, frames)
    table = {}
    for r in lat:
        table.setdefault(r['num'], {})[['m780', 'm410', 'm200', 'fin'][r['frame']]] = dict(x=r['x'], rail_m=r['rail_m'])
    print(json.dumps(dict(source=path, frames=[len(f) for f in frames], runners=table), indent=1))
