"""Draw a track card SVG from an OSM ring plus start/finish/chute marks (21 Oct 2026 preview of the 'draw it ourselves' option).
usage: python research/track_card_svg.py OUT_DIR slug[,slug...] [race_distance]"""
import json
import math
import os
import sys

W, H, PAD = 360, 230, 34


def render(t, race_dist=None):
    pts = [tuple(p) for p in t['pts']]
    n0 = len(pts)
    a, b = pts[t['s0'] % n0], pts[(t['s0'] + t['sn']) % n0]
    th = math.atan2(b[1] - a[1], b[0] - a[0])
    rot = lambda p, ang: (p[0] * math.cos(-ang) - p[1] * math.sin(-ang), p[0] * math.sin(-ang) + p[1] * math.cos(-ang))
    R = [rot(p, th) for p in pts]
    cy = sum(p[1] for p in R) / n0
    sy = (R[t['s0'] % n0][1] + R[(t['s0'] + t['sn']) % n0][1]) / 2
    if sy > cy:
        th += math.pi
        R = [rot(p, th) for p in pts]
    tr = lambda p: rot(p, th)
    fin = tr(t['fin']) if t.get('fin') else None
    starts = {k: tr(v) for k, v in (t.get('starts') or {}).items()}
    chutes = {k: (tr(v[0]), tr(v[1])) for k, v in (t.get('chutes') or {}).items()}
    allp = R + [q for c in chutes.values() for q in c]
    xs, ys = [p[0] for p in allp], [p[1] for p in allp]
    sc = min((W - 2 * PAD) / ((max(xs) - min(xs)) or 1), (H - 2 * PAD) / ((max(ys) - min(ys)) or 1))
    ox = (W - (max(xs) - min(xs)) * sc) / 2
    oy = (H - (max(ys) - min(ys)) * sc) / 2
    P = lambda p: (ox + (p[0] - min(xs)) * sc, oy + (max(ys) - p[1]) * sc)
    ring = [P(p) for p in R]
    d = 'M' + 'L'.join(f'{x:.1f} {y:.1f}' for x, y in ring) + 'Z'
    cx0 = sum(p[0] for p in ring) / len(ring)
    cy0 = sum(p[1] for p in ring) / len(ring)
    band = max(7.0, 20 * sc)
    out = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" font-family="system-ui,sans-serif">',
           f'<path d="{d}" fill="#e8f1e4" stroke="none"/>',
           f'<path d="{d}" fill="none" stroke="#d9d4c7" stroke-width="{band:.1f}" stroke-linejoin="round"/>',
           f'<path d="{d}" fill="none" stroke="#7b8794" stroke-width="1.1" stroke-linejoin="round"/>']
    for k, (p0, p1) in chutes.items():
        x0, y0 = P(p0)
        x1, y1 = P(p1)
        hit = race_dist is not None and str(race_dist) == k
        out.append(f'<line x1="{x0:.1f}" y1="{y0:.1f}" x2="{x1:.1f}" y2="{y1:.1f}" stroke="{"#111" if hit else "#b4ad9a"}" stroke-width="{band * 0.55:.1f}" stroke-linecap="butt"/>')
    def label(k, x, y, hit, anchor_pt):
        dx, dy = x - cx0, y - cy0
        m = math.hypot(dx, dy) or 1
        lx, ly = x + dx / m * 15, y + dy / m * 15
        fill = '#111' if hit else '#4b5563'
        wgt = 700 if hit else 500
        out.append(f'<circle cx="{x:.1f}" cy="{y:.1f}" r="{3.6 if hit else 2.6}" fill="{"#dc2626" if hit else "#374151"}" stroke="#fff" stroke-width="1"/>')
        out.append(f'<text x="{lx:.1f}" y="{ly + 3:.1f}" font-size="{10.5 if hit else 9.5}" font-weight="{wgt}" fill="{fill}" text-anchor="middle">{k}m</text>')
    for k, p in starts.items():
        x, y = P(p)
        label(k, x, y, race_dist is not None and str(race_dist) == k, p)
    for k, (p0, p1) in chutes.items():
        x, y = P(p1)
        label(k, x, y, race_dist is not None and str(race_dist) == k, p1)
    if fin:
        x, y = P(fin)
        out.append(f'<rect x="{x - 1.6:.1f}" y="{y - band / 2 - 2:.1f}" width="3.2" height="{band + 4:.1f}" fill="#111"/>')
        out.append(f'<text x="{x:.1f}" y="{y + band / 2 + 12:.1f}" font-size="9" font-weight="700" fill="#dc2626" text-anchor="middle">Finish</text>')
    out.append(f'<text x="{W / 2}" y="{H - 6}" font-size="9" fill="#6b7280" text-anchor="middle">{t["name"]}, circuit {t["perim"]} m</text>')
    out.append('</svg>')
    return ''.join(out)


if __name__ == '__main__':
    d = json.load(open('track_outlines.json'))['tracks']
    od = sys.argv[1]
    os.makedirs(od, exist_ok=True)
    for s in sys.argv[2].split(','):
        rd = int(sys.argv[3]) if len(sys.argv) > 3 else None
        open(os.path.join(od, s.replace(' ', '') + '.svg'), 'w').write(render(d[s], rd))
