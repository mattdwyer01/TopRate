"""Can the speed rating (EWM halflife 4 of par v2 figures) be improved? (19 Oct 2026) Extends speed_rating_variants.py with: longer memory (halflife 6/8/12), distance-matched
weights (runs at a similar distance count more), going-matched weights, both together, and a blend of the longer memory with the learned model. Same complete-case races
2025-07+ and the same scoring as speed_rating_variants.py. usage: PYTHONPATH=. python research/speed_rating_variants2.py"""
import os, sys
import numpy as np
sys.path.insert(0, os.path.dirname(__file__))
import speed_rating_variants as v

orig = v.variants


def matched(d, col, hl, dscale=None, gscale=None):
    """weighted mean of the horse's earlier figures: recency 0.5^(k/hl), times exp(-|dist gap|/dscale) and a going-gap factor"""
    out = np.full(len(d), np.nan)
    hid = d.horse_id.values
    s = d[col].values.astype(float)
    dist = d.distance.values.astype(float)
    gn = d.gnum.values.astype(float)
    bounds = np.flatnonzero(np.r_[True, hid[1:] != hid[:-1], True])
    for a, b in zip(bounds[:-1], bounds[1:]):
        for i in range(a + 2, b):
            j = np.arange(a, i)
            k = (i - 1 - j).astype(float)
            w = 0.5 ** (k / hl)
            if dscale:
                w = w * np.exp(-np.abs(dist[j] - dist[i]) / dscale)
            if gscale:
                w = w * np.exp(-np.abs(gn[j] - gn[i]) / gscale)
            ok = ~np.isnan(s[j])
            if ok.sum() >= 2 and w[ok].sum() > 0:
                out[i] = (w[ok] * s[j][ok]).sum() / w[ok].sum()
    return out


def variants2(d):
    d = orig(d)
    gg = d.groupby('horse_id', sort=False)
    for h in (6.0, 8.0, 12.0):
        d[f'V6 recency weighted, halflife {h:g} runs'] = gg['_s2'].transform(lambda s, h=h: s.ewm(halflife=h, min_periods=2).mean())
    d['_sp2'] = d['sp2']
    d['V6 hl6 + distance matched (400m)'] = matched(d, 'sp2', 6.0, dscale=400.0)
    d['V6 hl6 + distance matched (800m)'] = matched(d, 'sp2', 6.0, dscale=800.0)
    d['V6 hl6 + going matched (1.5)'] = matched(d, 'sp2', 6.0, gscale=1.5)
    d['V6 hl6 + distance 800 + going 1.5'] = matched(d, 'sp2', 6.0, dscale=800.0, gscale=1.5)
    return d


v.variants = variants2
v.main()
