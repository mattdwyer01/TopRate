"""Turning angle per 200m section from GPS (19 Oct 2026). Extra ground run in a section grows with width off the rail: extra = theta x width, so the within-race
slope of (real section length - nominal) on rail_m is the angle turned (radians) in that section. Needs no outline. usage: python research/gps_turning_probe.py"""
import glob
import numpy as np
import pandas as pd

fs = sorted(glob.glob('data/gps/r[cq]_gps_sections_202[3-6].parquet'))
g = pd.concat([pd.read_parquet(f) for f in fs], ignore_index=True)
g = g.sort_values(['race_code', 'tab_no', 'cum_dist_m'])
k = ['race_code', 'tab_no']
g['sec_len'] = g.groupby(k).real_dist_m.diff().fillna(g.real_dist_m)
g['sec_m'] = g.groupby(k).cum_dist_m.diff().fillna(g.cum_dist_m)
g = g[(g.sec_m == 200) & g.rail_m.notna()].copy()
g['extra'] = g.sec_len - g.sec_m
g['dist'] = g.groupby('race_code').cum_dist_m.transform('max')
g['x'] = g.rail_m - g.groupby(['race_code', 'cum_dist_m']).rail_m.transform('mean')
g['y'] = g.extra - g.groupby(['race_code', 'cum_dist_m']).extra.transform('mean')


def theta(d):
    den = (d.x ** 2).sum()
    return pd.Series({'theta': (d.x * d.y).sum() / den if den > 0 else np.nan, 'n': len(d), 'width_sd': d.x.std()})


if __name__ == '__main__':
    print(len(g), 'section rows', g.course.nunique(), 'courses')
    for c, dist in [('Flemington', 1600), ('Moonee Valley', 1200), ('Randwick', 1400), ('Caulfield', 1400), ('Sunshine Coast', 1200), ('Eagle Farm', 1400)]:
        s = g[g.course.str.contains(c) & g.dist.between(dist - 50, dist + 50)]
        if not len(s):
            print(c, dist, 'no rows')
            continue
        r = s.groupby('cum_dist_m').apply(theta, include_groups=False)
        print(f'{c} {dist}m, {s.race_code.nunique()} races: theta per 200m section (rad): ' + ' '.join(f'{int(i)}m:{v:.2f}' for i, v in r.theta.items()),
              f'| total {r.theta.sum():.2f} rad ({np.degrees(r.theta.sum()):.0f} deg)')
