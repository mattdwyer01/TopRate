"""Geocode our track names with Nominatim (19 Oct 2026) so OSM outlines can be matched by location instead of by name (OSM names the course differently, e.g. Sunshine
Coast = Corbould Park, or leaves the running track unnamed). Cached in data/track_outlines/geocode.json, one request per second as the usage policy asks.
usage: PYTHONPATH=. python research/track_outline_geocode.py"""
import glob
import json
import os
import re
import time
import urllib.parse
import urllib.request

import pandas as pd

OUT = os.path.join('data', 'track_outlines', 'geocode.json')
SUFFIX = re.compile(r'\b(synthetic|inner|heath|parks?|scarpside|lakeside|hillside|fibre sand|gh|kensington)\b', re.I)


ALIAS = {'Sunshine Coast': 'Corbould Park', 'Townsville': 'Cluden Park', 'Toowoomba': 'Clifford Park', 'Rockhampton': 'Callaghan Park', 'Hobart': 'Elwick Park Glenorchy',
         'Launceston': 'Mowbray Racecourse', 'Wagga': 'Murrumbidgee Turf Club Wagga Wagga', 'Canberra': 'Thoroughbred Park Canberra', 'Rosehill': 'Rosehill Gardens',
         'Eagle Farm': 'Eagle Farm Race Course', 'Mackay': 'Ooralea Mackay Turf Club', 'Cairns': 'Cannon Park Cairns', 'Moonee Valley': 'Moonee Valley Racing Club Moonee Ponds',
         'Echuca': 'Echuca Racing Club', 'Murray Bridge': 'Murray Bridge Racecourse', 'Albury': 'Albury Racecourse Albury Racing Club', 'Newcastle': 'Broadmeadow Racecourse',
         'Warwick Farm': 'Warwick Farm Racecourse', 'Sandown': 'Sandown Racecourse Springvale', 'Pioneer Park': 'Pioneer Park Racecourse', 'Taree': 'Taree Racecourse',
         'Muswellbrook': 'Muswellbrook Race Club', 'Mt Gambier': 'Mount Gambier Racecourse', 'Geraldton': 'Geraldton Racecourse', 'Kalgoorlie': 'Kalgoorlie Racecourse',
         'Northam': 'Northam Racecourse', 'Pinjarra': 'Pinjarra Racecourse', 'Ballarat': 'Ballarat Turf Club Dowling Forest', 'Seymour': 'Seymour Racecourse', 'Sale': 'Sale Racecourse Victoria',
         'Kilmore': 'Kilmore Racecourse', 'Beaudesert': 'Beaudesert Racecourse', 'Dalby': 'Dalby Racecourse', 'Swan Hill': 'Swan Hill Racecourse', 'Moruya': 'Moruya Racecourse',
         'Albany': 'Albany Racecourse Western Australia', 'Balaklava': 'Balaklava Racecourse', 'Beaumont': 'Beaumont Racecourse', 'Lark Hill': 'Lark Hill Racecourse'}


def base(t):
    b = SUFFIX.sub('', t.replace('-', ' ')).strip()
    return re.sub(r'\s+', ' ', b)


def q(name):
    url = 'https://nominatim.openstreetmap.org/search?' + urllib.parse.urlencode({'q': (ALIAS[name] if name in ALIAS else f'{name} racecourse'), 'format': 'json', 'countrycodes': 'au', 'limit': 3})
    req = urllib.request.Request(url, headers={'User-Agent': 'TopRateResearch/1.0 (personal horse racing analytics)'})
    with urllib.request.urlopen(req, timeout=30) as r:
        return json.load(r)


def main():
    runs = pd.concat([pd.read_csv(f, usecols=['track']) for f in sorted(glob.glob('race_results_20*.csv.gz'))[-3:]]).track.value_counts()
    cache = json.load(open(OUT)) if os.path.exists(OUT) else {}
    wanted = {base(t) for t in runs.index if runs[t] >= 100}
    for k in ALIAS:
        cache.pop(k, None)           # re-query aliased names
    todo = sorted((wanted | set(ALIAS)) - set(cache))
    print(len(todo), 'to geocode', flush=True)
    for i, b in enumerate(todo):
        try:
            res = q(b)
            cache[b] = [{'lat': float(r['lat']), 'lon': float(r['lon']), 'name': r.get('display_name', '')[:80], 'type': r.get('type')} for r in res]
        except Exception as e:  # noqa: BLE001
            print(b, 'failed', e, flush=True)
            continue
        time.sleep(1.1)
        if i % 25 == 0:
            json.dump(cache, open(OUT, 'w'))
            print(i, flush=True)
    json.dump(cache, open(OUT, 'w'), indent=0)
    print('done', len(cache), flush=True)


if __name__ == '__main__':
    main()
