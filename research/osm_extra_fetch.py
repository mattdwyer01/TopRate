"""Targeted OSM fetch for tracks the sport=horse_racing query missed (19 Oct 2026). For every geocoded track with no outline yet, ask Overpass for any leisure=track /
racetrack / sport=horse_racing way or relation within 1.5 km of its geocoded point (some courses lack the sport tag), and store them in data/track_outlines/osm_extra.json
in the same element format, which track_outline_geometry.py merges in. One request per track, mail.ru mirror. usage: PYTHONPATH=. python research/osm_extra_fetch.py"""
import json
import os
import time
import urllib.parse
import urllib.request

HOST = 'https://maps.mail.ru/osm/tools/overpass/api/interpreter'
GM = os.path.join('data', 'track_outlines', 'track_geometry.json')
GC = os.path.join('data', 'track_outlines', 'geocode.json')
OUT = os.path.join('data', 'track_outlines', 'osm_extra.json')


def q(la, lo):
    data = f'[out:json][timeout:60];(way["leisure"="track"](around:1500,{la},{lo});relation["leisure"="track"](around:1500,{la},{lo});way["leisure"="racetrack"](around:1500,{la},{lo});way["sport"="horse_racing"](around:1500,{la},{lo}););out geom;'
    req = urllib.request.Request(HOST, data=urllib.parse.urlencode({'data': data}).encode(), headers={'User-Agent': 'TopRateResearch/1.0 (personal horse racing analytics)'})
    with urllib.request.urlopen(req, timeout=120) as r:
        return json.load(r).get('elements', [])


def main():
    import re
    from track_outline_geocode import base
    have = set(json.load(open(GM))) if os.path.exists(GM) else set()
    gc = json.load(open(GC))
    done = json.load(open(OUT)) if os.path.exists(OUT) else {'queried': {}, 'elements': {}}
    for name, pts in sorted(gc.items()):
        if name in have or name in done['queried'] or not pts:
            continue
        got = 0
        for p in pts[:2]:
            try:
                for e in q(p['lat'], p['lon']):
                    done['elements'][f"{e['type']}{e['id']}"] = e
                    got += 1
            except Exception as ex:  # noqa: BLE001
                print(name, 'failed', ex, flush=True)
            time.sleep(1.0)
        done['queried'][name] = got
        print(name, got, flush=True)
    json.dump(done, open(OUT, 'w'), separators=(',', ':'))
    print('done', len(done['elements']), flush=True)


if __name__ == '__main__':
    main()
