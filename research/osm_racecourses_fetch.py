"""Fetch Australian racecourse track outlines from OpenStreetMap (19 Oct 2026). Run this ONCE from a machine with normal internet access (the cloud session
cannot reach OSM hosts), then commit data/track_outlines/osm_horse_racing.json. Ways tagged sport=horse_racing (the running tracks) plus the racecourse
landuse/leisure areas, with node geometry and tags. Data (c) OpenStreetMap contributors, ODbL: keep the attribution if it is ever shown on the dashboard.
usage: python research/osm_racecourses_fetch.py"""
import json
import os
import sys
import time
import urllib.parse
import urllib.request

HOSTS = ['https://maps.mail.ru/osm/tools/overpass/api/interpreter', 'https://overpass.osm.ch/api/interpreter', 'https://overpass-api.de/api/interpreter']
QUERY = """[out:json][timeout:180];
area["ISO3166-1"="AU"][admin_level=2]->.a;
(
  way["sport"="horse_racing"](area.a);
  relation["sport"="horse_racing"](area.a);
  way["leisure"="track"]["sport"~"horse"](area.a);
  way["landuse"="racetrack"](area.a);
  way["leisure"="racetrack"](area.a);
);
out tags geom;
"""
OUT = os.path.join('data', 'track_outlines', 'osm_horse_racing.json')


def fetch(host):
    req = urllib.request.Request(host, data=urllib.parse.urlencode({'data': QUERY}).encode(), headers={'User-Agent': 'TopRateResearch/1.0 (personal horse racing analytics)'})
    with urllib.request.urlopen(req, timeout=240) as r:
        return json.load(r)


def main():
    for host in HOSTS:
        try:
            d = fetch(host)
            break
        except Exception as e:  # noqa: BLE001
            print(host, 'failed:', e, file=sys.stderr)
            time.sleep(5)
    else:
        sys.exit('no Overpass host answered')
    els = d.get('elements', [])
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    json.dump({'source': 'OpenStreetMap contributors (ODbL)', 'fetched': time.strftime('%Y-%m-%d'), 'elements': els}, open(OUT, 'w'), separators=(',', ':'))
    named = sum(1 for e in els if e.get('tags', {}).get('name'))
    print(len(els), 'elements,', named, 'named ->', OUT)


if __name__ == '__main__':
    main()
