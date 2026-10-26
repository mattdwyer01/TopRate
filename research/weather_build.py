"""Daily weather by racecourse (Open-Meteo archive, free, no key): rain that day and the 3 days before, max wind and its direction, max temperature.  Resumable.
Venues come from the results files (sponsor words stripped); coordinates from Open-Meteo geocoding restricted to Australia (Hong Kong and others skipped).
  python research/weather_build.py"""
import json, os, re, time, urllib.parse, urllib.request
import pandas as pd
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, 'data', 'weather'); os.makedirs(OUT, exist_ok=True)
SPONSOR = re.compile(r'\b(sportsbet|bet365|ladbrokes|tab|picklebet|aquis|neds|pointsbet|bluebet|unibet|bet|park|racecourse|synthetic|poly|track|royal)\b')
def vkey(x): return re.sub(r'[^a-z ]', '', SPONSOR.sub('', str(x).lower())).strip()
def get(url):
    for k in range(3):
        try:
            with urllib.request.urlopen(url, timeout=30) as r: return json.load(r)
        except Exception as e:
            time.sleep(2 + 3 * k)
    return None
if __name__ == '__main__':
    v = pd.concat([pd.read_csv(os.path.join(ROOT, f'race_results_{y}.csv.gz'), usecols=['venue'], low_memory=False) for y in range(2019, 2027)])
    v['vk'] = v.venue.map(vkey)
    v = v[v.vk.str.len() > 2]
    tops = v.groupby('vk').agg(n=('venue', 'size'), name=('venue', lambda s: s.value_counts().index[0])).reset_index()
    tops = tops[tops.n >= 300]
    gp = os.path.join(OUT, 'venue_geo.json'); geo = json.load(open(gp)) if os.path.exists(gp) else {}
    for r in tops.itertuples():
        if r.vk in geo: continue
        q = urllib.parse.urlencode({'name': r.vk, 'count': 10, 'language': 'en', 'countryCode': 'AU'})
        d = get('https://geocoding-api.open-meteo.com/v1/search?' + q)
        res = [x for x in (d or {}).get('results', []) if x.get('country_code') == 'AU']
        if res:
            pick = res[0]
            geo[r.vk] = dict(lat=pick['latitude'], lon=pick['longitude'], tz=pick.get('timezone', 'Australia/Sydney'), found=pick['name'], admin=pick.get('admin1'), n=int(r.n))
        else:
            geo[r.vk] = None
        json.dump(geo, open(gp, 'w'))
    print(len([k for k, x in geo.items() if x]), 'venues geocoded of', len(geo))
    for k, x in geo.items():
        fp = os.path.join(OUT, f'daily_{k.replace(" ", "_")}.parquet')
        if not x or os.path.exists(fp): continue
        q = urllib.parse.urlencode({'latitude': x['lat'], 'longitude': x['lon'], 'start_date': '2018-12-25', 'end_date': '2026-10-25', 'timezone': x['tz'],
                                    'daily': 'precipitation_sum,wind_speed_10m_max,wind_gusts_10m_max,wind_direction_10m_dominant,temperature_2m_max'})
        d = get('https://archive-api.open-meteo.com/v1/archive?' + q)
        if not d or 'daily' not in d: print('fail', k); continue
        df = pd.DataFrame(d['daily']); df['vk'] = k
        df.to_parquet(fp)
        time.sleep(1.2)
    print('done')
