"""Download Sky replay videos and runner silks for one meeting.
usage: python research/sky_replay_fetch.py YYYYMMDD CODE VENUE NRACES VID_DIR SILK_DIR
"""
import hashlib, json, os, sys, urllib.request

date, code, venue, nr, vid, silk = sys.argv[1:7]
os.makedirs(vid, exist_ok=True)
os.makedirs(silk, exist_ok=True)
lo, hi = (nr.split('-') + [nr])[:2] if '-' in nr else ('1', nr)
for n in range(int(lo), int(hi) + 1):
    f = f'{date}{code}{n:02d}'
    url = f'https://mediatabs.skyracing.com.au/Race_Replay/{date[:4]}/{date[4:6]}/{f}_V.mp4'
    try:
        urllib.request.urlretrieve(url, f'{vid}/{f}.mp4')
    except Exception as e:
        print('video fail', f, e)
iso = f'{date[:4]}-{date[4:6]}-{date[6:]}'
for r in json.load(open('toprate_history.json'))['RACES']:
    if r['venue'] == venue and r['date'] == iso:
        for x in r['runners']:
            sk = x.get('sk')
            fn = f"{silk}/{hashlib.md5(sk.encode()).hexdigest()}.png" if sk else None
            if sk and not os.path.exists(fn):
                try:
                    urllib.request.urlretrieve(sk, fn)
                except Exception as e:
                    print('silk fail', x['h'], e)
