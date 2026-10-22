"""Live meeting lean from racing.com GPS (VIC and SA), Oct 2026. A READING AID: it changes no rating. For each of today's VIC/SA meetings it reads every race that has
run and has GPS (about 10 to 25 minutes after the jump, see CLAUDE.md), and stores per race the rank correlation of where each horse sat after the first 400m with its
finishing order (lead: + = horses near the lead finished better), of its average distance off the rail with the finishing order (fence: + = horses nearer the fence finished
better) and of its barrier with the finishing order (draw: + = wide barriers finished worse). The dashboard (BiasNote's sibling MeetingLeanNote) averages the races so far and says so
once there are 3+ races and the lean clears a bar. Output meeting_lean.json: {date: {venue: {race_no: {lead, fence, draw, n, t}}}}, keyed by the runners.csv venue name.
Needs the racing-model checkout (--rm) and RACINGCOM_API_KEY / RACINGCOM_CAL_API_KEY. Usage: python meeting_lean.py --rm ../rm [--date 2026-10-23] [--out meeting_lean.json]"""
import argparse, json, os, re, sys
from datetime import datetime, timedelta, timezone

import numpy as np
import pandas as pd

OUT = 'meeting_lean.json'
KEEP_DAYS = 3
DONE = ('final', 'paying', 'closed', 'resulted', 'protest', 'provisional')


def spear(a, b):
    d = pd.DataFrame({'a': a, 'b': b}).dropna()
    if len(d) < 5 or d.a.nunique() < 2 or d.b.nunique() < 2:
        return None
    v = d.a.rank().corr(d.b.rank())
    return None if pd.isna(v) else round(float(v), 3)


def race_lean(runs, secs, dist):
    """runs, secs: DataFrames as racingcom_sectionals.parse_race returns them for one race. dist: race distance in metres."""
    if runs.empty:
        return None
    r = runs.copy()
    n = len(r)
    r['finish'] = pd.to_numeric(r.finish, errors='coerce')
    r = r[(r.finish >= 1) & (r.finish <= n)]      # a placeholder finish (2147483647) is not a placing
    if len(r) < 5:
        return None
    early = None
    if not secs.empty and dist:
        s = secs[secs.from_m >= dist - 400].sort_values('from_m', ascending=False)   # sections run from the finish backwards, the last row is the 400m mark
        early = s.groupby('tab_no').pos.last()
    r['early'] = pd.to_numeric(r.tab_no.map(early), errors='coerce') if early is not None else np.nan
    r['rail'] = pd.to_numeric(r.rail_avg_m, errors='coerce')
    r['barrier'] = pd.to_numeric(r.barrier, errors='coerce')
    return dict(lead=spear(r.early, r.finish), fence=spear(r.rail, r.finish), draw=spear(r.barrier, r.finish), n=int(n))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--rm', required=True)
    ap.add_argument('--date')
    ap.add_argument('--out', default=OUT)
    a = ap.parse_args()
    sys.path.insert(0, a.rm)
    from ingest import racingcom_sectionals as rc
    now = datetime.now(timezone.utc)
    date = a.date or (now + timedelta(hours=10)).strftime('%Y-%m-%d')     # Melbourne date (a fixed +10 is close enough for the daytime window this runs in)
    store = json.load(open(a.out)) if os.path.exists(a.out) else {}
    store = {d: v for d, v in store.items() if d >= (datetime.strptime(date, '%Y-%m-%d') - timedelta(days=KEEP_DAYS)).strftime('%Y-%m-%d')}
    R = pd.read_csv('runners.csv', usecols=['date', 'venue', 'state'], low_memory=False)
    venues = sorted(R[(R.date == date) & R.state.isin(['VIC', 'SA'])].venue.dropna().unique())
    if not venues:
        print('no VIC/SA meeting on', date); json.dump(store, open(a.out, 'w'), separators=(',', ':')); return
    cal = rc.Client(delay=0.3, endpoint='https://graphql.api.racing.com/', key_var='RACINGCOM_CAL_API_KEY')
    form = rc.Client(delay=0.3)
    idx = rc.CalendarIndex(cal, ['VIC', 'SA'])
    day = store.setdefault(date, {})
    new = 0
    for v in venues:
        code = idx.lookup(date, [v])
        if not code:
            print('no racing.com meeting for', v); continue
        have = day.setdefault(v, {})
        try:
            races = ((form.q(rc.RACES_FOR_MEET % code).get('data') or {}).get('racesForMeet')) or []
        except Exception as e:
            print(v, 'meet query failed', e); continue
        for r in races:
            n = r.get('raceNumber')
            if n is None or r.get('isTrial') or r.get('isJumpOut') or str(n) in have:
                continue
            if not (str(r.get('raceStatus')).lower() in DONE or r.get('hasSectionals')):
                continue
            try:
                obj = form.q(rc.RACE_FORM % (code, n))
                runs, secs = rc.parse_race(obj, code, int(n), dict(r, venue=v))
            except Exception as e:
                print(v, n, 'form failed', e); continue
            runs, secs = pd.DataFrame(runs), pd.DataFrame(secs)
            if runs.empty or secs.empty:      # GPS not posted yet: try again next pass
                continue
            dist = pd.to_numeric(re.sub(r'\D', '', str(r.get('distance') or '')) or None, errors='coerce')
            L = race_lean(runs, secs, None if pd.isna(dist) else float(dist))
            if L is None:
                continue
            L['t'] = now.strftime('%Y-%m-%dT%H:%MZ')
            have[str(n)] = L; new += 1
            print(v, 'R%s' % n, L)
    json.dump(store, open(a.out, 'w'), separators=(',', ':'))
    print('new races', new)


if __name__ == '__main__':
    main()
