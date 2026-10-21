"""Per-meeting GPS review (Triple S: VIC/SA via racing.com, QLD via Racing Queensland; other states have none). Descriptive, changes no model.
For each meeting on the date: how the races were run (early pace against the usual for the track and distance, whether leaders or closers did better),
whether the rail line mattered, the trips (ground lost to the winner, running line) of the winners and of runners that rated well below the Proj
(rating from data/tr_results when it has landed), and the 'unlucky' runs worth a second look next start (6m+ of ground lost).
Run: python review/gps_review.py 2026-10-17"""
import argparse, glob, gzip, json, os, sys
import numpy as np
import pandas as pd

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, 'research'))
import gps_counterfactual as G  # noqa: E402


def load(date):
    g = G.gps_runs()
    g = g[g.date == pd.Timestamp(date)].copy()
    L = pd.read_csv(os.path.join(ROOT, 'wpr_projection_log.csv.gz'))
    L = L[(L.date == date) & (L.src != 'backfill')].sort_values('made').drop_duplicates('run_id', keep='last')
    R = pd.read_csv(os.path.join(ROOT, 'runners.csv'), low_memory=False, usecols=['run_id', 'horse', 'venue', 'race', 'barrier', 'starting_price_sp', 'finish_position'])
    L = L.merge(R, on='run_id', how='left')
    L['hn'] = G.norm(L.horse)
    atw = []
    p = os.path.join(ROOT, 'data', 'tr_results', date + '.json.gz')
    if os.path.exists(p):
        for rid, r in json.load(gzip.open(p, 'rt'))['races'].items():
            for x in r['runners']:
                atw.append(dict(hn=G.norm(pd.Series([x['horse']]))[0], atw=x.get('atw'), status=r.get('wprStatus')))
    A = pd.DataFrame(atw, columns=['hn', 'atw', 'status']).drop_duplicates('hn')
    x = g.merge(L[['hn', 'proj', 'venue', 'race', 'barrier', 'starting_price_sp']], on='hn', how='left').merge(A, on='hn', how='left')
    x['n_race'] = x.groupby('rk').horse.transform('count')
    return x


def race_stats(r):
    d = {}
    f = r.finish.rank(method='min')
    ok = r.ep_f.notna() & r.finish.notna()
    d['lead_corr'] = float(np.corrcoef(r.ep_f[ok], f[ok])[0, 1]) if ok.sum() >= 5 and r.ep_f[ok].std() > 0 else np.nan   # + = leaders ran on, - = closers won
    ok = r.rail_rel.notna() & r.finish.notna()
    d['rail_corr'] = float(np.corrcoef(r.rail_rel[ok], f[ok])[0, 1]) if ok.sum() >= 5 and r.rail_rel[ok].std() > 0 else np.nan  # + = those further off the rail ran worse
    d['pace'] = float(r.race_pace.iloc[0]) if r.race_pace.notna().any() else np.nan
    return d


def text(date, x):
    L = [f'# GPS review {date}', '']
    if x.empty:
        return '\n'.join(L + ['No GPS runs for this date yet (racing.com and Racing Queensland publish a few days after the race).'])
    for venue, v in x.groupby('venue_k'):
        rs = pd.DataFrame([dict(rk=k, **race_stats(r), n=len(r), win=r[r.finish == 1].iloc[0] if (r.finish == 1).any() else None) for k, r in v.groupby('rk')])
        lc, rc_ = rs.lead_corr.dropna(), rs.rail_corr.dropna()
        z = lambda s: (s.mean() / (s.std() / np.sqrt(len(s)))) if len(s) > 2 and s.std() > 0 else np.nan
        L += [f'## {venue}: {len(rs)} races with GPS ({v.src.iloc[0]})', '']
        fast = (rs.pace > 0.4).sum(); slow = (rs.pace < -0.4).sum()
        L.append(f'Pace: {fast} races fast early, {slow} slow early, {rs.pace.notna().sum() - fast - slow} normal (early speed vs the usual for the track and distance).')
        L.append(f'Leaders vs closers: mean correlation of early position with finishing order {lc.mean():+.2f} (z {z(lc):+.1f}; + = those up early finished better).' if len(lc) else 'Leaders vs closers: not enough data.')
        L.append(f'Rail line: mean correlation of running wide with finishing order {rc_.mean():+.2f} (z {z(rc_):+.1f}; + = runners further off the rail finished worse).' if len(rc_) else 'Rail line: not available for this meeting.')
        w = v[v.finish == 1]
        if len(w):
            L.append(f'Winners: mean line off the rail vs the field {w.rail_rel.mean():+.1f}m, mean position after 400m {w.ep_f.mean():.2f} of the field (0 = led).')
        # runners that rated well below Proj with a lot of ground lost: the trips that explain a miss
        v = v.assign(miss=v.atw - v.proj)
        ex = v[(v.gl >= 6) & (v.miss <= -6)].sort_values('miss')
        if len(ex):
            L += ['', 'Rated 6+ below the Proj and lost 6m+ of ground (trip may explain it):'] + [f'  {q.horse}: {q.miss:+.1f} vs Proj, lost {q.gl:.0f}m, line {q.rail_rel:+.1f}m off the field mean, finished {int(q.finish) if pd.notna(q.finish) else "?"}' for q in ex.head(5).itertuples()]
        un = v[(v.gl >= 6) & (v.finish > 1)].sort_values('gl', ascending=False)
        if len(un):
            L += ['', 'Lost 6m+ of ground (rated about 1 point better next start on average, a small effect): ' + ', '.join(f'{q.horse} ({q.gl:.0f}m)' for q in un.head(6).itertuples())]
        L.append('')
    return '\n'.join(L)


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('date'); ap.add_argument('--out')
    a = ap.parse_args()
    t = text(a.date, load(a.date))
    if a.out:
        os.makedirs(a.out, exist_ok=True); open(os.path.join(a.out, a.date + '.md'), 'w').write(t)
    print(t)
