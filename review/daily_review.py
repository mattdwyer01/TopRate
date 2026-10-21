"""Combined post-race review for one racing day (Oct 2026). Read-only, changes no model. Run it 3 days after the meeting, when TopRate's ratings are Final.
Per meeting: how the Proj read it (actual rating at the weight carried from TopRate's race pages against the Proj logged before the race), whether leaders or
closers did better (position at 800m), whether the draw mattered, the winners the Proj had down the order, the biggest misses with the run comment, data checks.
GPS meetings (VIC/SA/QLD) get the GPS section after it (ground lost, running line, pace against the usual).
Needs data/tr_results/<date>.json.gz (workflow tr_results_fetch.yml). Run: python review/daily_review.py 2026-10-17 [--out DIR]"""
import argparse, gzip, json, os, sys
import numpy as np
import pandas as pd

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, 'review'))
import gps_review  # noqa: E402


def load(date):
    p = os.path.join(ROOT, 'data', 'tr_results', date + '.json.gz')
    if not os.path.exists(p):
        return None
    rows = []
    for rid, r in json.load(gzip.open(p, 'rt'))['races'].items():
        for x in r['runners']:
            rows.append(dict(race_id=int(rid), venue=r['venue'], race=r['race'], going=r.get('going'), status=r.get('wprStatus'), run_id=x.get('runId'), horse=x.get('horse'),
                             atw=x.get('atw'), p800=x.get('position800m'), fin=x.get('positionFinish'), barrier=x.get('barrier'), price=x.get('priceStarting'),
                             comment=x.get('commentsVideo', '')))
    T = pd.DataFrame(rows)
    L = pd.read_csv(os.path.join(ROOT, 'wpr_projection_log.csv.gz'))
    L = L[L.date == date].sort_values('made').drop_duplicates('run_id', keep='last')[['run_id', 'proj', 'nruns']]
    x = T.merge(L, on='run_id', how='left')
    x['n'] = x.groupby('race_id').run_id.transform('count')
    x['sf'] = x.p800 / x.n
    x['bf'] = x.barrier / x.n
    x['miss'] = x.atw - x.proj
    return x


def spear(a, b):
    ok = a.notna() & b.notna()
    if ok.sum() < 5 or a[ok].nunique() < 2 or b[ok].nunique() < 2:
        return np.nan
    return float(a[ok].rank().corr(b[ok].rank()))


def z(s):
    s = s.dropna()
    return float(s.mean() / (s.std() / np.sqrt(len(s)))) if len(s) > 2 and s.std() > 0 else np.nan


def meeting_text(venue, v, sd):
    L = []
    races = list(v.groupby('race'))
    fin = pd.DataFrame([dict(race=k, lead=spear(g.sf, g.fin), draw=spear(g.bf, g.fin), corr=spear(g.proj, -g.atw) * -1 if g.proj.notna().sum() > 4 else np.nan) for k, g in races])
    status = v.status.mode().iloc[0] if v.status.notna().any() else '?'
    m = v.miss.dropna()
    L.append(f'## {venue}: {len(races)} races, {len(v)} runners, ratings {status}, going {v.going.iloc[0]}')
    if len(m) > 10:
        L.append(f'Proj read: mean miss {m.mean():+.1f} rating points ({m.mean() / (sd / np.sqrt(len(m))):+.1f} se, + = ran better than Proj); Proj order tracked the actual ratings r={fin["corr"].mean():.2f}.')
    pos = (f'Leaders vs closers: correlation of position at 800m with finishing order {fin.lead.mean():+.2f} (z {z(fin.lead):+.1f}; + = those up near the lead finished better). '
           if fin.lead.notna().sum() >= 2 else 'Leaders vs closers: no running positions for this meeting. ')
    drw = f'Draw: {fin.draw.mean():+.2f} (z {z(fin.draw):+.1f}; + = wider barriers finished worse).' if fin.draw.notna().sum() >= 2 else 'Draw: not enough races.'
    L.append(pos + drw)
    winners = v[v.fin == 1]
    sur = []
    for _, w in winners.iterrows():
        g = v[v.race == w.race]
        rk = (g.proj > w.proj).sum() + 1 if pd.notna(w.proj) else None
        if rk is None or rk >= 6:
            sur.append(f"R{int(w.race)} {w.horse} (${w.price}, " + (f"Proj rank {rk}" if rk else 'no Proj') + ')')
    L.append('Winners the Proj had well down the order: ' + ('; '.join(sur) if sur else 'none') + '.')
    fell = v[v.fin.isna() & v.atw.notna()]
    if len(fell): L.append('Did not finish or refused (left out of the misses below): ' + ', '.join(f'R{int(q.race)} {q.horse}' for q in fell.itertuples()) + '.')
    ran = v[v.fin.notna()]
    big = ran.reindex(ran.miss.abs().sort_values(ascending=False).index).head(3)
    for q in big.itertuples():
        if pd.notna(q.miss):
            L.append(f"  R{int(q.race)} {q.horse}: rated {q.miss:+.1f} vs Proj, finished {int(q.fin) if pd.notna(q.fin) else '?'} at ${q.price}. {str(q.comment)[:140]}")
    chk = []
    unrated = v.groupby('race').proj.apply(lambda s: s.isna().sum())
    if (unrated > 1).any(): chk.append('races with 2+ unrated runners: ' + ', '.join(f'R{int(k)}' for k in unrated[unrated > 1].index))
    if v.going.isna().all() or str(v.going.iloc[0]) == 'nan': chk.append('going missing')
    if (v.status != 'Final').any(): chk.append('ratings not all Final yet, rerun later')
    if chk: L.append('Checks: ' + '; '.join(chk) + '.')
    L.append('')
    return L


def meeting_stats(venue, v):
    """Numbers behind one meeting's text, for the weekly and monthly roll-ups (review/rollup.py): sums so days can be pooled exactly."""
    races = list(v.groupby('race'))
    lead = [spear(g.sf, g.fin) for _, g in races]
    draw = [spear(g.bf, g.fin) for _, g in races]
    m = v[v.status == 'Final'].miss.dropna()      # the miss is only read on Final ratings (Preliminary ones run about a point low and move)
    winners = v[v.fin == 1]
    down = 0
    for _, w in winners.iterrows():
        g = v[v.race == w.race]
        if pd.notna(w.proj) and (g.proj > w.proj).sum() + 1 >= 6:
            down += 1
    clean = lambda a: [round(x, 3) for x in a if pd.notna(x)]
    return dict(venue=venue, races=len(races), runners=int(len(v)), final=bool((v.status == 'Final').mean() >= 0.9), going=None if str(v.going.iloc[0]) == 'nan' else str(v.going.iloc[0]),
                n=int(len(m)), miss_sum=round(float(m.sum()), 2), miss_ss=round(float((m ** 2).sum()), 2), lead=clean(lead), draw=clean(draw),
                winners=int(len(winners)), winners_down=int(down))


def band_stats(done):
    """Miss by Proj band and by number of earlier runs (pooled by the roll-up)."""
    out = {}
    for name, key, cuts in (('proj', done.proj, [0, 60, 70, 80, 90, 200]), ('nruns', done.nruns, [-1, 2, 5, 9, 999])):
        b = pd.cut(key, cuts)
        out[name] = {str(k): dict(n=int(len(g)), sum=round(float(g.miss.sum()), 2), ss=round(float((g.miss ** 2).sum()), 2)) for k, g in done.groupby(b, observed=True)}
    return out


def day_stats(date):
    x = load(date)
    if x is None:
        return None
    done = x[x.atw.notna() & x.proj.notna() & x.fin.notna() & (x.status == 'Final')]
    return dict(date=date, races=int(x.race_id.nunique()), runners=int(len(x)), final=bool((x.status == 'Final').mean() >= 0.9), n=int(len(done)), miss_sum=round(float(done.miss.sum()), 2),
                miss_ss=round(float((done.miss ** 2).sum()), 2), bands=band_stats(done), meetings=[meeting_stats(v_, g) for v_, g in x.groupby('venue')])


def report(date):
    x = load(date)
    if x is None:
        return f'# Daily review {date}\n\nNo TopRate post-race data for this date yet (run tr_results_fetch.yml first).\n'
    done = x[x.atw.notna() & x.proj.notna()]
    sd = float(done.miss.std()) if len(done) > 30 else 9.0
    L = [f'# Daily review {date}', f'{x.race_id.nunique()} races, {len(x)} runners; Proj miss across the day {done.miss.mean():+.1f} (sd {sd:.1f}); ratings {x.status.value_counts().to_dict()}.', '']
    for venue, v in x.groupby('venue'):
        L += meeting_text(venue, v, sd)
    L += ['# GPS (VIC, SA and QLD meetings)', '', gps_review.text(date, gps_review.load(date)).split('\n', 2)[2], '']
    return '\n'.join(L)


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('date'); ap.add_argument('--out')
    a = ap.parse_args()
    t = report(a.date)
    if a.out:
        os.makedirs(a.out, exist_ok=True); open(os.path.join(a.out, a.date + '.md'), 'w').write(t)
        st = day_stats(a.date)
        if st:
            json.dump(st, open(os.path.join(a.out, a.date + '.json'), 'w'), separators=(',', ':'))
    print(t)
