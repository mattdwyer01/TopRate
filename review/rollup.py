"""Weekly and monthly roll-up of the daily reviews (Oct 2026). Read-only, changes no model.
Pools reviews/daily/<date>.json (written by review/daily_review.py, 3 days after each meeting so ratings are Final) over a window and reports what is stable enough to learn from:
the Proj's miss by meeting and overall, by Proj band and by number of earlier runs; leaders-vs-closers and draw by meeting, with how many meeting days agree in sign; winners the Proj had
well down the order. Days whose ratings were not all Final are counted but left out of the miss figures. A single meeting is noise; a venue shows up here only when its miss holds over
many runners.
Run: python review/rollup.py 2026-10-26 --days 7 --out reviews/weekly --name 2026-W44   (weekly)
     python review/rollup.py 2026-10-31 --days 30 --out reviews/monthly --name 2026-10 --monthly"""
import argparse, glob, json, os
from datetime import datetime, timedelta
import numpy as np

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MIN_VENUE_RUNNERS = 60      # a venue's miss is only called when it has this many runners in the window
T_CALL = 2.5                # and |t| at least this (many venues are tested, so 2 is too loose)
T_RACE = 3.0                # leaders / draw z for a venue over its races


def load(end, days):
    out = []
    for i in range(days):
        d = (datetime.strptime(end, '%Y-%m-%d') - timedelta(days=i)).strftime('%Y-%m-%d')
        p = os.path.join(ROOT, 'reviews', 'daily', d + '.json')
        if os.path.exists(p):
            out.append(json.load(open(p)))
    return sorted(out, key=lambda x: x['date'])


def tstat(n, s, ss):
    if n < 3:
        return np.nan, np.nan
    m = s / n
    var = max(ss / n - m * m, 1e-9)
    return m, m / np.sqrt(var / n)


def zvals(v):
    v = np.array(v, float)
    return (v.mean() / (v.std(ddof=1) / np.sqrt(len(v)))) if len(v) > 3 and v.std() > 0 else np.nan


def text(end, days, monthly=False):
    D = load(end, days)
    L = [f'# {"Monthly" if monthly else "Weekly"} review, {days} days to {end}', '']
    if not D:
        return '\n'.join(L + ['No daily reviews in this window yet.', ''])
    F = [d for d in D if d['final']]
    L.append(f'{len(D)} racing days with a review ({len(F)} with all ratings Final; the miss figures below use only those). '
             f'{sum(d["races"] for d in D)} races, {sum(d["runners"] for d in D)} runners.')
    n, s, ss = (sum(d[k] for d in F) for k in ('n', 'miss_sum', 'miss_ss'))
    m, t = tstat(n, s, ss)
    if n:
        L.append(f'Proj miss across the window: {m:+.2f} rating points on {n} runners (t {t:+.1f}; + = ran better than Proj).')
        by_day = [(d['date'], d['miss_sum'] / d['n']) for d in F if d['n'] > 200]
        if len(by_day) >= 3:
            L.append('By day: ' + ', '.join(f'{a[5:]} {b:+.1f}' for a, b in by_day) + '.')
    L.append('')
    # bands
    L.append('## Miss by Proj band and by earlier runs (where the Proj is off for a kind of runner)')
    for key, title in (('proj', 'Proj band'), ('nruns', 'Earlier runs')):
        agg = {}
        for d in F:
            for b, v in d['bands'].get(key, {}).items():
                a = agg.setdefault(b, [0, 0.0, 0.0]); a[0] += v['n']; a[1] += v['sum']; a[2] += v['ss']
        row = []
        for b, (bn, bs, bss) in agg.items():
            bm, bt = tstat(bn, bs, bss)
            row.append(f'{b}: {bm:+.2f} (n={bn}, t {bt:+.1f})')
        if row:
            L.append(f'{title}: ' + '; '.join(row) + '.')
    L.append('')
    # venues
    ven = {}
    for d in F:
        for mt in d['meetings']:
            if not mt['final']:
                continue
            a = ven.setdefault(mt['venue'], dict(n=0, s=0.0, ss=0.0, days=[], lead=[], draw=[], win=0, down=0, runners=0))
            a['n'] += mt['n']; a['s'] += mt['miss_sum']; a['ss'] += mt['miss_ss']; a['lead'] += mt['lead']; a['draw'] += mt['draw']
            a['win'] += mt['winners']; a['down'] += mt['winners_down']; a['days'].append((mt['miss_sum'] / mt['n'] if mt['n'] else np.nan, np.mean(mt['lead']) if mt['lead'] else np.nan,
                                                                                         np.mean(mt['draw']) if mt['draw'] else np.nan))
    rows = []
    for v, a in ven.items():
        vm, vt = tstat(a['n'], a['s'], a['ss'])
        rows.append((v, a['n'], vm, vt, len(a['days']), zvals(a['lead']), zvals(a['draw']), a))
    L.append('## Venues')
    called = [r for r in rows if r[1] >= MIN_VENUE_RUNNERS and abs(r[3]) >= T_CALL]
    if called:
        L.append(f'Venue effects worth a look (at least {MIN_VENUE_RUNNERS} runners and |t| of {T_CALL} or more; the as-of venue feature is parked for now, these are its candidates):')
        for v, n_, vm, vt, nd, _, _, a in sorted(called, key=lambda r: -abs(r[3])):
            sign = np.mean([np.sign(x[0]) == np.sign(vm) for x in a['days'] if pd_ok(x[0])]) if a['days'] else np.nan
            L.append(f'  {v}: {vm:+.2f} on {n_} runners over {nd} meeting day{"s" if nd != 1 else ""} (t {vt:+.1f}); {sign * 100:.0f}% of its days leaned the same way.')
    else:
        L.append(f'No venue clears the bar ({MIN_VENUE_RUNNERS}+ runners and |t| of {T_CALL}+). With this many venues a few extremes are expected by chance.')
    L.append('')
    L.append('All venues with 40+ runners (mean miss, t):')
    big = [f'{v} {vm:+.1f} ({vt:+.1f}, n={n_})' for v, n_, vm, vt, *_ in sorted(rows, key=lambda r: -r[2]) if n_ >= 40]
    L.append('  ' + ('; '.join(big) + '.' if big else 'none yet.'))
    L.append('')
    L.append('## Track shape by venue (reading aid, not a predictor: bias does not persist enough to use before a race)')
    shown = False
    for v, n_, vm, vt, nd, zl, zd, a in sorted(rows, key=lambda r: -(abs(r[5]) if not np.isnan(r[5]) else 0)):
        if (not np.isnan(zl) and abs(zl) >= T_RACE) or (not np.isnan(zd) and abs(zd) >= T_RACE):
            shown = True
            parts = []
            if not np.isnan(zl) and abs(zl) >= T_RACE:
                parts.append(f'{"leaders" if zl > 0 else "closers"} did better (z {zl:+.1f} over {len(a["lead"])} races)')
            if not np.isnan(zd) and abs(zd) >= T_RACE:
                parts.append(f'{"inside" if zd > 0 else "wide"} barriers did better (z {zd:+.1f})')
            L.append(f'  {v}: ' + '; '.join(parts) + '.')
    if not shown:
        L.append(f'  No venue has |z| of {T_RACE} or more on leaders or draw.')
    tw, td = sum(a['win'] for a in ven.values()), sum(a['down'] for a in ven.values())
    if tw:
        L += ['', f'Winners the Proj had at rank 6 or worse: {td} of {tw} ({td / tw * 100:.1f}%).']
    if monthly:
        L += ['', '## For the month: what could change a model',
              f'- Venue feature (parked): add when several venues keep clearing the bar month after month. This month {len(called)} cleared it.',
              '- Proj bands and earlier-run groups above: a band that is off by more than about 1 point with |t| above 3 for two months running is a calibration candidate (`projection/models_tr/ctx.json`, retrain with `projection/train_ctx.py`).',
              '- Retrain `projection/train_ctx.py` as the runner-page store grows, and compare held-out RMSE before shipping.',
              '- Nothing here is a reason to change a rating by hand: single meetings and single weeks are noise.']
    L.append('')
    return '\n'.join(L)


def pd_ok(x):
    return x is not None and not (isinstance(x, float) and np.isnan(x))


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('end'); ap.add_argument('--days', type=int, default=7); ap.add_argument('--out'); ap.add_argument('--name'); ap.add_argument('--monthly', action='store_true')
    a = ap.parse_args()
    t = text(a.end, a.days, a.monthly)
    if a.out:
        os.makedirs(os.path.join(ROOT, a.out), exist_ok=True); open(os.path.join(ROOT, a.out, (a.name or a.end) + '.md'), 'w').write(t)
    print(t)
