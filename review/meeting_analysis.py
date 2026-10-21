"""Meeting review v2 (Oct 2026): did the projection read each meeting correctly, judged on what the runners actually rated?
Actual = runners.csv wpr_actual (own-chain rating, filled the next day). It is on a different scale from Proj, so everything is WITHIN RACE: demean both, fit one
pooled slope b (actual on Proj) over the baseline window, and read each runner's residual e = actual - b x Proj. A meeting is then judged by groups of runners
(barrier thirds, suitability adjustment, weight term, price move) against the baseline noise, never by a handful of races alone. Descriptive: changes no model.
Run: python review/meeting_analysis.py 2026-10-17 [--window 40]"""
import argparse, os
import numpy as np
import pandas as pd

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def frame(d0, d1):
    L = pd.read_csv(os.path.join(ROOT, 'wpr_projection_log.csv.gz'))
    L = L[L.date.between(d0, d1) & (L.src != 'backfill')].sort_values('made').drop_duplicates('run_id', keep='last')
    R = pd.read_csv(os.path.join(ROOT, 'runners.csv'), low_memory=False,
                    usecols=lambda c: c in ('run_id', 'horse', 'venue', 'state', 'race', 'distance', 'going', 'barrier', 'tab_number', 'scratched', 'wpr_actual', 'finish_position',
                                            'won', 'margin_finish', 'starting_price_sp', 'fixed_win_price', 'open_price', 'weight_carried', 'jockey', 'comments_video'))
    x = L.merge(R, on='run_id', how='inner')
    x = x[(x.scratched.fillna(0) != 1) & x.wpr_actual.notna() & x.proj.notna()].copy()
    x['rk'] = x.venue + '|' + x.date + '|' + x.race.astype(str)
    g = x.groupby('rk')
    x['n'] = g.run_id.transform('count')
    x = x[x.n >= 5].copy()
    x['pd'] = x.proj - x.groupby('rk').proj.transform('mean')
    x['ad'] = x.wpr_actual - x.groupby('rk').wpr_actual.transform('mean')
    x['bf'] = x.barrier / x.n
    x['mv'] = np.log(x.starting_price_sp.where(x.starting_price_sp > 1) / x.open_price.where(x.open_price > 1).fillna(x.fixed_win_price))
    return x


def residuals(x, base):
    b = float((base.pd * base.ad).sum() / (base.pd ** 2).sum())
    x = x.copy(); x['b'] = b
    x['e'] = x.ad - b * x.pd
    return x, b


def groups(x):
    return {
        'inside barriers (1st third)': x.bf <= 1 / 3,
        'middle barriers': (x.bf > 1 / 3) & (x.bf <= 2 / 3),
        'outside barriers (last third)': x.bf > 2 / 3,
        'Proj top 3 in race': x.groupby('rk').proj.rank(ascending=False) <= 3,
        'Proj bottom third': x.groupby('rk').proj.rank(pct=True) <= 1 / 3,
        'suitability adj +0.5 or better': x.adj >= 0.5,
        'suitability adj -0.5 or worse': x.adj <= -0.5,
        'carrying 2+ kg more than field': x.weight_carried - x.groupby('rk').weight_carried.transform('mean') >= 2,
        'shortened 15%+ (market support)': x.mv <= -0.15,
        'drifted 15%+': x.mv >= 0.15,
    }


def analyse(date, window=40):
    d0 = (pd.Timestamp(date) - pd.Timedelta(days=window)).strftime('%Y-%m-%d')
    all_ = frame(d0, date)
    base = all_[all_.date < date]
    all_, b = residuals(all_, base)
    sd = float(all_[all_.date < date].e.std())
    out = {'date': date, 'slope': b, 'sd': sd, 'meetings': []}
    day = all_[all_.date == date]
    gb = {k: m for k, m in groups(base).items()}
    base_means = {k: float(base.assign(e=all_.loc[base.index, 'e']).loc[m, 'e'].mean()) for k, m in gb.items()}
    for venue, v in day.groupby('venue'):
        races = v.rk.nunique()
        if len(v) < 40: continue
        corr = float(np.corrcoef(v.pd, v.ad)[0, 1])
        bc = base.groupby('rk').apply(lambda g: np.corrcoef(g.pd, g.ad)[0, 1] if len(g) > 4 else np.nan).dropna()
        mt = dict(venue=venue, races=int(races), runners=int(len(v)), going=v.going.iloc[0], state=v.state.iloc[0], corr=corr, base_corr=float(bc.mean()), flags=[])
        for k, m in groups(v).items():
            e = v.e[m]
            if len(e) < 8: continue
            mean_rel = float(e.mean() - base_means[k]); se = sd / np.sqrt(len(e))
            mt['flags'].append(dict(group=k, n=int(len(e)), mean=float(e.mean()), rel=mean_rel, z=mean_rel / se))
        v = v.assign(z=v.e / sd)
        big = v.reindex(v.e.abs().sort_values(ascending=False).index).head(5)
        mt['misses'] = [dict(race=int(r.race), horse=r.horse, tab=r.tab_number, proj=float(r.pd), actual=float(r.ad / b if b else r.ad), e=float(r.e), z=float(r.z),
                             barrier=int(r.barrier), n=int(r.n), price=float(r.starting_price_sp) if pd.notna(r.starting_price_sp) else None,
                             finish=int(r.finish_position) if pd.notna(r.finish_position) else None) for r in big.itertuples()]
        out['meetings'].append(mt)
    return out


def text(o):
    L = [f"# Meeting review {o['date']}", f"Within-race fit: actual ~ {o['slope']:.2f} x Proj, miss sd {o['sd']:.1f} (baseline window).", '']
    for m in o['meetings']:
        L.append(f"## {m['venue']} ({m['state']}) {m['going']}: {m['races']} races, {m['runners']} runners; Proj tracked the field order r={m['corr']:.2f} (usual {m['base_corr']:.2f})")
        sig = [f for f in m['flags'] if abs(f['z']) >= 2]
        L.append('Unusual: ' + ('; '.join(f"{f['group']}: {f['rel']:+.1f} pts vs usual (n={f['n']}, z {f['z']:+.1f})" for f in sig) if sig else 'nothing beyond chance.'))
        for q in m['misses'][:3]:
            L.append(f"  R{q['race']} {q['horse']} (barrier {q['barrier']}/{q['n']}, ${q['price']}, finished {q['finish']}): rated {q['e']:+.1f} vs Proj-implied (z {q['z']:+.1f})")
        L.append('')
    return '\n'.join(L)


def pooled(d0, d1):
    """The version that can teach us something: the same groups pooled over every meeting in the window, with z against chance and both halves."""
    x = frame(d0, d1)
    x, b = residuals(x, x)
    sd = float(x.e.std())
    ds = sorted(x.date.unique()); mid = ds[len(ds) // 2]
    L = [f'# Pooled review {d0} to {d1}: {len(x)} runners, {x.rk.nunique()} races, {len(ds)} days. actual ~ {b:.2f} x Proj within race, miss sd {sd:.1f}.',
         'Mean miss (actual minus Proj-implied, rating points, + = ran better than Proj), z against chance, first half / second half:']
    for k, m in groups(x).items():
        e = x.e[m]
        if len(e) < 30: continue
        h1, h2 = x.e[m & (x.date < mid)], x.e[m & (x.date >= mid)]
        L.append(f'  {k:34s} n={len(e):6d} mean {e.mean():+.2f} z {e.mean() / (sd / np.sqrt(len(e))):+.1f} | {h1.mean():+.2f} / {h2.mean():+.2f}')
    L.append('Within-race demeaning removes anything shared by a whole race (going, track speed), so meeting-level effects need the runner-page ratings (ATW) instead.')
    return '\n'.join(L)


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('date'); ap.add_argument('--window', type=int, default=40); ap.add_argument('--pooled-from')
    a = ap.parse_args()
    print(pooled(a.pooled_from, a.date) if a.pooled_from else text(analyse(a.date, a.window)))
