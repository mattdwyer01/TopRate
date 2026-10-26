"""How much of a run's rating miss is shared by the whole race, and can it be predicted? (26 Oct 2026)

Miss e = a run's wpr minus the mean wpr of the horse's last 3 runs (a plain stand-in for the ability estimate), raw scale, 2022 to 8 Oct 2026,
races where 8+ runners have an e. The part of e that every runner in a race shares (the race-level component) is what a better view of the
race (pace, track, the day's standard) could in principle remove; the part left after removing it is per-horse and per-run.

  1. Variance split of e: between races (shared) and within races.
  2. Carry-over: does the mean e of the EARLIER races at the same meeting (3+) predict the mean e of a later race? (a live "meeting standard")
  3. Pre-race predictability: R2 of a race's mean e on what is known before the race (venue, going, distance, class, field size, state), fitted
     before 2025 and scored on 2025 on.

  PYTHONPATH=. python research/race_level_component.py
"""
import glob
import os
import sys

import numpy as np
import pandas as pd

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..'))


def load():
    cols = ['race_id', 'horse_id', 'date', 'track', 'distance', 'going', 'wpr', 'raceNumber', 'field_size', 'race_class', 'isBarrierTrial', 'is_jumpout', 'start_time']
    fs = [f for f in sorted(glob.glob(os.path.join(ROOT, 'race_results_202[2-6].csv.gz')))]
    d = pd.concat([pd.read_csv(f, usecols=lambda c: c in set(cols), low_memory=False) for f in fs], ignore_index=True)
    d = d[(~d.isBarrierTrial.astype(bool)) & (~d.is_jumpout.fillna(False).astype(bool)) & d.wpr.notna()].drop_duplicates(['race_id', 'horse_id'])
    d['date'] = pd.to_datetime(d.date)
    return d.sort_values(['horse_id', 'date', 'race_id']).reset_index(drop=True)


def main():
    d = load()
    g = d.groupby('horse_id')
    d['p3'] = pd.concat([g.wpr.shift(k) for k in (1, 2, 3)], axis=1).mean(axis=1, skipna=False)
    d['e'] = d.wpr - d.p3
    z = d.dropna(subset=['e']).copy()
    z['n'] = z.groupby('race_id').e.transform('size')
    z = z[z.n >= 8].copy()
    print(f'runs with a miss {len(z):,} in {z.race_id.nunique():,} races; sd of e {z.e.std():.2f}')

    # 1. variance split
    rm = z.groupby('race_id').e.agg(['mean', 'size', 'var'])
    within = (rm['var'] * (rm['size'] - 1)).sum() / (rm['size'] - 1).sum()
    total = z.e.var()
    between_obs = rm['mean'].var()
    between = max(between_obs - within * (1 / rm['size']).mean(), 0.0)
    print(f'\n1. variance of e {total:.1f}: shared by the race {between:.1f} ({100 * between / total:.0f}%, sd {np.sqrt(between):.2f}); within races {within:.1f} ({100 * within / total:.0f}%, sd {np.sqrt(within):.2f})')
    print(f'   if the shared part were removed exactly, the miss would fall from {np.sqrt(total):.2f} to about {np.sqrt(total - between):.2f}')

    # 2. carry-over inside a meeting
    r = z.groupby('race_id').agg(date=('date', 'first'), track=('track', 'first'), rn=('raceNumber', 'first'), e=('e', 'mean'), n=('e', 'size')).reset_index()
    r = r.sort_values(['track', 'date', 'rn'])
    r['prev'] = r.groupby(['track', 'date']).e.transform(lambda s: s.shift(1).expanding().mean())
    r['nprev'] = r.groupby(['track', 'date']).e.transform(lambda s: s.shift(1).expanding().count())
    q = r[r.nprev >= 3].dropna(subset=['prev'])
    b = np.polyfit(q.prev, q.e, 1)
    print(f'\n2. carry-over inside a meeting: {len(q):,} races with 3+ earlier races: slope {b[0]:+.2f}, corr {q[["prev", "e"]].corr().iloc[0, 1]:+.2f}')
    obs_var = q.e.var()
    print(f'   the mean miss of a race has sd {q.e.std():.2f}; knowing the earlier races\' mean removes {100 * q[["prev", "e"]].corr().iloc[0, 1] ** 2:.1f}% of that variance')

    # 3. predictable from what is known before the race
    r['year'] = r.date.dt.year
    zz = z.groupby('race_id').agg(going=('going', 'first'), dist=('distance', 'first'), cls=('race_class', 'first'), fs=('field_size', 'first')).reset_index()
    r = r.merge(zz, on='race_id')
    r['gs'] = pd.to_numeric(r.going.astype(str).str.extract(r'(\d+)')[0], errors='coerce')
    r['band'] = pd.cut(r.dist, [0, 1150, 1450, 1850, 2300, 9999], labels=False)
    tr, te = r[r.year < 2025], r[r.year >= 2025]

    def design(df, cats):
        cols = []
        for c in cats:
            cols.append(pd.get_dummies(df[c].astype(str), prefix=c))
        return pd.concat(cols, axis=1)

    cats = ['track', 'band', 'cls']
    Xtr = design(tr, cats)
    Xte = design(te, cats).reindex(columns=Xtr.columns, fill_value=0)
    Xtr['gs'] = tr.gs.fillna(4).values
    Xte['gs'] = te.gs.fillna(4).values
    Xtr['fs'] = tr.fs.values
    Xte['fs'] = te.fs.values
    lam = 5.0
    A = Xtr.values.astype(float)
    A = np.column_stack([np.ones(len(A)), A])
    pen = lam * np.eye(A.shape[1])
    pen[0, 0] = 0
    beta = np.linalg.solve(A.T @ A + pen, A.T @ tr.e.values)
    B2 = np.column_stack([np.ones(len(Xte)), Xte.values.astype(float)])
    pred = B2 @ beta
    ss = ((te.e.values - te.e.mean()) ** 2).sum()
    r2 = 1 - ((te.e.values - pred) ** 2).sum() / ss
    print(f'\n3. race mean miss from venue, distance band, class, going and field size (ridge, fit before 2025, scored 2025 on, {len(te):,} races): R2 {r2:.3f}')
    print(f'   venue only by the same method is part of that; the share of the race-level variance this covers is about {100 * max(r2, 0) * obs_var / max(between, 1e-9):.0f}%')


if __name__ == '__main__':
    sys.exit(main())
