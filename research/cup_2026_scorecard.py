"""2026 Melbourne Cup field on the going-in measures of research/cup_profile.py (2 Nov 2026).  Run with: PYTHONPATH=.:projection python research/cup_2026_scorecard.py

Ratings are the runner pages' ATW figures as TopRate gives them (the same scale as the 2020-25 going-in figures, which were built from results-file ratings plus the
weight offset).  Flags use only pointers that held in the 2020-25 Cups: gap to the field's best last-3 average, peak of the last 8, last-start finish, days since the
last run, wide barrier, and (pooled 2800m+ races) carried weight and distance experience.  Read-only.
"""
import os
import sys

import numpy as np
import pandas as pd

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
sys.path.insert(0, ROOT)
sys.path.insert(0, os.path.join(ROOT, 'projection'))
os.environ.setdefault('PROJECTION_RATINGS', 'toprate')
import ctx as C  # noqa: E402

RACE = pd.Timestamp('2026-11-03')


def main():
    rp = C.page_frame()
    r = pd.read_csv(os.path.join(ROOT, 'runners.csv'), low_memory=False)
    cup = r[(r.date == '2026-11-03') & (r.venue == 'Flemington') & (r.race == 7) & (r.scratched.fillna(0) != 1) & (r.barrier > 0)].copy()
    L = pd.read_csv(os.path.join(ROOT, 'wpr_projection_log.csv.gz'), low_memory=False).drop_duplicates('run_id', keep='last')
    cup = cup.merge(L[['run_id', 'proj']], on='run_id', how='left')
    rows = []
    for _, h in cup.iterrows():
        x = rp[rp.horse_id == h.horse_id].sort_values('date').tail(8)
        W = x.wpr.values[::-1]
        D = x.distance.values[::-1]
        P = x.positionFinish.values[::-1]
        FS = x.field_size.values[::-1]
        d0 = x.date.values[::-1]
        rows.append(dict(horse=h.horse, tab=h.tab_no if 'tab_no' in cup.columns else np.nan, barrier=h.barrier, weight=h.weight_carried, age=h.get('horse_age'), sex=h.get('horse_sex'), proj=h.proj,
                         runs=len(x), last1=W[0] if len(W) else np.nan, last3=np.nanmean(W[:3]) if len(W) else np.nan, peak8=np.nanmax(W) if len(W) else np.nan,
                         last_dist=D[0] if len(D) else np.nan, n24=int((D >= 2400).sum()), n28=int((D >= 2800).sum()), placed24=int(((D >= 2400) & (P <= 3)).sum()),
                         days=(RACE - pd.Timestamp(d0[0])).days if len(d0) else np.nan, last_frac=(P[0] / FS[0]) if len(P) and FS[0] else np.nan, last_pos=P[0] if len(P) else np.nan,
                         last_field=FS[0] if len(FS) else np.nan))
    t = pd.DataFrame(rows)
    n = len(t)
    t['bar_frac'] = t.barrier / n
    best3 = t.last3.max()
    t['gap3'] = best3 - t.last3
    t['rk3'] = t.last3.rank(ascending=False, method='min')
    t['wt_rel'] = t.weight - t.weight.mean()
    pos, neg = [], []
    for _, q in t.iterrows():
        p, g = [], []
        if q.gap3 <= 6:
            p.append('within 6 of best last-3')
        if q.gap3 > 10:
            g.append('over 10 behind best last-3')
        if q.peak8 >= 102:
            p.append('peak8 102+')
        else:
            g.append('peak8 under 102')
        if pd.notna(q.last_frac):
            if q.last_frac <= 0.25:
                p.append('last start top quarter')
            elif q.last_frac > 0.5:
                g.append('last start back half')
        if q.days > 28:
            g.append(f'{int(q.days)}d since run')
        elif q.days < 15:
            p.append('ran inside 15 days')
        if q.bar_frac >= 0.67:
            g.append('wide barrier')
        if q.placed24 >= 2:
            p.append('placed 2+ at 2400m+')
        if q.n28 >= 2:
            g.append('2+ runs at 2800m+')
        if q.wt_rel >= 1:
            p.append('weight above field mean')
        pos.append('; '.join(p))
        neg.append('; '.join(g))
    t['positives'] = pos
    t['negatives'] = neg
    t['score'] = [len(a.split('; ')) if a else 0 for a in pos]
    t['neg'] = [len(a.split('; ')) if a else 0 for a in neg]
    pd.set_option('display.width', 280)
    pd.set_option('display.max_colwidth', 80)
    cols = ['horse', 'barrier', 'weight', 'age', 'proj', 'runs', 'last1', 'last3', 'peak8', 'gap3', 'rk3', 'days', 'last_pos', 'last_field', 'last_dist', 'n24', 'n28', 'placed24']
    print(f'2026 Cup field ({n} runners); best last-3 in field {best3:.1f}; field mean weight {t.weight.mean():.1f}')
    print(t.sort_values('last3', ascending=False)[cols].round(1).to_string(index=False))
    print('\nFlags (positives | negatives):')
    for _, q in t.sort_values(['score', 'neg'], ascending=[False, True]).iterrows():
        print(f"  {q.horse:20s} +{q.score} -{q.neg}  | {q.positives}  | {q.negatives}")


if __name__ == '__main__':
    main()
