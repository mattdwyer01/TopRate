"""Test the 2026 Cup groups on the 2020-25 Cups (2 Nov 2026).  Run with: PYTHONPATH=.:projection python research/cup_group_test.py

Groups (same rules as research/cup_2026_scorecard.py): flags per runner = positives (within 6 of the field's best last-3 average; peak of last 8 >= 102; last start in the top
quarter; ran within 15 days; placed 2+ times at 2400m+; weight 1kg+ above the field mean) and negatives (more than 10 behind the best last-3; peak under 102; last start in the back
half; more than 28 days since the last run; barrier in the outer third; 2+ runs at 2800m+).  Group A = positives minus negatives >= 3, B = not A and within 6.5 of the best last-3,
C = more than 6.5 behind.  Runners with fewer than 3 earlier results-file rated runs (mostly internationals) cannot be graded and are reported separately.
Part 1: in-sample (the rules were chosen after looking at these Cups).  Part 2: out of sample in the sense that matters: keep only rules whose direction holds in 2800m+ races
that are NOT Cups, score the Cups with those rules, compare the top third / middle / bottom third of each field.  Permutation test for the group A share of top-4 finishers.
Read-only.
"""
import os
import sys

import numpy as np
import pandas as pd

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, '..')
sys.path.insert(0, ROOT)
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, 'projection'))
os.environ.setdefault('PROJECTION_RATINGS', 'toprate')
import cup_profile as P  # noqa: E402
import wfa_scale  # noqa: E402

K = P.K
rng = np.random.default_rng(3)


def build():
    d = P.add_lags(P.load())
    d['off'] = [wfa_scale.atw_offset(int(a), s, dt.date().isoformat(), di, w) if pd.notna(a) and pd.notna(w) and pd.notna(di) else np.nan
                for a, s, dt, di, w in zip(d.horse_age.fillna(0), d.horse_sex, d.date, d.distance, d.weightCarried)]
    d['off'] = pd.to_numeric(d.off, errors='coerce')
    t = d[(d.distance >= 2800) & (d.field_size >= 8) & (d.date >= '2019-07-01') & d.positionFinish.notna() & d.off.notna()].copy()
    for k in range(1, K + 1):
        t[f'wpr{k}'] = t[f'wpr{k}'] + t.off
    t = P.features(t)
    t['top4'] = (t.positionFinish <= 4).astype(float)
    t['win'] = (t.positionFinish == 1).astype(float)
    t['cup'] = (t.track.astype(str).str.contains('Flemington')) & (t.distance == 3200) & (t.date.dt.month == 11) & (t.date.dt.weekday == 1) & (t.field_size >= 15) & (t.date >= '2020-01-01')
    grp = t.groupby('race_id')
    t['best3'] = grp.last3.transform('max')
    t['gap3'] = t.best3 - t.last3
    t['wt_rel'] = t.weightCarried - grp.weightCarried.transform('mean')
    t['bar_frac'] = t.barrier / t.field_size
    return t


RULES = {   # name: (sign, function)
    'within 6 of best last-3': (+1, lambda x: x.gap3 <= 6),
    'peak8 >= 102': (+1, lambda x: x.peak8 >= 102),
    'last start top quarter': (+1, lambda x: x.last_frac <= 0.25),
    'ran within 15 days': (+1, lambda x: x.days_since < 15),
    'placed 2+ at 2400m+': (+1, lambda x: x.placed24 >= 2),
    'weight 1kg+ above mean': (+1, lambda x: x.wt_rel >= 1),
    'over 10 behind best last-3': (-1, lambda x: x.gap3 > 10),
    'peak8 under 102': (-1, lambda x: x.peak8 < 102),
    'last start back half': (-1, lambda x: x.last_frac > 0.5),
    'over 28 days since run': (-1, lambda x: x.days_since > 28),
    'wide barrier': (-1, lambda x: x.bar_frac >= 0.67),
    '2+ runs at 2800m+': (-1, lambda x: x.n28 >= 2),
}


def score(x, rules):
    s = np.zeros(len(x))
    for name in rules:
        sign, f = RULES[name]
        s += sign * f(x).fillna(False).values.astype(float)
    return s


def perm_p(g, n_iter=5000):
    """P(at least this many top-4 finishers fall in group A) when labels are shuffled within each Cup (group sizes kept)."""
    obs = int(((g.grp == 'A') & (g.top4 == 1)).sum())
    cnt = 0
    for _ in range(n_iter):
        tot = 0
        for _, r in g.groupby('date'):
            lab = rng.permutation(r.grp.values)
            tot += int(((lab == 'A') & (r.top4.values == 1)).sum())
        cnt += tot >= obs
    return obs, cnt / n_iter


def main():
    t = build()
    C = t[t.cup & (t.n >= 3)].copy()
    allC = t[t.cup].copy()
    print('Cups', sorted(allC.date.dt.strftime('%Y').unique()), '| runners', len(allC), '| gradable (3+ earlier rated runs)', len(C), '| top-4 finishers gradable', int(C.top4.sum()), 'of', int(allC.top4.sum()))
    pd.set_option('display.width', 220)

    # ---- Part 1: in-sample groups
    net = score(C, list(RULES))
    C['net'] = net
    C['grp'] = np.where(C.net >= 3, 'A', np.where(C.gap3 <= 6.5, 'B', 'C'))
    base = C.top4.mean()
    print('\n=== Part 1: the 2026 grouping rules applied to each past Cup (in-sample) ===')
    r = C.groupby('grp').agg(runners=('top4', 'size'), top4=('top4', 'sum'), rate=('top4', 'mean'), winners=('win', 'sum'), mean_finish=('positionFinish', 'mean')).round(3)
    r['share_of_runners'] = (r.runners / len(C)).round(2)
    r['share_of_top4'] = (r.top4 / C.top4.sum()).round(2)
    r['lift'] = (r.rate / base).round(2)
    print(r.to_string())
    u = allC[allC.n < 3]
    print(f"  not gradable: {len(u)} runners, top-4 {int(u.top4.sum())} ({u.top4.mean() * 100:.0f}%), winners {int(u.win.sum())}")
    obs, p = perm_p(C)
    print(f'  Group A top-4 finishers: {obs} of {int(C.top4.sum())}; chance of that many or more by shuffling labels within each Cup: {p:.3f}')
    print('\nBy Cup (top-4 finishers by group, winner group; group sizes):')
    for dt, g in C.groupby('date'):
        gt = g[g.top4 == 1].sort_values('positionFinish')
        gw = g[g.win == 1]
        print(f"  {dt.date()}  sizes A/B/C {int((g.grp == 'A').sum())}/{int((g.grp == 'B').sum())}/{int((g.grp == 'C').sum())}  top-4 groups (1st..4th): "
              + ' '.join(gt.grp.tolist()) + f"   winner {'in ' + gw.grp.iloc[0] if len(gw) else 'unrated'}  | ungradable in top 4: {int(allC[(allC.date == dt) & (allC.n < 3)].top4.sum())}")

    # simple baselines inside the same Cups
    print('\nSimple comparisons in the same Cups (gradable runners):')
    for lab, m in (('within 6 of best last-3', C.gap3 <= 6), ('more than 6 behind', C.gap3 > 6), ('top-3 by last-3 in field', C.groupby('date').last3.rank(ascending=False, method='min') <= 3),
                   ('last start top quarter', C.last_frac <= 0.25), ('last start back half', C.last_frac > 0.5)):
        x = C[m]
        print(f"  {lab:28s} n={len(x):3d} top-4 {int(x.top4.sum()):2d} ({x.top4.mean() * 100:4.1f}%) winners {int(x.win.sum())}")

    # ---- Part 2: rules chosen on non-Cup staying races only
    N = t[~t.cup & (t.n >= 3)].copy()
    print('\n=== Part 2: rules kept only if they work in 2800m+ races that are not Cups, then applied to the Cups ===')
    nb = N.top4.mean()
    keep = []
    print(f'  non-Cup 2800m+ runners {len(N)}, base top-4 rate {nb * 100:.1f}%')
    for name, (sign, f) in RULES.items():
        m = f(N).fillna(False)
        if m.sum() < 100:
            continue
        lift = N[m].top4.mean() / nb
        ok = (lift > 1.0) if sign > 0 else (lift < 1.0)
        # the rule has to be clearly in the claimed direction (5%) to be kept
        ok = ok and abs(lift - 1) >= 0.05
        if ok:
            keep.append(name)
        print(f"    {'+' if sign > 0 else '-'} {name:28s} n={int(m.sum()):5d} lift {lift:4.2f}  {'KEEP' if ok else 'drop'}")
    C['net2'] = score(C, keep)
    C['third'] = C.groupby('date').net2.transform(lambda s: pd.qcut(s.rank(method='first'), 3, labels=['bottom', 'middle', 'top']).astype(str))
    r2 = C.groupby('third').agg(runners=('top4', 'size'), top4=('top4', 'sum'), rate=('top4', 'mean'), winners=('win', 'sum'), mean_finish=('positionFinish', 'mean')).round(3)
    r2['lift'] = (r2.rate / base).round(2)
    print(f'\n  Cups scored with the kept rules ({len(keep)}), each field split into thirds by score:')
    print(r2.loc[['top', 'middle', 'bottom']].to_string())
    C['third_l3'] = C.groupby('date').last3.transform(lambda s: pd.qcut(s.rank(method='first'), 3, labels=['bottom', 'middle', 'top']).astype(str))
    r3 = C.groupby('third_l3').agg(runners=('top4', 'size'), top4=('top4', 'sum'), rate=('top4', 'mean'), winners=('win', 'sum')).round(3)
    print('  For comparison, thirds by last-3 average alone:')
    print(r3.loc[['top', 'middle', 'bottom']].to_string())
    C['grp'] = C.third.map({'top': 'A', 'middle': 'A', 'bottom': 'C'})  # placeholder to reuse perm helper on the top third only
    C['grp'] = np.where(C.third == 'top', 'A', 'C')
    obs, p = perm_p(C)
    print(f'  top third by kept rules: {obs} of {int(C.top4.sum())} top-4 finishers; shuffle probability of that many or more {p:.3f}')


if __name__ == '__main__':
    main()
