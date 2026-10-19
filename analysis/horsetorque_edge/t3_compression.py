"""Test 3: race compression gate (Amplifier idea)."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from model import *
from rules import *

RES = os.path.join(os.path.dirname(__file__), 'results')


def compression(rt, col):
    """rt: frame with race_id and a rating column. Returns per-race gap_1_5 and within-X counts keyed by (thr)."""
    r = rt[['race_id', col]].dropna().copy()
    r['rk'] = r.groupby('race_id')[col].rank(ascending=False, method='first')
    top = r[r['rk'] == 1].set_index('race_id')[col]
    r['top'] = r['race_id'].map(top)
    r['gap'] = r['top'] - r[col]
    g = r.groupby('race_id')
    n = g.size()
    fifth = r[r['rk'] == np.minimum(5, r['race_id'].map(n))].set_index('race_id')['gap']
    res = pd.DataFrame({'gap_1_5': fifth, 'field': n})
    for thr in (3, 4, 5, 6):
        res[f'n_within_{thr}'] = r[r['gap'] <= thr].groupby('race_id').size()
    return res


def run():
    D = prep(pd.read_pickle(os.path.join(CACHE, 'features.pkl')))
    cols = BASE + CLASS_PAR
    rt = walk_forward_rating(D, cols)
    comp = compression(rt, 'rating')
    real_ids, P_ids, a, real = rule_sets(D)
    out = ['## Test 3: race compression gate\n']
    out.append('Model rating = ridge regression of the run WPR (race-relative) on the as-of features (base + class_par), walk-forward 2023-2026. '
               '`compressed(thr, N)` = at least N runners (rank 1 included) rated within `thr` points of rank 1. Gate = skip a pick when its race is compressed. '
               'The sweep is 12 thresholds, so read it against the halves columns, not the single best row.\n')
    cm = comp.describe().T[['mean', '25%', '50%', '75%']].reset_index().rename(columns={'index': 'stat'})
    out.append(md(cm, {k: '{:.2f}' for k in ['mean', '25%', '50%', '75%']}) + '\n')
    m = D[['run_id', 'race_id', 'date', 'win', 'price_top', 'priceStarting']].merge(rt[['run_id', 'rating']], on='run_id').merge(comp, left_on='race_id', right_index=True)
    pops = {'rule P (2023-2026)': m[m['run_id'].isin(P_ids)], 'locked rule, real (Apr-Oct 2026)': m[m['run_id'].isin(real_ids)]}
    for nm, pop in pops.items():
        rows = [roi_stats(pop, 'price_top', 'no gate')]
        for thr in (3, 4, 5, 6):
            for N in (4, 5, 6):
                keep = pop[pop[f'n_within_{thr}'].fillna(0) < N]
                r = roi_stats(keep, 'price_top', f'skip compressed: >= {N} within {thr} pts (kept {len(keep)/len(pop)*100:.0f}%)')
                rows.append(r)
        out.append(f'### 3a. {nm}\n')
        out.append(fmt_table(rows) + '\n')
    # gap_1_5 buckets
    for nm, pop in pops.items():
        q = pop['gap_1_5'].quantile([0, .25, .5, .75, 1.0]).values
        rows = []
        for lo, hi in zip(q[:-1], q[1:]):
            s = pop[(pop['gap_1_5'] >= lo) & (pop['gap_1_5'] <= hi)]
            rows.append(roi_stats(s, 'price_top', f'gap_1_5 {lo:.1f} to {hi:.1f}'))
        out.append(f'### 3b. {nm}: ROI by gap_1_5 quartile (larger gap = less compressed)\n')
        out.append(fmt_table(rows) + '\n')
    # real-window alternative ratings (TopRate's own pre-race ratings)
    w = a[['run_id', 'wpr_nett', 'race_id']].rename(columns={'race_id': 'rid'})
    rr = real[['run_id', 'race_id', 'date', 'win', 'price_top', 'starting_price_sp']].merge(a[['run_id', 'wpr_nett']], on='run_id')
    cn = compression(a[['race_id', 'wpr_nett']], 'wpr_nett')
    rr = rr.merge(cn, left_on='race_id', right_index=True)
    rows = [roi_stats(rr, 'price_top', 'locked rule, no gate')]
    for thr in (3, 4, 5, 6):
        for N in (4, 5, 6):
            keep = rr[rr[f'n_within_{thr}'].fillna(0) < N]
            rows.append(roi_stats(keep, 'price_top', f'wpr_nett: skip >= {N} within {thr} (kept {len(keep)/len(rr)*100:.0f}%)'))
    out.append('### 3c. Locked rule (real) gated on compression of TopRate\'s own pre-race wpr_nett\n')
    out.append(fmt_table(rows) + '\n')
    open(os.path.join(RES, 't3.md'), 'w').write('\n'.join(out))
    print('\n'.join(out))


if __name__ == '__main__':
    run()
