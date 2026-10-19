"""Test 1: class par ladder. Class_move / peak_at_class recomputed off class_par; sr_vs_par as a candidate feature."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from model import *

RES = os.path.join(os.path.dirname(__file__), 'results'); os.makedirs(RES, exist_ok=True)


def run():
    D = prep(pd.read_pickle(os.path.join(CACHE, 'features.pkl')))
    out = ['## Test 1: class par ladder\n']
    # ---- table 1a: coverage and shape of the ladder
    D['par_band'] = pd.cut(D['class_par'], [0, 86.5, 90, 92, 94, 96.5, 99, 101, 104, 108, 120],
                           labels=['86 Maiden', '86.5-90 low BM/CLS', '90-92 BM62-ish', '92-94', '94-96.5', '96.5-99', '99-101 Open/LR', '101-104 G3/LR', '104-108 G2', '108+ G1'])
    w = D[D['win'] == 1]
    t = D.groupby('par_band', observed=True).agg(runs=('win', 'size'), mean_wpr=('wpr', 'mean')).join(
        w.groupby('par_band', observed=True).agg(winner_mean_wpr=('wpr', 'mean'))).reset_index()
    out.append('### 1a. Ladder coverage and whether par tracks the ratings (2019-2026 flat runs)\n')
    out.append(f"class_par mapped on {D['class_par'].notna().mean()*100:.2f}% of runs. F&M / 3YOF rungs could be applied to only "
               f"{D['race_name'].astype(str).str.contains(r'fillies|filly|mares|mare|oaks', case=False, regex=True).mean()*100:.3f}% of runs (race_name is filled on ~15% of rows), so they are effectively unused.\n")
    out.append(md(t, {'mean_wpr': '{:.1f}', 'winner_mean_wpr': '{:.1f}'}) + '\n')
    # monotonic check old rung vs class_par vs the buggy trackGrading
    rows = []
    for nm, c in (('trackGrading (bug)', 'tg'), ('retired rung ladder', 'rung_old'), ('class_par', 'class_par')):
        x = D[[c, 'wpr']].dropna()
        rows.append(dict(ladder=nm, spearman_with_wpr=x[c].rank().corr(x['wpr'].rank()), pearson_with_wpr=x[c].corr(x['wpr'])))
    out.append('Correlation of each class measure with the run rating (higher = the ladder really measures class):\n')
    out.append(md(pd.DataFrame(rows)) + '\n')

    # ---- 1a-ii: is each rung calibrated? winner rating minus par should be roughly constant down the ladder
    def grp(r):
        c = str(r['race_class']).upper(); b = r['blackType']
        if isinstance(b, str): return b
        if c == 'OPEN': return 'Open (no black type)'
        if c.startswith('MAI'): return 'Maiden'
        p = r['class_par']
        return 'BM/CLS ' + ('94+' if p >= 98 else '84-93' if p >= 96 else '74-83' if p >= 93 else '62-73' if p >= 91 else 'below 62')
    u = D[['race_class', 'blackType', 'class_par']].drop_duplicates()
    u['grp'] = u.apply(grp, axis=1)
    G = D.merge(u, on=['race_class', 'blackType', 'class_par'], how='left')
    gw = G[G['win'] == 1]
    t2 = gw.groupby('grp').agg(races=('win', 'size'), par=('class_par', 'mean'), winner_wpr=('wpr', 'mean')).reset_index()
    t2['winner_wpr_minus_par'] = t2['winner_wpr'] - t2['par']
    t2 = t2.sort_values('par', ascending=False)
    out.append('Calibration of the rungs (winners only): if the ladder were in WPR points, winner WPR minus par would be flat down the table.\n')
    out.append(md(t2, {'par': '{:.1f}', 'winner_wpr': '{:.1f}', 'winner_wpr_minus_par': '{:+.1f}'}) + '\n')

    # ---- table 1b: walk-forward feature comparison
    sets = {'base': BASE, '+class_move/peak (trackGrading bug)': BASE + CLASS_BUG, '+class_move/peak (retired rung ladder)': BASE + CLASS_RUNG,
            '+class_move/peak (class_par)': BASE + CLASS_PAR, '+class_par +sr_vs_par': BASE + CLASS_PAR + SR_PAR, '+sr_vs_par only': BASE + SR_PAR}
    preds = {}
    for k, cols in sets.items():
        preds[k] = walk_forward(D, cols, name=k)
        print('fit', k, flush=True)
    t = model_table(D, preds, 'base')
    out.append('### 1b. Out-of-sample model comparison (train before year Y, test 2023-2026)\n')
    out.append('Gain = paired reduction in race-level winner log-loss vs base (positive = better); t = gain / s.e. over races.\n')
    out.append(md(t, {'auc': '{:.4f}', 'logloss': '{:.4f}', 'race_ll': '{:.4f}', 'race_ll_gain_vs_base': '{:+.4f}', 'gain_se': '{:.4f}', 'gain_t': '{:+.1f}', 'top1': '{:.2f}'}) + '\n')
    # ---- table 1c: bets
    real_ids, P_ids, a, real = rule_sets(D)
    rows = []
    for k in ('base', '+class_move/peak (class_par)', '+class_par +sr_vs_par'):
        rows += bet_table(D, {k: preds[k]}, real_ids, P_ids)
    out.append('### 1c. ROI at the Top price (flat 1 unit, fixed-odds win), model gates on the two rule populations\n')
    out.append(fmt_table(rows) + '\n')
    open(os.path.join(RES, 't1.md'), 'w').write('\n'.join(out))
    pd.to_pickle({k: v for k, v in preds.items()}, os.path.join(CACHE, 'preds_t1.pkl'))
    print('\n'.join(out))


if __name__ == '__main__':
    run()
