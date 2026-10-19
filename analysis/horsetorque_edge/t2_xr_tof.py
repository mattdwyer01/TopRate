"""Test 2: winner-anchored sectional rating XR, TOF, TOF rank, and the avoid flag."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from model import *
from rules import *

RES = os.path.join(os.path.dirname(__file__), 'results')


def avoid_flag(D):
    """Pre-race flag on a runner's NEXT start: last run TOF<0 AND last run settled in the rear third AND (carrying more weight OR racing further)."""
    f = (D['tof_prev'] < 0) & (D['rear_last'] == 1) & ((D['w_up'] > 0) | (D['d_up'] > 0))
    known = D['tof_prev'].notna() & D['rear_last'].notna() & D['w_up'].notna() & D['d_up'].notna()
    return f.where(known)


def run():
    D = prep(pd.read_pickle(os.path.join(CACHE, 'features.pkl')))
    out = ['## Test 2: winner-anchored sectional rating (XR) and TOF\n']
    out.append(f'XR = winner WPR + (runner last-400m - winner last-400m) converted at 1 point per 0.1 s, TOF = XR - WPR. The results files hold last-400m as '
               f'`sect_i_l400` in LENGTHS vs a per-race standard (per-runner last-400m times are not stored; only the winner has a time, and only on 1-30% of races), '
               f'so lengths are converted at 0.147 s per length (1.47 points per length). The repo\'s own rating-per-length slope is ~2.15, so 1.47 compresses XR '
               f'relative to WPR (TOF averages {D["TOF"].mean():+.1f}); a 2.15 version is reported as a sensitivity. Differences beyond +-15 lengths are clipped (sect_i columns hold +-100 data errors). '
               f'Coverage: XR on {D["XR"].notna().mean()*100:.0f}% of runs.\n')
    # ---- 2a: feature comparison
    P = BASE + CLASS_PAR
    sets = {'base + class_par': P, '+ XR/TOF/TOF rank': P + XRTOF, '+ TOF only': P + ['TOF_m3', 'TOF_last', 'tof_rank_pct'], '+ XR only': P + ['XR_m3']}
    D2 = D.copy(); D2['TOF_m3'] = D2['TOF_alt_m3']; D2['TOF_last'] = D2['TOF_alt_last']
    preds = {k: walk_forward(D, c, name=k) for k, c in sets.items()}
    t = model_table(D, preds, 'base + class_par')
    out.append('### 2a. Retrain with vs without XR / TOF / TOF rank (train before Y, test 2023-2026)\n')
    out.append(md(t, {'auc': '{:.4f}', 'logloss': '{:.4f}', 'race_ll': '{:.4f}', 'race_ll_gain_vs_base': '{:+.4f}', 'gain_se': '{:.4f}', 'gain_t': '{:+.1f}', 'top1': '{:.2f}'}) + '\n')
    real_ids, P_ids, a, real = rule_sets(D)
    rows = []
    for k in ('base + class_par', '+ XR/TOF/TOF rank'):
        rows += bet_table(D, {k: preds[k]}, real_ids, P_ids)
    out.append('### 2b. ROI at the Top price with the model as a gate on the rule populations\n')
    out.append(fmt_table(rows) + '\n')
    # ---- 2c: avoid flag
    D['avoid'] = avoid_flag(D)
    D['avoid_alt'] = (((D['TOF_alt_last'] < 0) & (D['rear_last'] == 1) & ((D['w_up'] > 0) | (D['d_up'] > 0)))).where(D['avoid'].notna())
    D['TOF_dm'] = D['TOF'] - D.groupby('race_id')['TOF'].transform('mean')       # race-relative TOF: removes the 1.47 pts/length scale offset
    D['TOF_dm_last'] = asof_last(D, 'TOF_dm')
    D['avoid_dm'] = (((D['TOF_dm_last'] < 0) & (D['rear_last'] == 1) & ((D['w_up'] > 0) | (D['d_up'] > 0)))).where(D['avoid'].notna())
    base = D[(D['price_top'] > 1) & D['avoid'].notna()]
    rows = [roi_stats(base[base['avoid'] == True], 'price_top', 'flag set (all runners)'),
            roi_stats(base[base['avoid'] == False], 'price_top', 'flag not set (all runners)'),
            roi_stats(base[(base['avoid'] == True) & (base['price_top'] >= 3)], 'price_top', 'flag set, Top >= $3'),
            roi_stats(base[(base['avoid'] == False) & (base['price_top'] >= 3)], 'price_top', 'flag not set, Top >= $3')]
    alt = D[(D['price_top'] > 1) & D['avoid_alt'].notna()]
    rows += [roi_stats(alt[alt['avoid_alt'] == True], 'price_top', 'flag set, 2.15 pts/length XR'),
             roi_stats(alt[alt['avoid_alt'] == False], 'price_top', 'flag not set, 2.15 pts/length XR')]
    dm = D[(D['price_top'] > 1) & D['avoid_dm'].notna()]
    rows += [roi_stats(dm[dm['avoid_dm'] == True], 'price_top', 'flag set, race-relative TOF (TOF below the race mean)'), roi_stats(dm[dm['avoid_dm'] == False], 'price_top', 'flag not set, race-relative TOF'),
             roi_stats(dm[(dm['avoid_dm'] == True) & (dm['price_top'] >= 3)], 'price_top', 'race-relative flag set, Top >= $3'), roi_stats(dm[(dm['avoid_dm'] == False) & (dm['price_top'] >= 3)], 'price_top', 'race-relative flag not set, Top >= $3')]
    ids = D[D['run_id'].isin(P_ids) & D['avoid'].notna()]
    rows += [roi_stats(ids[ids['avoid'] == True], 'price_top', 'rule P picks with flag'), roi_stats(ids[ids['avoid'] == False], 'price_top', 'rule P picks without flag')]
    rr = D[D['run_id'].isin(real_ids) & D['avoid'].notna()]
    rdm = D[D['run_id'].isin(real_ids) & D['avoid_dm'].notna()]
    rows += [roi_stats(ids2[ids2['avoid_dm'] == True], 'price_top', 'rule P picks with race-relative flag') for ids2 in [D[D['run_id'].isin(P_ids) & D['avoid_dm'].notna()]]]
    rows += [roi_stats(ids2[ids2['avoid_dm'] == False], 'price_top', 'rule P picks without race-relative flag') for ids2 in [D[D['run_id'].isin(P_ids) & D['avoid_dm'].notna()]]]
    rows += [roi_stats(rdm[rdm['avoid_dm'] == True], 'price_top', 'locked rule picks with race-relative flag (2026)'), roi_stats(rdm[rdm['avoid_dm'] == False], 'price_top', 'locked rule picks without race-relative flag (2026)')]
    rows += [roi_stats(rr[rr['avoid'] == True], 'price_top', 'locked rule picks with flag (2026)'), roi_stats(rr[rr['avoid'] == False], 'price_top', 'locked rule picks without flag (2026)')]
    # win rate vs market-implied for the flag (is it a signal the price already holds?)
    b = base.copy(); b['imp'] = 1 / b['price_top']
    b['imp'] = b['imp'] / b.groupby('race_id')['imp'].transform('sum')
    x = b.groupby('avoid').agg(n=('win', 'size'), win_rate=('win', 'mean'), market_implied=('imp', 'mean'))
    out.append('### 2c. Avoid flag: TOF<0 last start AND rear third at the 800m call AND weight up OR distance up (flag known before the race)\n')
    out.append(f'Flag set on {(D["avoid"]==True).sum():,} runs ({(D["avoid"]==True).sum()/D["avoid"].notna().sum()*100:.1f}% of runs where it can be computed; needs a prior TOF and 800m position). '
               f'It is rare by construction: horses that settle in the rear third almost always finish with a positive TOF (they pass tiring runners), so TOF<0 AND rear third is a narrow corner. '
               f'The race-relative version (TOF below the race mean) is flagged on {(D["avoid_dm"]==True).sum():,} runs ({(D["avoid_dm"]==True).sum()/D["avoid_dm"].notna().sum()*100:.1f}%).\n')
    out.append(fmt_table(rows) + '\n')
    x = x.reset_index(); x['win_rate'] *= 100; x['market_implied'] *= 100
    x['avoid'] = x['avoid'].map({True: 'flag set', False: 'flag not set'})
    out.append('Win rate vs the book-normalised market-implied rate (a flag that the price already holds shows no gap):\n')
    out.append(md(x, {'win_rate': '{:.2f}', 'market_implied': '{:.2f}'}) + '\n')
    # ---- 2d: TOF rank alone as a selection angle
    r = D[D['tof_rank'].notna() & (D['price_top'] >= 3) & (D['field_size'] >= 6)]
    rows = [roi_stats(r[r['tof_rank'] == 1], 'price_top', 'TOF rank 1 (as-of last-3 mean), Top >= $3'), roi_stats(r[r['tof_rank'] <= 2], 'price_top', 'TOF rank <= 2'),
            roi_stats(r[r['tof_rank'] == r.groupby('race_id')['tof_rank'].transform('max')], 'price_top', 'TOF rank last')]
    out.append('### 2d. TOF rank as a stand-alone selection (as-of last-3 mean TOF, fields of 6+)\n')
    out.append(fmt_table(rows) + '\n')
    open(os.path.join(RES, 't2.md'), 'w').write('\n'.join(out))
    pd.to_pickle(preds, os.path.join(CACHE, 'preds_t2.pkl'))
    print('\n'.join(out))


if __name__ == '__main__':
    run()
