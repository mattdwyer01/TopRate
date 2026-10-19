"""Test 4: race shape from settling positions and the 'Golden 8' claim (~75% of winners come from the first 8 settled positions).
Nothing is written to runners.csv: projected race shape goes to results/race_shape_projected.csv.gz for inspection only."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from model import *
from sklearn.linear_model import Ridge

RES = os.path.join(os.path.dirname(__file__), 'results')


def load_shape():
    parts = []
    for y in range(2019, 2027):
        d = pd.read_csv(os.path.join(ROOT, f'race_results_{y}.csv.gz'), usecols=['race_id', 'raceShapeEarly', 'raceShapeMid', 'raceShapeLate'], low_memory=False)
        parts.append(d.groupby('race_id').first().reset_index())
    return pd.concat(parts).drop_duplicates('race_id')


def run():
    D = prep(pd.read_pickle(os.path.join(CACHE, 'features.pkl')))
    out = ['## Test 4: race shape and the Golden 8\n']
    out.append('"Settled position" is the 800m call (`position800m`): `positionSettled` is blank in every results file. For sprints this call is close to the start, for '
               'staying races it is mid-race. Only races where the winner and at least 80% of the field have an 800m position are used.\n')
    R = D[D['settle'].notna()].copy()
    cover = D.groupby('race_id')['settle'].apply(lambda s: s.notna().mean())
    ok = cover[cover >= 0.8].index
    R = R[R['race_id'].isin(ok)]
    wr = R[R['win'] == 1]
    races = wr['race_id'].nunique()
    # ---- 4a: by settled position
    rows = []
    cum = 0
    for p in list(range(1, 13)) + [13]:
        sel = (R['settle'] == p) if p < 13 else (R['settle'] >= 13)
        n = int(sel.sum()); w = int((sel & (R['win'] == 1)).sum())
        cum += w
        rows.append(dict(settled_position=str(p) if p < 13 else '13+', runners=n, winners=w, winner_share_pct=w / races * 100, cumulative_pct=cum / races * 100, win_rate_pct=w / max(n, 1) * 100,
                         avg_top_price=R[sel & R['price_top'].notna()]['price_top'].mean()))
    out.append(f'### 4a. Winners by settled position ({races:,} races, all field sizes)\n')
    out.append(md(pd.DataFrame(rows), {'winner_share_pct': '{:.1f}', 'cumulative_pct': '{:.1f}', 'win_rate_pct': '{:.1f}', 'avg_top_price': '{:.1f}'}) + '\n')
    # ---- 4b: first-8 share vs the share of runners in the first 8 (fields <=8 are trivially 100%)
    R['first8'] = R['settle'] <= 8
    bands = [(4, 8), (9, 10), (11, 12), (13, 14), (15, 24)]
    rows = []
    for lo, hi in bands:
        s = R[(R['field_size'] >= lo) & (R['field_size'] <= hi)]
        rw = s[s['win'] == 1]
        rows.append(dict(field_size=f'{lo}-{hi}' if lo > 4 else '<=8', races=len(rw), winners_in_first8_pct=rw['first8'].mean() * 100, runners_in_first8_pct=s['first8'].mean() * 100,
                         lift=rw['first8'].mean() / s['first8'].mean(), win_rate_first8=s[s['first8']]['win'].mean() * 100, win_rate_9plus=s[~s['first8']]['win'].mean() * 100))
    s = R[R['field_size'] >= 9]; rw = s[s['win'] == 1]
    rows.append(dict(field_size='9+ all', races=len(rw), winners_in_first8_pct=rw['first8'].mean() * 100, runners_in_first8_pct=s['first8'].mean() * 100, lift=rw['first8'].mean() / s['first8'].mean(),
                     win_rate_first8=s[s['first8']]['win'].mean() * 100, win_rate_9plus=s[~s['first8']]['win'].mean() * 100))
    out.append('### 4b. First-8 share by field size (the claim only has content when the field is larger than 8)\n')
    out.append(md(pd.DataFrame(rows), {k: '{:.1f}' for k in ['winners_in_first8_pct', 'runners_in_first8_pct', 'win_rate_first8', 'win_rate_9plus']} | {'lift': '{:.2f}'}) + '\n')
    # ---- 4c: by distance band, fields of 9+
    s9 = R[R['field_size'] >= 9].copy()
    s9['dband'] = pd.cut(s9['distance'], [0, 1100, 1300, 1600, 2000, 5000], labels=['<=1100', '1101-1300', '1301-1600', '1601-2000', '2000+'])
    rows = []
    for b, g in s9.groupby('dband', observed=True):
        rw = g[g['win'] == 1]
        rows.append(dict(distance=b, races=len(rw), winners_in_first8_pct=rw['first8'].mean() * 100, runners_in_first8_pct=g['first8'].mean() * 100, lift=rw['first8'].mean() / g['first8'].mean()))
    out.append('### 4c. Fields of 9+ by distance\n')
    out.append(md(pd.DataFrame(rows), {'winners_in_first8_pct': '{:.1f}', 'runners_in_first8_pct': '{:.1f}', 'lift': '{:.2f}'}) + '\n')
    # ---- 4d: projected map position (as-of avg settle of last 3) vs actual
    P = D[D['settle_m3_pos'].notna() & D['settle'].notna() & (D['field_size'] >= 9)].copy()
    P['proj_rank'] = P.groupby('race_id')['settle_m3_pos'].rank(method='first')
    P['act_first8'] = P['settle'] <= 8
    rho = P[['settle_m3_pos', 'settle']].rank().corr().iloc[0, 1]
    pw = P[P['win'] == 1]
    rows = [dict(measure='Spearman: projected avg settle vs actual 800m position', value=rho),
            dict(measure='runners projected in first 8 (rank<=8) who actually settle in first 8, %', value=P[P['proj_rank'] <= 8]['act_first8'].mean() * 100),
            dict(measure='winners with projected rank <= 8, % (fields 9+)', value=(pw['proj_rank'] <= 8).mean() * 100),
            dict(measure='runners with projected rank <= 8, % (fields 9+)', value=(P['proj_rank'] <= 8).mean() * 100),
            dict(measure='win rate, projected rank <= 8, %', value=P[P['proj_rank'] <= 8]['win'].mean() * 100),
            dict(measure='win rate, projected rank > 8, %', value=P[P['proj_rank'] > 8]['win'].mean() * 100)]
    out.append('### 4d. Projected map position (mean 800m position of the last 3 starts) in fields of 9+\n')
    out.append(md(pd.DataFrame(rows), {'value': '{:.3f}'}) + '\n')
    # ---- 4e: projected race shape vs TopRate's realised shape
    sh = load_shape()
    Q = D[D['settle_m3_pos'].notna()].copy()
    Q['leader'] = (Q['settle_m3_pos'] <= 3).astype(float)
    Q['front3'] = (Q['settle_m3_pos'] <= 3.5) & (Q['sect_i_early_m5'] > Q['sect_i_early_m5'].median())
    g = Q.groupby('race_id')
    Rc = pd.DataFrame({'n_leaders': g['leader'].sum(), 'mean_front3': g['settle_m3_pos'].apply(lambda s: s.nsmallest(3).mean()), 'field': g.size(),
                       'early_speed_top3': g['sect_i_early_m5'].apply(lambda s: s.nlargest(3).mean()), 'year': g['dt_year'].first(), 'dist': g['distance'].first()})
    Rc = Rc.join(sh.set_index('race_id'), how='inner').dropna(subset=['n_leaders', 'mean_front3'])
    feats = ['n_leaders', 'mean_front3', 'field', 'early_speed_top3', 'dist']
    Rc[feats] = Rc[feats].astype(float).fillna(Rc[feats].median())
    rows = []
    proj = []
    for tgt in ('raceShapeEarly', 'raceShapeMid', 'raceShapeLate'):
        d = Rc.dropna(subset=[tgt])
        pr = []
        for ty in (2023, 2024, 2025, 2026):
            tr = d[d['year'] < ty]; te = d[d['year'] == ty]
            m = Ridge(alpha=1.0).fit((tr[feats] - tr[feats].mean()) / tr[feats].std(), tr[tgt])
            p = m.predict((te[feats] - tr[feats].mean()) / tr[feats].std())
            pr.append(pd.Series(p, index=te.index, name=tgt + '_proj'))
        pr = pd.concat(pr); te = d.loc[pr.index]
        r2 = 1 - ((te[tgt] - pr) ** 2).sum() / ((te[tgt] - te[tgt].mean()) ** 2).sum()
        rows.append(dict(target=tgt, races=len(te), r2_out_of_sample=r2, corr=np.corrcoef(te[tgt], pr)[0, 1],
                         corr_n_leaders=np.corrcoef(te[tgt], te['n_leaders'])[0, 1]))
        proj.append(pr)
    out.append('### 4e. Race shape projected from settling positions (race_shape_early / mid / late)\n')
    out.append('Race-level ridge regression of TopRate\'s realised raceShapeEarly/Mid/Late on pre-race pace pressure (number of horses whose average settle is 3 or better, '
               'mean settle of the 3 most forward, field size, early-speed history, distance), walk-forward 2023-2026. This is the version of "populate race_shape" that can be '
               'known before the race; the realised values are post-race and are what the runners file would hold after the result.\n')
    out.append(md(pd.DataFrame(rows), {'r2_out_of_sample': '{:.3f}', 'corr': '{:.3f}', 'corr_n_leaders': '{:.3f}'}) + '\n')
    pd.concat(proj, axis=1).reset_index().to_csv(os.path.join(RES, 'race_shape_projected.csv.gz'), index=False)
    # ---- 4f: retrain with projected map position
    P8 = BASE + CLASS_PAR
    sets = {'base + class_par': P8, '+ projected map position (avg settle, rank pct, first-8 flag)': P8 + MAP}
    preds = {k: walk_forward(D, c, name=k) for k, c in sets.items()}
    t = model_table(D, preds, 'base + class_par')
    out.append('### 4f. Retrain with projected map position (settle_m3_pos, map_rank_pct, golden8 flag)\n')
    out.append(md(t, {'auc': '{:.4f}', 'logloss': '{:.4f}', 'race_ll': '{:.4f}', 'race_ll_gain_vs_base': '{:+.4f}', 'gain_se': '{:.4f}', 'gain_t': '{:+.1f}', 'top1': '{:.2f}'}) + '\n')
    real_ids, P_ids, a, real = rule_sets(D)
    rows = []
    for k in preds:
        rows += bet_table(D, {k: preds[k]}, real_ids, P_ids)
    out.append('### 4g. ROI at the Top price with the model as a gate\n')
    out.append(fmt_table(rows) + '\n')
    open(os.path.join(RES, 't4.md'), 'w').write('\n'.join(out))
    pd.to_pickle(preds, os.path.join(CACHE, 'preds_t4.pkl'))
    print('\n'.join(out))


if __name__ == '__main__':
    run()
