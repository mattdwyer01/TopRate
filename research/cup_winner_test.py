"""Melbourne Cup WINNERS (2 Nov 2026).  Run with: PYTHONPATH=.:projection python research/cup_winner_test.py

1) The six 2020-25 Cup winners going in (the 2020 winner, an international, has no results-file rating).
2) Win-specific pointers learned ONLY on 2800m+ races that are not Cups (win rate with the rule against the base), then where the Cup winners ranked under them.
3) A small logistic model of winning (same inputs), fitted on the non-Cup staying races, scored on the Cups (out of sample): winner's rank in each Cup, winner log-likelihood against
   chance and against the starting prices.
4) The 2026 field under the same model.
Read-only; ratings are results-file plain ratings on the ATW scale of the race weight for past races and the runner pages' ATW figures for 2026.
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
import cup_group_test as G  # noqa: E402
import ctx as C  # noqa: E402

pd.set_option('display.width', 250)
pd.set_option('display.max_columns', 40)
FEATS = ['gap3', 'gap_peak8', 'last_frac', 'wt_rel', 'placed24', 'n28', 'days_c', 'bar_frac', 'age_c']
RACE = pd.Timestamp('2026-11-03')


def prep(x):
    g = x.groupby('race_id') if 'race_id' in x.columns else x.groupby(lambda i: 0)
    x['gap_peak8'] = g.peak8.transform('max') - x.peak8
    x['days_c'] = x.days_since.clip(upper=60)
    x['age_c'] = x.horse_age.clip(upper=8)
    return x


def softmax_rank(df, score_col):
    out = []
    for _, r in df.groupby('race_id'):
        s = r[score_col].values
        p = np.exp(s - s.max())
        out.append(pd.Series(p / p.sum(), index=r.index))
    return pd.concat(out)


def main():
    t = G.build()
    t['act'] = t.wpr + t.off
    t = prep(t)
    allC = t[t.cup].copy()
    Cg = allC[allC.n >= 3].copy()
    N = t[~t.cup & (t.n >= 3)].copy()
    # ---- 1) the winners
    print('=== 1) The six Cup winners going in ===')
    rows = []
    Cg['rk3'] = Cg.groupby('date').last3.rank(ascending=False, method='min')
    for dt, g in allC.groupby('date'):
        w = g[g.win == 1]
        if w.empty:
            continue
        w = w.iloc[0]
        gr = Cg[Cg.date == dt]
        ww = gr[gr.win == 1]
        rows.append(dict(cup=dt.year, winner=w.horse, rated=int(w.n >= 3), cup_run=w.act, last3=w.last3, gap_to_best=w.gap3 if w.n >= 3 else np.nan,
                         rank_last3=float(ww.rk3.iloc[0]) if len(ww) else np.nan, field_rated=len(gr), peak8=w.peak8, last_start=f"{int(w.pos1)}/{int(w.fie1)}" if pd.notna(w.pos1) else '-',
                         days=w.days_since, kg=w.weightCarried, wt_rel=w.wt_rel if w.n >= 3 else np.nan, age=w.horse_age, placed24=w.placed24, sp=w.priceStarting))
    print(pd.DataFrame(rows).round(1).to_string(index=False))

    # ---- 2) win pointers from non-Cup races
    print('\n=== 2) Win rate by rule in non-Cup 2800m+ races (win lift = win rate with the rule / base win rate) ===')
    nb = N.win.mean()
    keep = []
    print(f'  non-Cup runners {len(N)}, winners {int(N.win.sum())}, base win rate {nb * 100:.1f}%')
    for name, (sign, f) in G.RULES.items():
        m = f(N).fillna(False)
        if m.sum() < 100:
            continue
        lift = N[m].win.mean() / nb
        ok = (lift >= 1.08) if sign > 0 else (lift <= 0.92)
        if ok:
            keep.append(name)
        cm = f(Cg).fillna(False)
        print(f"    {'+' if sign > 0 else '-'} {name:28s} non-Cup n={int(m.sum()):5d} win lift {lift:4.2f} {'KEEP' if ok else 'drop'} | Cups: {int(cm.sum()):3d} of {len(Cg)} rated runners, winners meeting it {int((cm & (Cg.win == 1)).sum())} of {int(Cg.win.sum())}")
    Cg['s_w'] = G.score(Cg, keep)
    Cg['key'] = Cg.s_w * 1000 + Cg.last3.fillna(0)
    Cg['rk_rules'] = Cg.groupby('date').key.rank(ascending=False, method='min')
    print(f'\n  Winner rank among the rated runners under the {len(keep)} kept rules (1 = top; ties broken by last-3):')
    for dt, g in Cg.groupby('date'):
        w = g[g.win == 1]
        if len(w):
            print(f"    {dt.year}: rank {int(w.rk_rules.iloc[0])} of {len(g)} rated; by last-3 alone rank {int(w.rk3.iloc[0])}")
        else:
            print(f'    {dt.year}: winner not rated')

    # ---- 3) logistic win model fitted on non-Cups, scored on Cups
    from sklearn.linear_model import LogisticRegression
    from sklearn.preprocessing import StandardScaler
    Nf = N.dropna(subset=['gap3', 'last_frac', 'wt_rel']).copy()
    med = Nf[FEATS].median()
    X = Nf[FEATS].fillna(med)
    sc = StandardScaler().fit(X)
    lr = LogisticRegression(C=0.3, max_iter=500).fit(sc.transform(X), Nf.win)
    print('\n=== 3) Logistic win model fitted on non-Cup 2800m+ races (standardised coefficients; + = more likely to win) ===')
    for f_, c_ in sorted(zip(FEATS, lr.coef_[0]), key=lambda z: -abs(z[1])):
        print(f'    {f_:12s} {c_:+.3f}')
    Cm = Cg.dropna(subset=['gap3', 'last_frac', 'wt_rel']).copy()
    Cm['score'] = lr.decision_function(sc.transform(Cm[FEATS].fillna(med)))
    Cm['p'] = softmax_rank(Cm, 'score') if 'race_id' in Cm.columns else np.nan
    Cm['rk_model'] = Cm.groupby('date').score.rank(ascending=False, method='min')
    sp = Cm.priceStarting.where(Cm.priceStarting > 1)
    Cm['p_sp'] = (1 / sp) / (1 / sp).groupby(Cm.date).transform('sum')
    print('\n  Cup winners under the model (out of sample): rank among rated runners, model win chance, starting-price chance, chance at random')
    lls = []
    for dt, g in Cm.groupby('date'):
        w = g[g.win == 1]
        if len(w):
            w = w.iloc[0]
            print(f"    {dt.year}: {w.horse:18s} model rank {int(w.rk_model):2d} of {len(g)}  model chance {w.p * 100:4.1f}%  SP chance {w.p_sp * 100:4.1f}% (SP {w.priceStarting:.1f})  random {100 / len(g):4.1f}%")
            lls.append((np.log(w.p), np.log(w.p_sp), np.log(1 / len(g))))
    if lls:
        a = np.array(lls)
        print(f'  Winner log-likelihood over {len(a)} Cups: model {a[:, 0].mean():+.2f}  starting price {a[:, 1].mean():+.2f}  random {a[:, 2].mean():+.2f}   (higher is better)')
    top3 = [(g[g.win == 1].rk_model.iloc[0] <= 3) for _, g in Cm.groupby('date') if (g.win == 1).any()]
    top5 = [(g[g.win == 1].rk_model.iloc[0] <= 5) for _, g in Cm.groupby('date') if (g.win == 1).any()]
    print(f'  Winner in the model\'s top 3: {sum(top3)} of {len(top3)}; top 5: {sum(top5)} of {len(top5)}  (random: about {np.mean([3 / len(g) for _, g in Cm.groupby("date")]) * len(top3):.1f} and {np.mean([5 / len(g) for _, g in Cm.groupby("date")]) * len(top5):.1f})')
    # same check on non-Cup races (big sample): winner in model top 3 vs chance, using an honest split by year
    Nf['score'] = lr.decision_function(sc.transform(Nf[FEATS].fillna(med)))
    Nf['rk'] = Nf.groupby('race_id').score.rank(ascending=False, method='min')
    big = Nf[Nf.groupby('race_id').win.transform('sum') == 1]
    hit3 = big[big.win == 1].rk.le(3).mean()
    rnd3 = (3 / big.groupby('race_id').size()).mean()
    print(f'  In-sample on the non-Cup races themselves: winner in the top 3 of the model {hit3 * 100:.0f}% (random {rnd3 * 100:.0f}%), top pick wins {(big[big.rk == 1].win.mean()) * 100:.1f}% ')

    # ---- 4) 2026 field
    rp = C.page_frame()
    r = pd.read_csv(os.path.join(ROOT, 'runners.csv'), low_memory=False)
    cup = r[(r.date == '2026-11-03') & (r.venue == 'Flemington') & (r.race == 7) & (r.scratched.fillna(0) != 1) & (r.barrier > 0)].copy()
    rows = []
    for _, h in cup.iterrows():
        x = rp[rp.horse_id == h.horse_id].sort_values('date').tail(8)
        W, D, P, FS, d0 = x.wpr.values[::-1], x.distance.values[::-1], x.positionFinish.values[::-1], x.field_size.values[::-1], x.date.values[::-1]
        rows.append(dict(horse=h.horse, barrier=h.barrier, weight=h.weight_carried, horse_age=h.get('horse_age'), last3=np.nanmean(W[:3]), peak8=np.nanmax(W), placed24=int(((D >= 2400) & (P <= 3)).sum()),
                         n28=int((D >= 2800).sum()), days_since=(RACE - pd.Timestamp(d0[0])).days, last_frac=P[0] / FS[0] if FS[0] else np.nan, last_pos=P[0], last_field=FS[0]))
    f = pd.DataFrame(rows)
    f['race_id'] = 1
    f['gap3'] = f.last3.max() - f.last3
    f['gap_peak8'] = f.peak8.max() - f.peak8
    f['wt_rel'] = f.weight - f.weight.mean()
    f['bar_frac'] = f.barrier / len(f)
    f['days_c'] = f.days_since.clip(upper=60)
    f['age_c'] = f.horse_age.clip(upper=8)
    f['score'] = lr.decision_function(sc.transform(f[FEATS].fillna(med)))
    f['p'] = softmax_rank(f, 'score')
    print('\n=== 4) The 2026 field under the win model (fitted on non-Cup races; a profile share, not a price) ===')
    f = f.sort_values('p', ascending=False)
    L = pd.read_csv(os.path.join(ROOT, 'wpr_projection_log.csv.gz'), low_memory=False).drop_duplicates('run_id', keep='last')
    f = f.merge(cup[['horse', 'run_id']].merge(L[['run_id', 'proj']], on='run_id', how='left')[['horse', 'proj']], on='horse', how='left')
    f['rank_win_model'] = np.arange(1, len(f) + 1)
    print(f[['rank_win_model', 'horse', 'p', 'last3', 'gap3', 'peak8', 'weight', 'last_pos', 'last_field', 'placed24', 'days_since', 'barrier', 'proj']].round(3).to_string(index=False))


if __name__ == '__main__':
    main()
