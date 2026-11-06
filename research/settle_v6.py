"""Settling position forecast: what could improve it? (5 Nov 2026). Reuses the shape_study feature build (import runs it; V12 = the best known input set,
spearman 0.5586 on 2025-01 on) and tests, time-forward on the same blocks:
  B    baseline V12 (regression on position fraction at 800m)
  L1   + meeting lean usable live (earlier races of the SAME meeting: top-4 finishers' barrier lean, from finishing order only)
  L2   + lean that needs 800m positions (earlier winners' / placegetters' early position, leader held on), VIC/SA GPS only live
  M    + closing market (ln SP, rank, normalised chance): an upper bound for early-price information
  P    + horse x jockey / jockey lead rates
  ALL  everything above
For each set: spearman of the regression, and the quantity the bet rule uses, "is this runner in the first third of the field at 800m"
(ft = (pos800 - 1) / (nr - 1) <= 1/3): the hard rule (rank the regression, cut at a third), a direct classifier P(first third), AUC / log loss / Brier,
precision of the hard cut vs the classifier at the SAME number of selections, and precision at probability thresholds.
Run: PYTHONPATH=.:projection:research python research/settle_v6.py --variants B,L1,L2
"""
import sys, os
_args = sys.argv[1:]
VAR = 'B'
if '--variants' in _args:
    VAR = _args[_args.index('--variants') + 1]
sys.argv = ['shape_study.py', '--variants', 'V12', '--out', '/tmp/settle_out']
import numpy as np, pandas as pd, lightgbm as lgb
from sklearn.metrics import roc_auc_score, log_loss, brier_score_loss
import shape_study as ss
log = ss.log
S = ss.S.copy()
ROOT = ss.ROOT

# ---- first-third target
S['ft'] = np.where(S.pos800.notna() & (S.nr >= 2), ((S.pos800 - 1) / (S.nr - 1).clip(lower=1) <= 1 / 3 + 1e-9).astype(float), np.nan)

# ---- meeting lean from earlier races of the same meeting
R = S.drop_duplicates('race_id')[['race_id', 'meeting_id', 'rn', 'date']].copy()
t4 = S[S.pos <= 4].groupby('race_id').barfrac.mean() - 0.5
t3e = S[S.pos <= 3].groupby('race_id').e0.mean()
we = S[S.pos == 1].groupby('race_id').e0.mean()
ld = S[S.pos800 == 1].groupby('race_id').pos.min()
R['lf_draw'] = R.race_id.map(t4)
R['lf_front'] = R.race_id.map(t3e)
R['lf_win_e'] = R.race_id.map(we)
R['lf_held'] = R.race_id.map(ld.le(3).astype(float))
R = R.sort_values(['meeting_id', 'rn'])
for c in ('lf_draw', 'lf_front', 'lf_win_e', 'lf_held'):
    R['ml_' + c[3:]] = R.groupby('meeting_id')[c].transform(lambda s: s.shift(1).expanding().mean())
R['ml_n'] = R.groupby('meeting_id').cumcount().astype(float)
S = S.merge(R[['race_id', 'ml_draw', 'ml_front', 'ml_win_e', 'ml_held', 'ml_n']], on='race_id', how='left')
S['x_draw'] = (S.barfrac - 0.5) * S.ml_draw
S['x_front'] = (S.e_ewm2 - 0.5) * (S.ml_front - 0.5)
S['x_held'] = (S.e_ewm2 - 0.5) * (S.ml_held - 0.5)
log('meeting lean done; runs with 3+ earlier races', int((S.ml_n >= 3).sum()))

# ---- closing market (ln SP etc.)
if 'priceStarting' not in S.columns:
    pr = pd.concat([pd.read_csv(os.path.join(ROOT, f'race_results_{y}.csv.gz'), usecols=['race_id', 'horse_id', 'priceStarting'], low_memory=False)
                    for y in range(2016, 2027)], ignore_index=True)
    pr['horse_id'] = pd.to_numeric(pr.horse_id, errors='coerce').astype(float)
    pr = pr.drop_duplicates(['race_id', 'horse_id'])
    S = S.merge(pr, on=['race_id', 'horse_id'], how='left')
sp = pd.to_numeric(S.priceStarting, errors='coerce').where(lambda x: x > 1)
S['lsp'] = np.log(sp)
g = S.groupby('race_id')
S['m_gap'] = S.lsp - g.lsp.transform('min')
S['m_rank'] = g.lsp.rank(pct=True)
imp = 1 / sp
S['m_prob'] = imp / imp.groupby(S.race_id).transform('sum')
S['m_fav'] = (g.lsp.rank(method='min') == 1).astype(float).where(S.lsp.notna())
log('market joined', int(S.lsp.notna().sum()))

# ---- horse x jockey and jockey lead rates
S['pair_lead'] = ss.asof_rate(S, 'pair', 'lead', prior=0.1, k=2)
S['jk_lead'] = ss.asof_rate(S, 'jk', 'lead', prior=0.1, k=50)
S['jkth'] = S.jk.astype(str) + '|' + S.third.astype(str)
S['jkth_lead'] = ss.asof_rate(S, 'jkth', 'lead', prior=0.1, k=30)
S['jkth_e'] = ss.asof_rate(S, 'jkth', 'e0', prior=0.5, k=30)

BASE = ss.FS['V12']
L1 = ['ml_n', 'ml_draw', 'x_draw']
L2 = L1 + ['ml_front', 'ml_win_e', 'ml_held', 'x_front', 'x_held']
M = ['lsp', 'm_gap', 'm_rank', 'm_prob', 'm_fav']
P = ['pair_lead', 'jk_lead', 'jkth_lead', 'jkth_e']
SETS = {'B': BASE, 'L1': BASE + L1, 'L2': BASE + L2, 'M': BASE + M, 'P': BASE + P, 'ALL': BASE + L2 + M + P}

NR, P0 = ss.NR, ss.P0
TEST_EDGES = ss.TEST_EDGES


def hard_flag(df, score):
    rk = pd.Series(score, index=df.index).groupby(df.race_id).rank(method='first')
    return (((rk - 1) / (df.nr - 1).clip(lower=1)) <= 1 / 3 + 1e-9)


def run(name, feats):
    pe = pd.Series(np.nan, index=S.index)
    pc = pd.Series(np.nan, index=S.index)
    for a, b in zip(TEST_EDGES[:-1], TEST_EDGES[1:]):
        trn = S[(S.date < a) & S.e0.notna() & S.g0.notna()]
        if len(trn) > ss.TRAIN_CAP:
            trn = trn[trn.race_id.isin(trn.race_id.drop_duplicates().sample(frac=ss.TRAIN_CAP / len(trn), random_state=1))]
        blk = S[(S.date >= a) & (S.date < b) & S.e0.notna()]
        if len(blk) == 0:
            continue
        m = lgb.train(dict(P0, objective='regression'), lgb.Dataset(trn[feats], trn.e0), NR)
        pe.loc[blk.index] = m.predict(blk[feats])
        t2 = trn[trn.ft.notna()]
        mc = lgb.train(dict(P0, objective='binary'), lgb.Dataset(t2[feats], t2.ft), NR)
        pc.loc[blk.index] = mc.predict(blk[feats])
        log(f'  {name} block {a.date()} done')
    test = S[(S.date >= TEST_EDGES[0]) & (S.date < TEST_EDGES[-1]) & S.e0.notna()].copy()
    test['pe'] = pe.loc[test.index]
    test['pc'] = pc.loc[test.index]
    res = ss.evaluate(test, test.pe, f'{name}/reg')
    out = dict(name=name, spearman=res['spearman_pos'], auc_lead=res['auc_lead'])
    d = test[test.nr >= 6]
    cnt = d.groupby('race_id').pos800.transform('count'); sz = d.groupby('race_id').pe.transform('size')
    d = d[(cnt == sz) & d.ft.notna()].copy()
    for lab, dd in (('all6+', d), ('8+', d[d.nr >= 8])):
        hf = hard_flag(dd, dd.pe.values)
        cf = hard_flag(dd, -dd.pc.values)           # classifier ordering, same rank cut
        k = int(hf.sum())
        topk = dd.pc.rank(method='first', ascending=False) <= k
        rows = {f'{lab}_n': len(dd), f'{lab}_base': dd.ft.mean(), f'{lab}_auc_reg': roc_auc_score(dd.ft, -dd.pe), f'{lab}_auc_cls': roc_auc_score(dd.ft, dd.pc),
                f'{lab}_ll': log_loss(dd.ft, dd.pc.clip(1e-6, 1 - 1e-6)), f'{lab}_ll_base': log_loss(dd.ft, np.full(len(dd), dd.ft.mean())),
                f'{lab}_brier': brier_score_loss(dd.ft, dd.pc),
                f'{lab}_prec_hard': dd.ft[hf].mean(), f'{lab}_prec_clsrank': dd.ft[cf].mean(), f'{lab}_prec_topk': dd.ft[topk].mean(), f'{lab}_k': k}
        for th in (0.5, 0.6, 0.7, 0.8):
            s = dd.pc >= th
            rows[f'{lab}_p{int(th * 100)}_n'] = int(s.sum()); rows[f'{lab}_p{int(th * 100)}_prec'] = dd.ft[s].mean() if s.any() else np.nan
        out.update(rows)
        log(f'  {name} [{lab}] n={len(dd)} base={dd.ft.mean():.3f}  AUC reg {rows[lab + "_auc_reg"]:.4f} cls {rows[lab + "_auc_cls"]:.4f}  logloss {rows[lab + "_ll"]:.4f} (base {rows[lab + "_ll_base"]:.4f}) '
            f'precision hard {rows[lab + "_prec_hard"]:.3f} cls-rank {rows[lab + "_prec_clsrank"]:.3f} cls-top-{k} {rows[lab + "_prec_topk"]:.3f}')
        log('     thresholds: ' + '  '.join(f'p>={th}: n={rows[f"{lab}_p{int(th*100)}_n"]} prec={rows[f"{lab}_p{int(th*100)}_prec"]:.3f}' for th in (0.5, 0.6, 0.7, 0.8)))
    return out, test[['race_id', 'horse_id', 'pe', 'pc']]


if __name__ == '__main__':
    outs = []
    for v in VAR.split(','):
        v = v.strip()
        o, preds = run(v, [c for c in dict.fromkeys(SETS[v]) if c in S.columns])
        outs.append(o)
        preds.to_pickle(os.path.join(ss.ARGS.out, f'pred_{v}.pkl'))
    pd.DataFrame(outs).to_csv(os.path.join(ss.ARGS.out, f'settle_{VAR.replace(",", "_")}.csv'), index=False)
    log('done')
