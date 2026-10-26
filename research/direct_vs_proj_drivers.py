"""What drives the direct model (B3) away from Proj on the 559 complete real-page fields where every runner has a dashboard Proj (26 Oct 2026).
Inputs: /tmp/direct_v2_T2.pkl, /tmp/direct_v2_B3.txt, /tmp/direct_v2_meta.json (written by direct_finish_v2.py).
  1. share of the model's within-race score variation by input group (per-input contributions, demeaned inside each race)
  2. within-race correlation of each raw input with Proj and with the direct score (what each one leans on)
  3. runners the direct model likes much more than Proj (direct top 3, Proj rank 6+) and the reverse: contributions by group and how they actually ran
Run: python research/direct_vs_proj_drivers.py"""
import json
import numpy as np, pandas as pd, lightgbm as lgb
meta = json.load(open('/tmp/direct_v2_meta.json')); feats = meta['feats']
d = pd.read_pickle('/tmp/direct_v2_T2.pkl')
d['proj'] = pd.to_numeric(d.proj, errors='coerce'); d['price'] = pd.to_numeric(d.price, errors='coerce')
ok = d.groupby('race_id').proj.transform(lambda s: s.notna().all())
d = d[ok].reset_index(drop=True)
print('races', d.race_id.nunique(), 'runners', len(d))
b = lgb.Booster(model_file='/tmp/direct_v2_B3.txt')
C = pd.DataFrame(b.predict(d[feats], pred_contrib=True)[:, :-1], columns=feats)
G = {
 'last run rating (w1, rank/gap vs field)': ['w1', 'r_w1', 'k_w1'],
 'earlier ratings (w2-w6)': ['w2', 'w3', 'w4', 'w5', 'w6'],
 'longer averages and peak (m3, m8, max8, gaps)': ['m3_wpr', 'm8_wpr', 'max8_wpr', 'r_m3_wpr', 'r_m8_wpr', 'r_max8_wpr', 'k_m3_wpr', 'k_m8_wpr', 'k_max8_wpr', 'gap_top_m3', 'gap_top_m8', 's8_wpr'],
 'trend': ['trend'],
 'last-run result (margin, finish, win/place share)': ['p1_mfin', 'm4_mfin', 'p1_finpct', 'm4_finpct', 'win8', 'plc8', 'r_m4_mfin', 'k_m4_mfin', 'r_m4_finpct', 'k_m4_finpct', 'r_win8', 'k_win8', 'r_plc8', 'k_plc8'],
 'jockey and trainer': ['jw', 'jw90', 'tw', 'tw90', 'jock_chg', 'r_jw', 'k_jw', 'r_jw90', 'k_jw90', 'r_tw', 'k_tw', 'r_tw90', 'k_tw90'],
 'freshness and experience': ['days', 'n_runs', 'r_days', 'k_days', 'wchg', 'dchg'],
 'weight, barrier, distance, going, class': ['weightCarried', 'barfrac', 'nr', 'distance', 'gs', 'cls', 'cls_same', 'r_weightCarried', 'k_weightCarried', 'r_barfrac', 'k_barfrac'],
 'age and sex': ['horse_age', 'sex', 'r_horse_age', 'k_horse_age'],
}
used = {c for v in G.values() for c in v}
G['other'] = [c for c in feats if c not in used]
rk = d.race_id
Cd = C - C.groupby(rk.values).transform('mean')           # within-race demeaned contributions
grp = pd.DataFrame({k: Cd[[c for c in v if c in feats]].sum(axis=1) for k, v in G.items()})
tot = Cd.sum(axis=1)
print('\n1. share of within-race score variation by input group (variance of the group score / variance of the total; groups overlap so shares do not sum to 100%)')
for k in grp:
    print(f'   {k:52s} sd {grp[k].std():.3f}   share of total variance {grp[k].var() / tot.var():.0%}   corr with the total {np.corrcoef(grp[k], tot)[0, 1]:+.2f}')
dm = lambda s: s - s.groupby(rk.values).transform('mean')
print('\n2. within-race correlation of raw inputs with Proj and with the direct score')
dsc = np.log(d.p_B3.clip(1e-9))
rows = []
for c in ['w1', 'w2', 'm3_wpr', 'm8_wpr', 'max8_wpr', 'trend', 'p1_mfin', 'p1_finpct', 'win8', 'plc8', 'days', 'n_runs', 'weightCarried', 'barfrac', 'horse_age', 'jw', 'tw', 'jock_chg', 'nett']:
    x = pd.to_numeric(d[c], errors='coerce')
    m = x.notna()
    rows.append((c, np.corrcoef(dm(x)[m], dm(d.proj)[m])[0, 1], np.corrcoef(dm(x)[m], dm(dsc)[m])[0, 1]))
print('   input            with Proj   with direct   (direct minus Proj)')
for c, a, bb in sorted(rows, key=lambda t: -(abs(t[2]) - abs(t[1]))):
    print(f'   {c:15s} {a:+8.2f} {bb:+11.2f} {bb - a:+14.2f}')
print('   Proj vs direct score, within-race correlation:', round(np.corrcoef(dm(d.proj), dm(dsc))[0, 1], 2))
# 3. disagreements
d['rd'] = d.groupby('race_id').p_B3.rank(ascending=False, method='first'); d['rp'] = d.groupby('race_id').proj.rank(ascending=False, method='first')
d['mk'] = (1 / d.price) / (1 / d.price).groupby(rk.values).transform('sum')
print('\n3. disagreements')
for lab, m in (('direct likes (direct top 3, Proj rank 6+)', (d.rd <= 3) & (d.rp >= 6)), ('Proj likes (Proj top 3, direct rank 6+)', (d.rp <= 3) & (d.rd >= 6))):
    x = d[m]
    print(f'\n   {lab}: {len(x)} runners in {x.race_id.nunique()} races; won {x.win.mean():.1%}; direct predicted {x.p_B3.mean():.1%}; market-implied {x.mk.mean():.1%}; avg price ${x.price.mean():.2f}; placed {x.top3.mean():.1%}; flat ROI {(x.win * x.price - 1).mean():+.1%}')
    g2 = grp[m].mean()
    print('      mean within-race contribution by group (+ pushes the horse up):', {k[:22]: round(v, 2) for k, v in g2.sort_values(ascending=False).items()})
