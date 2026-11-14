"""Volume v2 with 'points off the top' on the dashboard's blended Rating vs the plain Proj, same races, same rules.
Blend (raceModel.ts, DIRECT_SHARE 0.5): rating = race mean Proj + 0.5 x (Proj - mean) + 0.5 x 5 x (ln dm - mean ln dm), only in races where every
rated runner has a direct score; otherwise the Proj alone (as the dashboard does). Run from a checkout of main."""
import glob, gzip, json, os, sys
import numpy as np, pandas as pd
sys.path.insert(0, os.getcwd())
import volume_rules as V
import betfair_prices as bf

D0, D1 = sys.argv[1], sys.argv[2]
gaps = {}
for f in sorted(glob.glob('data/trip_map_archive/*.json.gz')):
    t = json.load(gzip.open(f))
    for v in t.get('races', {}).values():
        for r in v.get('runners', []):
            if r.get('gap') is not None:
                gaps[str(r['rid'])] = float(r['gap'])
g2, _ = V.read_gaps('trip_map.json')
for k, v in g2.items():
    gaps.setdefault(k, v)

rn = V.read_runners()
for c in ('state', 'won', 'starting_price_sp', 'horse'):
    pass
full = pd.read_csv(V.RUNNERS, low_memory=False, usecols=lambda c: c in set(V.RUNNER_COLS) | {'state', 'won', 'finish_position'})
full = full[(full.date >= D0) & (full.date <= D1)]
dm = {}
for f in sorted(glob.glob('data/direct_scores/*.json')):
    d = os.path.basename(f)[:10]
    if D0 <= d <= D1:
        for rid, m in json.load(open(f)).get('races', {}).items():
            for tab, p in m.items():
                dm[(str(rid), str(tab))] = p
full['rid_s'] = full.race_id.astype('Int64').astype(str)
full['tab_s'] = pd.to_numeric(full.tab_number, errors='coerce').astype('Int64').astype(str)
full['dm'] = [dm.get(k) for k in zip(full.rid_s, full.tab_s)]

def blend(df):
    df = df.copy()
    p = pd.to_numeric(df.wprp_proj, errors='coerce')
    live = pd.to_numeric(df.scratched, errors='coerce').fillna(0) != 1
    rated = live & p.notna() & ~df.wprp_model.isin(['debut'])
    out = p.copy()
    nbl = 0
    for rid, idx in df[rated].groupby('race_id').groups.items():
        sub = df.loc[idx]
        d = pd.to_numeric(sub.dm, errors='coerce')
        if d.isna().any() or (d <= 0).any():
            continue
        pp = p.loc[idx]; m = pp.mean(); ld = np.log(d)
        out.loc[idx] = m + 0.5 * (pp - m) + 0.5 * 5 * (ld - ld.mean())
        nbl += 1
    df['wprp_proj'] = out
    return df, nbl

ov = V.read_overrides()
res = {}
bl, nbl = blend(full)
for name, df in (('proj', full), ('blend', bl)):
    d, rc = V.evaluate(df, gaps, 'fixed', ov)
    w = pd.to_numeric(d['won'], errors='coerce')
    done = d.assign(w=w).groupby('race_id')['w'].agg(['count', 'sum', 'size'])
    done = done[(done['count'] == done['size']) & (done['sum'] == 1)].index
    d = d[d.race_id.isin(done)]
    res[name] = d
look = bf.lookup(full.date.unique())

def summ(d, label):
    s = d[d.v2].copy()
    if s.empty:
        print(label, 'no bets'); return
    st = s.stake_v2
    won = pd.to_numeric(s.won, errors='coerce') == 1
    s['bsp'] = [look.get((dt, bf.norm(h))) for dt, h in zip(s.date, s.horse)]
    s['comm'] = s.state.map(bf.commission)
    fx = np.where(won, st * s.price, 0)
    bsp_ok = s.bsp.notna()
    bfr = np.where(won, st * ((s.bsp.fillna(s.price) - 1) * (1 - s.comm) + 1), 0)
    s['ret_bf'] = bfr; s['ret_fx'] = fx
    def roi(r, stake): return 100 * (r.sum() / stake.sum() - 1)
    o = s.sort_values('ret_bf', ascending=False)
    def ex(n):
        k = o.iloc[n:]; return roi(k.ret_bf, k.stake_v2)
    days = sorted(s.date.unique()); h = days[len(days) // 2]
    a, b = s[s.date < h], s[s.date >= h]
    print(f"{label}: races {s.race_id.nunique()}, bets {len(s)}, wins {int(won.sum())}, staked ${st.sum():.0f}, "
          f"ROI fixed {roi(s.ret_fx, st):+.1f}%, Betfair {roi(s.ret_bf, st):+.1f}% (BSP found {bsp_ok.mean()*100:.0f}%), "
          f"ex3 {ex(3):+.1f}%, ex10 {ex(10):+.1f}%, halves {roi(a.ret_bf, a.stake_v2):+.1f}% / {roi(b.ret_bf, b.stake_v2):+.1f}% (split {h})")
    return s

print(f"{D0} to {D1}: {full.race_id.nunique()} races, {nbl} with a direct score for every rated runner, "
      f"resulted {res['proj'].race_id.nunique()}")
for lo in (D0, '2026-11-05', '2026-11-11'):
    if lo < D0: continue
    print(f"--- from {lo}")
    sp = summ(res['proj'][res['proj'].date >= lo], 'Plain Proj ')
    sb = summ(res['blend'][res['blend'].date >= lo], 'Blended Rating')
p = res['proj'][res['proj'].v2][['date', 'venue', 'race', 'horse', 'price', 'won', 'off']]
b = res['blend'][res['blend'].v2][['date', 'venue', 'race', 'horse', 'price', 'won', 'off']]
k = ['date', 'venue', 'race', 'horse']
m = p.merge(b, on=k, how='outer', suffixes=('_p', '_b'), indicator=True)
ch = m[m._merge != 'both'].sort_values(k)
print(f"\nbets in only one version: {len(ch)} (plain only {int((ch._merge=='left_only').sum())}, blend only {int((ch._merge=='right_only').sum())})")
for _, r in ch.iterrows():
    side = 'plain only' if r._merge == 'left_only' else 'blend only'
    pr = r.price_p if r._merge == 'left_only' else r.price_b
    w = r.won_p if r._merge == 'left_only' else r.won_b
    print(f"  {r.date} {r.venue} R{int(r.race)} {r.horse} ${pr} {'WON' if w == 1 else ''} [{side}] off {r.off_p if pd.notna(r.off_p) else '-'} vs {round(r.off_b,2) if pd.notna(r.off_b) else '-'}")
