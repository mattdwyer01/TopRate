import json, gzip, pandas as pd, numpy as np
D = pd.read_pickle('flem2.pkl'); D['h'] = D.horse.str.lower()
W = D[(D.fin == 1)].copy(); W['beat'] = W.atw - W.proj
W['Prank'] = [D[(D.date == a) & (D.race == b)].proj.rank(ascending=False).get(i) for a, b, i in zip(W.date, W.race, W.index)]
W['SPrank'] = [D[(D.date == a) & (D.race == b)].sp.rank().get(i) for a, b, i in zip(W.date, W.race, W.index)]
W = W[W.beat >= 4].sort_values('beat', ascending=False)
pages = {d: json.load(gzip.open(f'pg_{d}.json.gz'))['rows'] for d in W.date.unique()}
out = []
for _, w in W.iterrows():
    p = next((v for v in pages[w.date].values() if str(v.get('horse','')).lower() == w.h and 'flemington' in str(v.get('venue','')).lower()), None)
    form = sorted([f for f in (p.get('form') or []) if f['date'] < w.date], key=lambda f: f['date'], reverse=True) if p else []
    runs = [f for f in form if not f.get('isBarrierTrial') and not f.get('isJumpout')]
    trials = [f for f in form if f.get('isBarrierTrial') or f.get('isJumpout')]
    # prep: runs since last gap of 60+ days
    prep = 1
    for a, b in zip(runs, runs[1:]):
        if (pd.Timestamp(a['date']) - pd.Timestamp(b['date'])).days > 60: break
        prep += 1
    last = runs[0] if runs else {}
    print(f"\n=== {w.date} R{w.race} {w.cls} {w.dist}m  {w.horse}  SP ${w.sp}  Proj {w.proj:.1f} (rank {int(w.Prank)}), market rank {int(w.SPrank)}, actual {w.atw:.1f}  beat +{w.beat:.1f}")
    print(f"   prep run {prep + 1 if runs and (pd.Timestamp(w.date) - pd.Timestamp(runs[0]['date'])).days <= 60 else 1} | days since last {(pd.Timestamp(w.date) - pd.Timestamp(last['date'])).days if last else '-'} | weight now {w.wt} vs last {last.get('weightCarried')} | gear changes today {p.get('gear_changes') if p else None}")
    for f in runs[:5]:
        print(f"   {f['date']} {f.get('track','')[:14]:14s} {f.get('distance')}m {str(f.get('going',''))[:7]:7s} {str(f.get('class',''))[:6]:6s} fin {f.get('positionFinish')}/{f.get('starters')} mgn {f.get('marginFinish')} wpr {f.get('wpr')} SP {f.get('priceStarting')} | {(f.get('commentsSteward') or '')[:110]} || {(f.get('commentsVideo') or '')[:110]}")
    for f in trials[:2]:
        print(f"   trial {f['date']} {f.get('track','')} {f.get('distance')}m fin {f.get('positionFinish')}/{f.get('starters')} mgn {f.get('marginFinish')}")
