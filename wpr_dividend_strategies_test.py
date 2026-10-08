"""Read-only: model-ranking strategies paid at REAL TAB dividends (tab_dividends.csv, 2-8 Oct 2026 only).
Win/place on #1, quinella/exacta/trifecta/first-four boxes and keyed, quaddie legs inside gap line. $1 unit stakes.
Per-race dividends are per $1. Tiny sample: reported with n and with the biggest payout removed."""
import sys; sys.path.insert(0,'.')
import itertools, math, numpy as np, pandas as pd, payload_io
P=payload_io.load_payload()
div=pd.read_csv('tab_dividends.csv'); div=div[div.status=='Paying']
def norm(v): return v.split('@')[-1].strip().lower() if '@' in v else v.lower()
R={}
for r in P['RACES']:
    if r['date']<'2026-10-02': continue
    R[(r['date'],r['venue'].lower(),r['race'])]=r
def find(date,venue,no):
    v=venue.lower(); cands=[v,norm(venue),v.split(' @ ')[0]]
    for (d,vn,n),r in R.items():
        if d==date and n==no and any(c==vn or c in vn or vn in c for c in cands): return r
races=[]
for (date,venue,no),g in div.groupby(['date','venue','race_no']):
    r=find(date,venue,no)
    if not r: continue
    rs=[x for x in r['runners'] if not x.get('scr') and x.get('wpjp') is not None and x.get('tab')]
    if len(rs)<5: continue
    rs=sorted(rs,key=lambda x:-x['wpjp'])
    top=rs[0]['wpjp']
    for x in rs: x['gap']=top-x['wpjp']
    pre=all((x.get('wpjmd') or '9')<r['start_time'][:19]+'Z' for x in rs)
    races.append(dict(date=date,venue=venue,no=no,rs=rs,pre=pre,div=g,start=r['start_time']))
print('races with dividends + projections:',len(races),'| pre-race projections:',sum(x['pre'] for x in races))
def D(r,prod,sel=None):
    g=r['div'][r['div']['product']==prod]
    if sel is None: return g
    row=g[g.selections==sel]; return float(row.amount.iloc[0]) if len(row) else 0.0
def bet(name,L):
    # L = list of (stake, ret)
    if len(L)<10: print(f'{name}: n={len(L)} too few');return
    s=np.array([a for a,_ in L]);ret=np.array([b for _,b in L]);net=ret-s
    roi=net.sum()/s.sum()*100; hit=(ret>0).mean()*100
    big=np.argmax(ret); ex=(net.sum()-(ret[big]-s[big])-0)/(s.sum()-s[big])*100 if len(L)>1 else 0
    h=len(L)//2; r1=(net[:h].sum()/s[:h].sum()*100);r2=net[h:].sum()/s[h:].sum()*100
    print(f'{name}: n={len(L)} hit={hit:.0f}% ROI={roi:+.1f}% | halves {r1:+.0f}/{r2:+.0f} | ex-biggest {ex:+.1f}% | avg stake ${s.mean():.1f}')
races.sort(key=lambda r:(r['date'],r['start']))
T=lambda r,k:[str(x['tab']) for x in r['rs'][:k]]
print('\n== Win/Place on model #1 (real totes)')
for gmin in(0,2,4,6):
    W=[];Pl=[]
    for r in races:
        a=r['rs'][0];b=r['rs'][1]
        if a['wpjp']-b['wpjp']<gmin: continue
        t=str(a['tab']);W.append((1,D(r,'Win',t)));Pl.append((1,D(r,'Place',t)))
    bet(f'Win #1, lead>={gmin}',W);bet(f'Place #1, lead>={gmin}',Pl)
print('\n== Exotics: boxed over top-k by model, $1 unit (cost = combos)')
for k in(2,3,4):
    L=[]
    for r in races:
        t=set(T(r,k));pay=0
        g=D(r,'Quinella')
        for _,row in g.iterrows():
            if set(row.selections.split('/'))<=t: pay=row.amount
        L.append((math.comb(k,2),pay))
    bet(f'Quinella box top{k}',L)
for k in(3,4,5):
    L=[]
    for r in races:
        t=T(r,k);g=D(r,'Trifecta');pay=0
        for _,row in g.iterrows():
            if all(s in t for s in row.selections.split('/')): pay=row.amount
        L.append((k*(k-1)*(k-2),pay)) if False else L.append((math.perm(k,3),pay/6*6 if False else pay))
    bet(f'Trifecta box top{k} ($1/combo)',L)
for k in(4,5,6):
    L=[]
    for r in races:
        t=T(r,k);g=D(r,'FirstFour');pay=0
        for _,row in g.iterrows():
            if all(s in t for s in row.selections.split('/')): pay=row.amount
        L.append((math.perm(k,4),pay))
    bet(f'FirstFour box top{k}',L)
print('\n== Keyed (banker): #1 first, others from top-m')
for m in(4,5,6):
    L=[]
    for r in races:
        t=T(r,m);g=D(r,'Trifecta');pay=0;key=t[0]
        for _,row in g.iterrows():
            s=row.selections.split('/')
            if s[0]==key and all(x in t for x in s): pay=row.amount
        L.append(((m-1)*(m-2),pay))
    bet(f'Trifecta #1 first, 2nd/3rd from top{m}',L)
for m in(5,6):
    L=[]
    for r in races:
        t=T(r,m);g=D(r,'FirstFour');pay=0;key=t[0]
        for _,row in g.iterrows():
            s=row.selections.split('/')
            if s[0]==key and all(x in t for x in s): pay=row.amount
        L.append(((m-1)*(m-2)*(m-3),pay))
    bet(f'FirstFour #1 first, rest from top{m}',L)
print('\n== Quaddie (late = last 4 races of meeting; selections inside a gap line each leg)')
byv={}
for r in races: byv.setdefault((r['date'],r['venue']),[]).append(r)
for line in(2,3,4,6):
    L=[]
    for (d,v),rs in byv.items():
        rs=sorted(rs,key=lambda r:r['no'])
        nums=[r['no'] for r in rs]
        if len(rs)<4 or nums[-4:]!=list(range(nums[-1]-3,nums[-1]+1)): continue
        legs=rs[-4:];g=legs[-1]['div'];g=g[g['product']=='Quaddie']
        if g.empty: continue
        cost=1;ok=True;sel=[]
        for lg in legs:
            s=[str(x['tab']) for x in lg['rs'] if x['gap']<=line];cost*=len(s);sel.append(s)
        w=g.selections.iloc[0].split('/')
        pay=g.amount.iloc[0] if all(w[i] in sel[i] for i in range(4)) else 0
        L.append((cost,pay))
    bet(f'Late quaddie, inside {line}',L)
