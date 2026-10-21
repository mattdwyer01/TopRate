"""Spd top 5/6 box where at least k of the pool are priced over $10 (SP): hit rate vs market-implied, estimated and real return. usage: PYTHONPATH=.:research python research/speed_exotics_n10.py R_CACHE.csv (cache written by speed_exotics_select.py)"""
import sys, numpy as np, pandas as pd
sys.path.insert(0,'research'); sys.path.insert(0,'.')
import speed_exotics_select as SEL, speed_exotics_nuggets as N
P=SEL.dividend_pairs(); fit=SEL.fit_div(P)
R=pd.read_csv(sys.argv[1])
R['ed3']=SEL.est_div(R.h3,R.field,fit['Trifecta']); R['ed4']=SEL.est_div(R.h4,R.field,fit['FirstFour'])
R['train']=R.date<'2026-02-01'
rng=np.random.default_rng(1)
def rep(lab,m,hit,ed,cost,ic):
    g=R[m]
    if len(g)<100: return
    ret=(g[hit]*g[ed]).values; roi=ret.sum()/(cost*len(g))-1
    bs=[ret[rng.integers(0,len(g),len(g))].sum()/(cost*len(g))-1 for _ in range(600)]
    a=g[g.train]; b=g[~g.train]
    r1=(a[hit]*a[ed]).sum()/(cost*len(a))-1; r2=(b[hit]*b[ed]).sum()/(cost*len(b))-1
    ratio=g[hit].sum()/g[ic].sum()
    print(f"  {lab:22s} races {len(g):5d} ({len(g)/len(R)*100:4.1f}%) hit {g[hit].mean()*100:5.1f}% vs mkt-implied {g[ic].mean()*100:5.1f}% (x{ratio:.2f}) est ROI {roi*100:+4.0f}% [{np.percentile(bs,5)*100:+.0f},{np.percentile(bs,95)*100:+.0f}] halves {r1*100:+.0f}/{r2*100:+.0f}")
for pool,k in (('s5',3),('s6',3)):
    for kind,ed,ic,cost in (('tri','ed3',f'{pool}_itri',60 if pool=='s5' else 120),('ff','ed4',f'{pool}_iff',120 if pool=='s5' else 360)):
        print(f"== {pool} {kind} (cost ${cost})")
        col=f'{pool}_n10'
        for n in range(0,6):
            rep(f'exactly {n} over $10',R[col]==n,f'{pool}_{kind}',ed,cost,ic)
        for n in (2,3,4):
            rep(f'{n}+ over $10',R[col]>=n,f'{pool}_{kind}',ed,cost,ic)
print("== s5 with over $8 / over $15 thresholds, 3+ (first four, trifecta)")
for col,lab in (('s5_n8','3+ over $8'),('s5_n15','3+ over $15')):
    for kind,ed,ic,cost in (('tri','ed3','s5_itri',60),('ff','ed4','s5_iff',120)):
        rep(lab+' '+kind,R[col]>=3,f's5_{kind}',ed,cost,ic)
# real dividends
import runners_io
r=runners_io.read_runners(); r=r[(r.date.astype(str)>='2026-10-02')&(r.scratched.fillna(0)==0)].copy()
r['v']=r.venue.astype(str).str.upper(); r['spd']=pd.to_numeric(r.spd_fig,errors='coerce')
r['px']=pd.to_numeric(r.starting_price_sp,errors='coerce').fillna(pd.to_numeric(r.fixed_win_price,errors='coerce'))
dv=pd.read_csv('tab_dividends.csv'); dv=dv[dv['product'].isin(['Trifecta','FirstFour'])&(dv.status=='Paying')].drop_duplicates(['date','venue','race_no','product'])
rows=[]
for (dt,ven,rn),g in r.groupby([r.date.astype(str),'v','race']):
    sub=dv[(dv.date==dt)&(dv.venue.str.split(' @ ').str[0]==ven)&(dv.race_no==rn)]
    t=sub[sub['product']=='Trifecta']; f=sub[sub['product']=='FirstFour']
    if t.empty or f.empty or g.spd.notna().sum()<5 or g.tab_number.isna().any() or g.px.isna().any(): continue
    g=g.sort_values('spd',ascending=False,na_position='last')
    t3={int(x) for x in str(t.iloc[0].selections).split('/')}; f4={int(x) for x in str(f.iloc[0].selections).split('/')}
    for n,name in ((5,'s5'),(6,'s6')):
        top=g.head(n); rows.append(dict(pool=name,n10=int((top.px>10).sum()),tri=int(t3<=set(top.tab_number.astype(int))),ff=int(f4<=set(top.tab_number.astype(int))),tdiv=t.iloc[0].amount,fdiv=f.iloc[0].amount,n=n))
X=pd.DataFrame(rows)
print("\nREAL TAB dividends, 2 to 21 Oct 2026 (prices = SP else last fixed)")
for pool,cost in (('s5',(60,120)),('s6',(120,360))):
    for lab,m in (('all',X.n10>=0),('3+ over $10',X.n10>=3),('2 or fewer',X.n10<=2)):
        g=X[(X.pool==pool)&m]
        for kind,div,c in (('tri','tdiv',cost[0]),('ff','fdiv',cost[1])):
            ret=g[kind]*g[div]; ex=ret.copy()
            if g[kind].sum()>=3: ex.loc[ret.sort_values(ascending=False).index[:3]]=0
            print(f"  {pool} {kind} {lab:12s}: races {len(g):3d} hits {int(g[kind].sum()):3d} return {(ret.sum()/(c*len(g))-1)*100:+4.0f}% (ex top3 {(ex.sum()/(c*len(g))-1)*100:+4.0f}%)")
