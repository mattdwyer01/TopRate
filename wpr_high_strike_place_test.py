"""Read-only: highest strike-rate plays (win and place), break-even place prices, estimated place ROI, and place multis.
Part A: 1 Jul to 7 Oct window (log projections, SM = demeaned suitability). Place = paid places (8+ runners 3, 5-7 runners 2, under 5 none).
Part B: real TAB place dividends (tab_dividends.csv, 2 to 8 Oct only) for the same plays, and a place-dividend vs win-price calibration.
Part C: place doubles/trebles of the best plays (empirical hit rate of consecutive same-day legs, and the combined dividend needed to break even)."""
import sys; sys.path.insert(0,'.')
import numpy as np, pandas as pd, runners_io
log=pd.read_csv('wpr_projection_log.csv.gz').sort_values('made').drop_duplicates('run_id')
r=runners_io.read_runners(); r['date']=r['date'].astype(str)
cols=['run_id','race_id','date','starting_price_sp','fixed_win_price','won','finish_position','scratched','resulted']
if 'start_time' in r.columns: cols.append('start_time')
r=r[(r.resulted==1)&(r.date<='2026-10-07')&(r.scratched.fillna(0)!=1)][cols]
d=r.merge(log[['run_id','proj','wtadj','adj','nruns']],on='run_id'); d=d[d.proj.notna()]
g=d.groupby('race_id'); d=d[g.won.transform('sum').eq(1)&g.run_id.transform('count').ge(5)].copy()
d['price']=d.starting_price_sp.fillna(d.fixed_win_price); d=d[d.price.notna()&(d.price>1)]
d['rating']=d.proj+d.wtadj.fillna(0); G=d.groupby('race_id')
d['gap']=G.rating.transform('max')-d.rating
d['rank']=G.rating.rank(ascending=False,method='min')
second=G.rating.transform(lambda s:s.nlargest(2).iloc[-1]); d['lead']=G.rating.transform('max')-second
d['sm']=d.adj-G.adj.transform('mean'); d['field']=G.run_id.transform('count'); d['mrank']=G.price.rank(method='min')
d['places']=np.where(d.field>=8,3,np.where(d.field>=5,2,0))
d['win']=d.won==1; d['plc']=(d.finish_position<=d.places)&(d.places>0); d['ret']=np.where(d.win,d.price-1,-1)
M=d[d.rating.notna()].copy()
def row(name,x):
    if len(x)<40: print(f'{name:44} n={len(x)} (few)'); return
    w,p=x.win.mean(),x.plc.mean()
    print(f'{name:44} n={len(x):5} win={w*100:5.1f}% place={p*100:5.1f}% avg${x.price.mean():5.2f} winROI={x.ret.mean()*100:+6.1f}% | place break-even dividend ${1/p:4.2f} (per $1 = +{(1/p-1)*100:3.0f}%)')
print('races',M.race_id.nunique(),'| ALL runners:'); row('all runners',M)
print('\n== A. Highest strike-rate plays')
for lab,f in [('model #1',M['rank']==1),('#1, lead over 2nd >= 2',(M['rank']==1)&(M.lead>=2)),('#1, lead >= 4',(M['rank']==1)&(M.lead>=4)),('#1, lead >= 6',(M['rank']==1)&(M.lead>=6)),
  ('#1 and SM >= +0.5',(M['rank']==1)&(M.sm>=.5)),('#1, lead >= 2 and SM >= +0.5',(M['rank']==1)&(M.lead>=2)&(M.sm>=.5)),('#1, lead >= 4 and SM >= +0.5',(M['rank']==1)&(M.lead>=4)&(M.sm>=.5)),
  ('#1 and market favourite',(M['rank']==1)&(M.mrank==1)),('#1 and fav, SM >= +0.5',(M['rank']==1)&(M.mrank==1)&(M.sm>=.5)),('#1 and fav, lead >= 2',(M['rank']==1)&(M.mrank==1)&(M.lead>=2)),
  ('#1 and fav, lead >= 4',(M['rank']==1)&(M.mrank==1)&(M.lead>=4)),('SM >= +0.5, gap < 2',(M.sm>=.5)&(M.gap<2)),('SM >= +0.5, gap < 2, price under $3',(M.sm>=.5)&(M.gap<2)&(M.price<3)),
  ('SM >= +0.5, gap < 2, field <= 10',(M.sm>=.5)&(M.gap<2)&(M.field<=10)),('gap < 2 (any)',M.gap<2),('gap < 4 and SM >= +0.5',(M.gap<4)&(M.sm>=.5)),('gap < 4, SM >= +0.5, price under $4',(M.gap<4)&(M.sm>=.5)&(M.price<4))]:
    row(lab,M[f])
print('\n== A2. Place-only view: highest PLACE strike rates (paid places only, 8+ runners = 3 places)')
P=M[M.places==3]
for lab,f in [('8+ runners, model #1',P['rank']==1),('8+ runners, rank 1-2',P['rank']<=2),('8+ runners, rank 1-3',P['rank']<=3),('8+ runners, #1 SM >= +0.5',(P['rank']==1)&(P.sm>=.5)),
  ('8+ runners, gap < 2',P.gap<2),('8+ runners, gap < 2, SM >= +0.5',(P.gap<2)&(P.sm>=.5)),('8+ runners, market fav',P.mrank==1),('8+ runners, mkt rank 2-3 and gap < 2',(P.mrank.between(2,3))&(P.gap<2)),
  ('8+ runners, gap < 4, price $3-6',(P.gap<4)&(P.price.between(3,6))),('8+ runners, gap < 4, SM >= +0.5, $3-6',(P.gap<4)&(P.sm>=.5)&P.price.between(3,6))]:
    row(lab,P[f])

# ---------------------------------------------------------------- Part B: real place dividends (2-8 Oct) + calibration
import payload_io
P_=payload_io.load_payload()
div=pd.read_csv('tab_dividends.csv'); div=div[div.status=='Paying']
R={}
for rc in P_['RACES']:
    if rc['date']>='2026-10-02': R[(rc['date'],rc['venue'].lower(),rc['race'])]=rc
def find(date,venue,no):
    v=venue.lower(); c=[v,v.split(' @ ')[0]]
    for (dd,vn,n),rc in R.items():
        if dd==date and n==no and any(x==vn or x in vn or vn in x for x in c): return rc
rows=[]
for (date,venue,no),gp in div.groupby(['date','venue','race_no']):
    rc=find(date,venue,no)
    if not rc: continue
    pl=gp[gp['product']=='Place'].set_index('selections').amount.to_dict()
    rs=[x for x in rc['runners'] if not x.get('scr') and x.get('tab') and x.get('wpjp') is not None]
    if len(rs)<5: continue
    top=max(x['wpjp'] for x in rs); srt=sorted([x['wpjp'] for x in rs],reverse=True)
    for x in rs:
        pr=x.get('sp') or x.get('fx')
        if not pr: continue
        rows.append(dict(date=date,race=rc['race_id'],tab=str(x['tab']),price=pr,rank=sorted(rs,key=lambda z:-z['wpjp']).index(x)+1 if False else None,
                         gap=top-x['wpjp'],lead=srt[0]-srt[1],div=pl.get(str(x['tab']),0.0),field=len(rs),won=x.get('won')==1))
B=pd.DataFrame(rows)
B['rank']=B.groupby('race')['gap'].rank(method='min'); B['mrank']=B.groupby('race').price.rank(method='min')
B['placed']=B['div']>0
print(f'\n== B. Real place dividends 2-8 Oct: {B.race.nunique()} races, {len(B)} runners, {B.placed.sum()} placed')
pp=B[B.placed&(B.price>1)]
bk=pd.cut(pp.price,[1,2,3,4,6,10,20,1000]); print('avg place dividend by win price (placed runners):'); print(pp.groupby(bk,observed=True)['div'].agg(['count','mean','median']).round(2).to_string())
b1,a1=np.polyfit(np.log(pp.price),np.log(pp['div']),1); print(f'fit: place div = exp({a1:.3f}) * price^{b1:.3f}  (corr {np.corrcoef(np.log(pp.price),np.log(pp["div"]))[0,1]:.2f})')
def real(name,x):
    if len(x)<25: print(f'{name:40} n={len(x)} (few)'); return
    ret=x['div']-1; print(f'{name:40} n={len(x):4} win={x.won.mean()*100:4.0f}% place={x.placed.mean()*100:4.0f}% avg place div ${x.loc[x.placed,"div"].mean():.2f} REAL place ROI={ret.mean()*100:+5.1f}%')
real('model #1',B[B['rank']==1]); real('#1, lead >= 2',B[(B['rank']==1)&(B.lead>=2)]); real('#1, lead >= 4',B[(B['rank']==1)&(B.lead>=4)])
real('#1 and fav',B[(B['rank']==1)&(B.mrank==1)]); real('market favourite',B[B.mrank==1]); real('gap < 2, price under $3',B[(B.gap<2)&(B.price<3)]); real('rank 2-3 (any price)',B[B['rank'].between(2,3)])

# ---------------------------------------------------------------- estimated place ROI over the whole window using the fitted dividend curve
M['pdiv']=np.exp(a1)*M.price**b1
def est(name,x):
    if len(x)<40: return
    gain=((x.plc*x.pdiv)).mean()-1
    print(f'{name:44} n={len(x):5} place={x.plc.mean()*100:5.1f}%  est avg div ${x.loc[x.plc,"pdiv"].mean():.2f}  EST place ROI={gain*100:+5.1f}%')
print('\n== B2. Estimated place ROI over the full window (dividend curve fitted on the 7 days above, so indicative only)')
S=M[M.places>0]
plays={'model #1':S['rank']==1,'#1, lead >= 2':(S['rank']==1)&(S.lead>=2),'#1, lead >= 4':(S['rank']==1)&(S.lead>=4),'#1 and fav, lead >= 2':(S['rank']==1)&(S.mrank==1)&(S.lead>=2),
       'SM >= +0.5, gap < 2, price under $3':(S.sm>=.5)&(S.gap<2)&(S.price<3),'market favourite':S.mrank==1,'gap < 4, SM >= +0.5, $5+':(S.gap<4)&(S.sm>=.5)&(S.price>5)}
for k,f in plays.items(): est(k,S[f])

# ---------------------------------------------------------------- Part C: place multis (consecutive same-day legs, non-overlapping)
print('\n== C. Place multis of the best plays (legs = consecutive qualifying selections on the same day, one per race)')
S2=S.copy(); S2['t']=S2.get('start_time',S2.race_id).astype(str) if 'start_time' in S2.columns else S2.race_id.astype(str)
def multis(name,f,legs):
    x=S2[f].sort_values(['date','t']).drop_duplicates('race_id')
    prods=[];hits=[]
    for dt,gp in x.groupby('date'):
        v=gp.to_dict('records')
        for i in range(0,len(v)-legs+1,legs):
            seg=v[i:i+legs]; ok=all(s['plc'] for s in seg); hits.append(ok); prods.append(np.prod([s['pdiv'] for s in seg]) if ok else 0)
    if len(hits)<40: return
    h=np.mean(hits); roi=np.mean(prods)-1
    single=x.plc.mean()
    print(f'  {name:36} {legs}-leg: n={len(hits):4} hit={h*100:5.1f}% (single {single*100:4.1f}%^{legs}={single**legs*100:4.1f}%)  est avg return/hit ${np.mean([p for p in prods if p>0]) if any(p>0 for p in prods) else 0:6.2f}  EST ROI={roi*100:+5.1f}%  break-even return ${1/max(h,1e-9):6.2f}')
for k in ['model #1','#1, lead >= 2','#1, lead >= 4','#1 and fav, lead >= 2','SM >= +0.5, gap < 2, price under $3']:
    for L in (2,3): multis(k,plays[k].reindex(S2.index,fill_value=False),L)
