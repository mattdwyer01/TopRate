"""Read-only: does blending model prob with market prob (conditional logit) give profitable bets?
Fit on first half of dates, bet on second half. Also price-band restriction. Checks: halves, excl top3 winners."""
import sys; sys.path.insert(0,'.')
import numpy as np, pandas as pd, runners_io
from scipy.optimize import minimize
BETA=0.20
r=runners_io.read_runners().drop_duplicates('run_id') if 'run_id' in runners_io.read_runners().columns else runners_io.read_runners()
log=pd.read_csv('wpr_projection_log.csv.gz')
log=log.sort_values('made').drop_duplicates('run_id',keep='first')  # first logged = pre-race
r['date']=pd.to_datetime(r['date'])
r=r[(r.date<='2026-10-07')&(r.resulted==1)&(r.scratched.fillna(0)!=1)]
d=r[['run_id','race_id','date','starting_price_sp','won']].merge(log[['run_id','proj','wtadj']],on='run_id')
d['rating']=d.proj+d.wtadj.fillna(0)
d=d[(d.starting_price_sp>1)&d.rating.notna()]
g=d.groupby('race_id')
d=d[g.won.transform('sum').eq(1)&g.run_id.transform('count').ge(4)].copy()
d['lm']=BETA*d.rating
d['lk']=-np.log(d.starting_price_sp)
for c in('lm','lk'):
    d[c]=d[c]-d.groupby('race_id')[c].transform('max')
dates=sorted(d.date.unique());cut=dates[len(dates)//2]
print('races',d.race_id.nunique(),'dates',len(dates),'split',str(cut)[:10])
def nll(w,x):
    s=w[0]*x.lm+w[1]*x.lk
    lse=np.log(np.exp(s).groupby(x.race_id).transform('sum'))
    return -((s-lse)*x.won).sum()
tr=d[d.date<cut]; te=d[d.date>=cut].copy()
w=minimize(nll,[1,1],args=(tr,),method='Nelder-Mead').x
print('fit weights model(beta-scaled)=%.3f market=%.3f'%tuple(w), '| market-only nll %.1f blend %.1f (test)'%(nll([0,1],te),nll(w,te)))
te['s']=w[0]*te.lm+w[1]*te.lk
te['p']=np.exp(te.s)/np.exp(te.s).groupby(te.race_id).transform('sum')
te['edge']=te.p*te.starting_price_sp-1
te['pm']=np.exp(te.lk)/np.exp(te.lk).groupby(te.race_id).transform('sum')
def rep(name,b):
    if len(b)<30: print(f'{name}: n={len(b)} (too few)');return
    ret=np.where(b.won==1,b.starting_price_sp-1,-1)
    b=b.assign(ret=ret).sort_values('date')
    h=len(b)//2
    ex=b.drop(b[b.won==1].nlargest(3,'starting_price_sp').index)
    print(f'{name}: n={len(b)} win={b.won.mean()*100:.1f}% ROI={ret.mean()*100:+.1f}% | halves {b.ret.iloc[:h].mean()*100:+.1f}/{b.ret.iloc[h:].mean()*100:+.1f} | ex-top3 {ex.ret.mean()*100:+.1f}%')
print('--- (1) blend edge thresholds, all prices'); 
for t in(0,.05,.10,.15,.20): rep(f'edge>{t:.2f}',te[te.edge>t])
print('--- (3) price bands with edge>0.05')
for lo,hi in((1,3),(1,5),(2,6),(3,8),(5,12),(8,30)):
    rep(f'${lo}-{hi}',te[(te.edge>.05)&te.starting_price_sp.between(lo,hi)])
print('--- (3) inside model gap line 4, blend edge>0')
top=te.groupby('race_id').rating.transform('max')
for lo,hi in((1,6),(2,8),(1,99)):
    rep(f'gap<=4 ${lo}-{hi}',te[(top-te.rating<=4)&(te.edge>0)&te.starting_price_sp.between(lo,hi)])
print('--- baselines: all test runners',end=' ');rep('all',te)
