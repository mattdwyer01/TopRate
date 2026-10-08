"""Read-only: re-tests the fixed rules on ~15 months of out-of-sample main-model projections (see wpr_oos_2025_backtest_build.py).
usage: python wpr_oos_2025_backtest_analysis.py oos_main.csv.gz"""
import sys, numpy as np, pandas as pd
d=pd.read_csv(sys.argv[1]); d['date']=d.date.astype(str)
d['nmain']=d.groupby('race_id').horse_id.transform('size')
d['price']=d.priceStarting.where(d.priceStarting>1)
d['rating']=d.p0-0.4*d.wt_rel.fillna(0)            # WT_K = 0.4 weight term, as in production
d['fin']=pd.to_numeric(d.positionFinish,errors='coerce'); d['win']=d.fin==1
print('main-model runners',len(d),'races',d.race_id.nunique(),'dates',d.date.nunique(),d.date.min(),'to',d.date.max())
def prep(x,tag):
    g=x.groupby('race_id'); x=x[g.price.transform(lambda s:s.notna().all())&g.win.transform('sum').eq(1)&(g.price.transform('size')>=5)].copy()
    G=x.groupby('race_id'); x['gap']=G.rating.transform('max')-x.rating; x['rank']=G.rating.rank(ascending=False,method='min')
    x['lead']=G.rating.transform('max')-G.rating.transform(lambda s:s.nlargest(2).iloc[-1]); x['mrank']=G.price.rank(method='min')
    x['sm']=x.adj-G.adj.transform('mean'); x['field']=x.field_size
    x['places']=np.where(x.field>=8,3,np.where(x.field>=5,2,0)); x['plc']=(x.fin<=x.places)&(x.places>0)
    x['ret']=np.where(x.win,x.price-1,-1); print(f'[{tag}] races {x.race_id.nunique()} runners {len(x)}'); return x
full=prep(d[d.nmain>=d.n_rated_in_race],'complete races (every rated runner is main-model)')
part=prep(d,'all races, main-model runners only (light-history runners absent)')
def st(x):
    if len(x)<40: return f'n={len(x):5} (few)'
    x=x.sort_values('date');h=len(x)//2;ex=x.drop(x[x.win].nlargest(3,'price').index)
    return f'n={len(x):5} win={x.win.mean()*100:4.1f}% plc={x.plc.mean()*100:3.0f}% ${x.price.mean():5.2f} ROI={x.ret.mean()*100:+6.1f}% halves {x.ret.iloc[:h].mean()*100:+4.0f}/{x.ret.iloc[h:].mean()*100:+4.0f} ex3 {ex.ret.mean()*100:+6.1f}%'
def plays(M):
    return {'all runners':M.price>0,'#1':M['rank']==1,'#1 lead>=2':(M['rank']==1)&(M.lead>=2),'#1 lead>=4':(M['rank']==1)&(M.lead>=4),'#1 lead>=6':(M['rank']==1)&(M.lead>=6),
      '#1 + fav':(M['rank']==1)&(M.mrank==1),'#1 + fav lead>=2':(M['rank']==1)&(M.mrank==1)&(M.lead>=2),'#1 + fav lead>=4':(M['rank']==1)&(M.mrank==1)&(M.lead>=4),
      'gap<2, under $3':(M.gap<2)&(M.price<3),'SM+0.5 gap<4':(M.sm>=.5)&(M.gap<4),'SM+0.5 gap<4 over $3':(M.sm>=.5)&(M.gap<4)&(M.price>3),'SM+0.5 gap<4 over $5':(M.sm>=.5)&(M.gap<4)&(M.price>5),
      'SM+0.5 gap<6 over $5':(M.sm>=.5)&(M.gap<6)&(M.price>5),'SM+0.5 gap<4 over $6':(M.sm>=.5)&(M.gap<4)&(M.price>6)}
for tag,M in (('COMPLETE RACES',full),('ALL RACES (main runners only)',part)):
    print('\n=====',tag,'=====\n(no SM) vs (+SM>=0.5) for the strike-rate plays')
    for k,f in plays(M).items():
        print(f'{k:24} {st(M[f])}')
        if k in('#1','#1 lead>=2','#1 lead>=4','#1 lead>=6','#1 + fav','#1 + fav lead>=2','#1 + fav lead>=4','gap<2, under $3'): print(f'{"  + SM>=+0.5":24} {st(M[f&(M.sm>=.5)])}')
    print('\nquarterly ROI, key rules:')
    M=M.copy(); M['q']=pd.to_datetime(M.date).dt.to_period('Q').astype(str)
    for k in ['#1 lead>=4','#1 + fav lead>=4','SM+0.5 gap<4 over $5','SM+0.5 gap<6 over $5']:
        x=M[plays(M)[k]]; print(f'  {k:24}', ' | '.join(f'{q}: n={len(g)} {g.ret.mean()*100:+5.1f}%' for q,g in x.groupby('q')))
