"""Read-only: out-of-sample check of SM>=+0.5 filters. Candidates are fixed up front (no tuning on the test window).
Train = first 2/3 of dates, test = last 1/3. Flat $1 win ROI at SP (else last fixed price)."""
import sys; sys.path.insert(0,'.')
import numpy as np, pandas as pd, runners_io
log=pd.read_csv('wpr_projection_log.csv.gz').sort_values('made').drop_duplicates('run_id')
r=runners_io.read_runners(); r['date']=r['date'].astype(str)
r=r[(r.resulted==1)&(r.date<='2026-10-07')&(r.scratched.fillna(0)!=1)]
d=r[['run_id','race_id','date','starting_price_sp','fixed_win_price','won','finish_position']].merge(log[['run_id','proj','wtadj','adj','nruns']],on='run_id')
d=d[d.proj.notna()]
g=d.groupby('race_id');d=d[g.won.transform('sum').eq(1)&g.run_id.transform('count').ge(6)].copy()
d['price']=d.starting_price_sp.fillna(d.fixed_win_price);d=d[d.price.notna()&(d.price>1)]
d['rating']=d.proj+d.wtadj.fillna(0);G=d.groupby('race_id')
d['gap']=G.rating.transform('max')-d.rating
d['sm']=d.adj-G.adj.transform('mean')
d['field']=G.run_id.transform('count')
d['fs_race']=G.nruns.transform(lambda s:(s==0).sum())
d['mrank']=G.price.rank(method='min')                       # 1 = market favourite
d['mrank_model']=G.rating.rank(ascending=False,method='min')
d['fav_price']=G.price.transform('min');d['pr_fav']=d.price/d.fav_price
e=np.exp(.2*d.rating);d['fair']=1/(e/e.groupby(d.race_id).transform('sum'))
d['val']=d.price/d.fair                                    # >1 = price longer than model fair
d['sm_rank']=d.groupby('race_id').sm.rank(ascending=False,method='min')   # 1 = best map in race
d['smN']=G.sm.transform(lambda s:(s>=.5).sum())             # number of SM+ runners in race
d['win']=d.won==1;d['ret']=np.where(d.win,d.price-1,-1)
M=d[d.sm.notna()].copy()
dates=sorted(M.date.unique());cut=dates[int(len(dates)*2/3)]
print('races',M.race_id.nunique(),'dates',len(dates),'train <',cut,'test >=',cut)
def stat(x):
    if len(x)<40: return f'n={len(x):4} (few)           '
    ex=x.drop(x[x.win].nlargest(3,'price').index)
    return f'n={len(x):4} win={x.win.mean()*100:4.1f}% ROI={x.ret.mean()*100:+6.1f}% ex3={ex.ret.mean()*100:+6.1f}%'
base=M[M.sm>=.5]
C={
 'SM+ (no filter)':lambda s:s.sm>=.5,
 'SM+ gap<4':lambda s:s.gap<4,
 'SM+ gap<4 $6-15 (earlier)':lambda s:(s.gap<4)&s.price.between(6,15),
 'SM+ gap<4, not mkt fav':lambda s:(s.gap<4)&(s.mrank>1),
 'SM+ gap<4, mkt rank 2-4':lambda s:(s.gap<4)&s.mrank.between(2,4),
 'SM+ gap<6, mkt rank 2-4':lambda s:(s.gap<6)&s.mrank.between(2,4),
 'SM+ gap<4, price<=4x fav':lambda s:(s.gap<4)&(s.pr_fav<=4)&(s.mrank>1),
 'SM+ gap<4, model rank 2-4':lambda s:(s.gap<4)&s.mrank_model.between(2,4),
 'SM+ model rank 2-3, not fav':lambda s:s.mrank_model.between(2,3)&(s.mrank>1),
 'SM+ gap<4, price>=1.15x fair':lambda s:(s.gap<4)&(s.val>=1.15),
 'SM+ gap<4, price>=1.3x fair':lambda s:(s.gap<4)&(s.val>=1.3),
 'SM+ gap<6, price>=1.3x fair':lambda s:(s.gap<6)&(s.val>=1.3),
 'SM+ gap<4, field<=10':lambda s:(s.gap<4)&(s.field<=10),
 'SM+ gap<4, field<=10, not fav':lambda s:(s.gap<4)&(s.field<=10)&(s.mrank>1),
 'SM+ gap<4, best map in race':lambda s:(s.gap<4)&(s.sm_rank==1),
 'SM+ gap<4, only SM+ runner in race':lambda s:(s.gap<4)&(s.smN==1),
 'SM+ gap<4, SM>=1.0':lambda s:(s.gap<4)&(s.sm>=1),
 'SM+ gap<4, no first starters':lambda s:(s.gap<4)&(s.fs_race==0),
 'SM+ gap<4, no 1st starters, not fav':lambda s:(s.gap<4)&(s.fs_race==0)&(s.mrank>1),
}
print(f"{'filter':38} | TRAIN {' '*34} | TEST")
for k,f in C.items():
    x=base[f(base)]
    print(f'{k:38} | {stat(x[x.date<cut])} | {stat(x[x.date>=cut])}')
print('\nreference, all main runners:',stat(M[M.date<cut]),'|',stat(M[M.date>=cut]))
