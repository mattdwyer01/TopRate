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

print(f"{'filter (SM>=+0.5, gap<4)':34} | TRAIN {' '*34}| TEST {' '*34}| ALL")
G4=base[base.gap<4]
for lab,f in [('any price',G4.price>0),('over $3',G4.price>3),('over $4',G4.price>4),('over $5',G4.price>5),('$3-6',G4.price.between(3,6)),('$3-10',G4.price.between(3,10)),('$3-20',G4.price.between(3,20)),('over $3, not fav',(G4.price>3)&(G4.mrank>1)),('over $3, >=1.15x fair',(G4.price>3)&(G4.val>=1.15))]:
    x=G4[f]
    print(f'{lab:34} | {stat(x[x.date<cut])} | {stat(x[x.date>=cut])} | {stat(x)}')
x=G4[G4.price>3].sort_values('date');print('\nmonthly, over $3:')
x['m']=x.date.str[:7];print(x.groupby('m').apply(lambda g:pd.Series(dict(n=len(g),win=g.win.mean()*100,roi=g.ret.mean()*100))).round(1))
