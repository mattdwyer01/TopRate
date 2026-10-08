"""Read-only: runners with SM Adj (demeaned suitability) >= +0.5, sliced by gap from top rated, first starters in race,
price, field size. Log 'adj' (main model only) demeaned over the race's non-scratched runners that have a value.
Window 1 Jul to 7 Oct 2026 (log 'oof'/live projections). Flat $1 win ROI at SP (else last fixed price)."""
import sys; sys.path.insert(0,'.')
import numpy as np, pandas as pd, runners_io
log=pd.read_csv('wpr_projection_log.csv.gz').sort_values('made').drop_duplicates('run_id')
r=runners_io.read_runners(); r['date']=r['date'].astype(str)
r=r[(r.resulted==1)&(r.date<='2026-10-07')&(r.scratched.fillna(0)!=1)]
d=r[['run_id','race_id','date','starting_price_sp','fixed_win_price','won','finish_position']].merge(log[['run_id','proj','wtadj','adj','model','nruns']],on='run_id')
d=d[d.proj.notna()]
g=d.groupby('race_id')
d=d[g.won.transform('sum').eq(1)&g.run_id.transform('count').ge(6)].copy()
d['rating']=d.proj+d.wtadj.fillna(0)
d['gap']=d.groupby('race_id').rating.transform('max')-d.rating
d['sm']=d.adj-d.groupby('race_id').adj.transform('mean')
d['fs_race']=d.groupby('race_id').nruns.transform(lambda s:(s==0).sum())
d['field']=d.groupby('race_id').run_id.transform('count')
d['price']=d.starting_price_sp.fillna(d.fixed_win_price)
d=d[d.price.notna()&(d.price>1)]
d['win']=(d.won==1);d['ret']=np.where(d.win,d.price-1,-1);d['t3']=d.finish_position.between(1,3)
print('races',d.race_id.nunique(),'runners',len(d),'with SM value',d.sm.notna().sum(),'dates',d.date.nunique())
M=d[d.sm.notna()]                       # main-model runners = comparison population
def row(name,x,base=None):
    if len(x)<40: return f'{name:34} n={len(x):4} (too few)'
    x=x.sort_values('date');h=len(x)//2
    ex=x.drop(x[x.win].nlargest(3,'price').index)
    s=f'{name:34} n={len(x):5} win={x.win.mean()*100:5.1f}% t3={x.t3.mean()*100:4.0f}% avg${x.price.mean():5.1f} ROI={x.ret.mean()*100:+6.1f}% | halves {x.ret.iloc[:h].mean()*100:+5.0f}/{x.ret.iloc[h:].mean()*100:+5.0f} | ex3 {ex.ret.mean()*100:+6.1f}%'
    return s
def tbl(title,col,bins,labels):
    print('\n--',title)
    M2=M.assign(b=pd.cut(M[col],bins,labels=labels,right=False))
    for b in labels:
        y=M2[M2.b==b]
        print(row(f'{b} SM>=+0.5',y[y.sm>=.5]));print(row(f'{b} all main runners',y))
print('\n== overall');print(row('SM>=+0.5',M[M.sm>=.5]));print(row('SM>=+1.0',M[M.sm>=1]));print(row('SM 0 to 0.5',M[(M.sm>=0)&(M.sm<.5)]));print(row('SM<=-0.5',M[M.sm<=-.5]));print(row('all main runners',M))
tbl('gap from top rated (WPR)','gap',[0,2,4,6,9,100],['0-2','2-4','4-6','6-9','9+'])
tbl('first starters in the race','fs_race',[0,1,2,100],['none','1','2+'])
tbl('price','price',[1,3,6,10,20,1000],['<$3','$3-6','$6-10','$10-20','$20+'])
tbl('field size','field',[0,9,13,100],['<=8','9-12','13+'])
print('\n== combos (SM>=+0.5)')
S=M[M.sm>=.5]
for gl,gh in((0,4),(0,6),(0,9)):
  for pl,ph in((3,20),(5,20),(6,15),(1,1000)):
    for fs,fn in((0,'no first starters'),(99,'any')):
        x=S[(S.gap>=gl)&(S.gap<gh)&(S.price>=pl)&(S.price<ph)&((S.fs_race==0) if fs==0 else True)]
        print(row(f'gap<{gh} ${pl}-{ph} {fn}',x))
