import sys; sys.path.insert(0,'.')
import numpy as np, pandas as pd
from own_ratings import tune as T
D=pd.read_pickle(T.CACHE+'/feat.pkl')
D=D.sort_values('race_id',kind='mergesort').reset_index(drop=True)
def X(t,quad): 
    l=np.log(t.pm.values); return np.column_stack([l,l*l]) if quad else l[:,None]
def seg(t): return np.flatnonzero(np.r_[True,t.race_id.values[1:]!=t.race_id.values[:-1]])
def pred(t,b,quad):
    s=seg(t); z=X(t,quad)@b; sz=np.diff(np.r_[s,len(t)]); rid=np.repeat(np.arange(len(s)),sz)
    e=np.exp(z-np.maximum.reduceat(z,s)[rid]); return e/np.add.reduceat(e,s)[rid]
for quad in (False,True):
    print('quad',quad)
    rows=[]
    for ty in range(2020,2027):
        tr=D[D.year<=ty-1]; te=D[D.year==ty].copy()
        b=T._clogit_fit(X(tr,quad),seg(tr),tr.win.values,l2=0.0)
        te['p']=pred(te,b,quad); te['ev']=te.p*te.sp; te['ret']=np.where(te.win==1,te.sp,0.0)
        rows.append(te)
        print(ty,'beta',np.round(b,3))
    A=pd.concat(rows)
    for lo in (1.0,1.03,1.05,1.10,1.15,1.20):
        x=A[A.ev>lo]
        ex10=x.drop(x[x.win==1].nlargest(10,'sp').index)
        print(f' ev>{lo}: n={len(x)} win {x.win.mean()*100:.1f}% avg ${x.sp.mean():.2f} ROI {(x.ret.mean()-1)*100:+.1f}% ex10 {(ex10.ret.mean()-1)*100:+.1f}% hc10 {(np.where(x.win==1,x.sp*.9,0).mean()-1)*100:+.1f}% yrs',' '.join(f"{(x[x.year==y].ret.mean()-1)*100:+.0f}" for y in range(2020,2027)))
print('---- diagnostics (linear calibration, ev>1.10)')
A['book']=1/A.sp; A['book']=A.groupby('race_id').book.transform('sum')
print(A.book.describe().round(3).to_dict())
x=A[A.ev>1.10].copy()
x['bq']=pd.qcut(x.book,5,duplicates='drop')
print(x.groupby('bq',observed=True).agg(n=('ret','size'),roi=('ret',lambda s:(s.mean()-1)*100),win=('win','mean'),sp=('sp','mean')).round(2))
x['pb']=pd.cut(x.sp,[1,3,6,10,20,50,1000])
print(x.groupby('pb',observed=True).agg(n=('ret','size'),roi=('ret',lambda s:(s.mean()-1)*100),win=('win','mean')).round(2))
print('races with book<1.05:',(A.groupby('race_id').book.first()<1.05).mean().round(4))
y=A[A.book>=1.15]; y=y[y.ev>1.10]
print('book>=1.15 only: n',len(y),'ROI',round((y.ret.mean()-1)*100,1))
