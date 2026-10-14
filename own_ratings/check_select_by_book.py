import sys; sys.path.insert(0,'.')
import numpy as np, pandas as pd
from own_ratings import tune as T
o=pd.read_pickle(T.CACHE+'/obs.pkl'); D=pd.read_pickle(T.CACHE+'/feat.pkl')
r,te=T.evaluate(T.BASE,(2023,2024,2025,2026),o,D,keep=True,mode='lgbm')
te['book']=te.groupby('race_id').sp.transform(lambda s:(1/s).sum())
te.to_pickle(T.CACHE+'/te_lgbm.pkl')
def show(name,x):
    if not len(x): print(name,'n=0'); return
    ex10=x.drop(x[x.win==1].nlargest(10,'sp').index)
    print(f'{name:28} n={len(x):5} win {x.win.mean()*100:4.1f}% avg ${x.sp.mean():5.2f} ROI {(x.ret.mean()-1)*100:+6.1f}% ex10 {(ex10.ret.mean()-1)*100:+6.1f}%  yrs',' '.join(f"{(x[x.year==y].ret.mean()-1)*100:+.0f}" for y in (2023,2024,2025,2026)))
for lab,mask in (('all races',te.book>0),('book<1.00',te.book<1.0),('book 1.00-1.10',(te.book>=1.0)&(te.book<1.10)),('book>=1.10 (clean)',te.book>=1.10)):
    print('==',lab,'races',te[mask].race_id.nunique())
    x=te[mask]
    show('Select (EV>1.20)',x[x.tier=='S']); show('Volume incl Select',x[x.tier!=''])
