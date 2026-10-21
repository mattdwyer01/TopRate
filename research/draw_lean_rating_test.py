"""Draw lean vs rating: how many rating points is a wide barrier worth on a day that has leaned inside or wide? Lean = mean barrier fraction of the top 4 minus 0.5, averaged over earlier races of the same meeting (3+ races), observable live from TAB placings. Target = runner wpr minus race mean, minus its prior-3 form likewise. Fit 2022-24, test 2025. Run from repo root."""
import pandas as pd, numpy as np
cols=['race_id','meeting_id','date','raceNumber','barrier','positionFinish','horse_id','wpr','isBarrierTrial','is_jumpout']
d=pd.concat([pd.read_csv(f'race_results_{y}.csv.gz',usecols=cols) for y in range(2022,2026)])
d=d[(d.isBarrierTrial.fillna(0)==0)&(d.is_jumpout.fillna(0)==0)].copy()
d['date']=pd.to_datetime(d.date); d=d.sort_values(['horse_id','date'])
d['p3']=d.groupby('horse_id').wpr.transform(lambda s:s.shift(1).rolling(3,min_periods=2).mean())
d['fin']=pd.to_numeric(d.positionFinish,errors='coerce'); d['b']=pd.to_numeric(d.barrier,errors='coerce')
d['n']=d.groupby('race_id').race_id.transform('size')
d=d[(d.b>=1)&(d.fin>=1)&(d.fin<=d.n)].copy()
d['bf']=((d.b-1)/(d.n-1)).clip(0,1)
print('A',len(d),d.p3.notna().sum())
t=d[d.fin<=4].groupby('race_id').agg(top4=('bf','mean'),k=('bf','size')); t=t[t.k==4]
rc=d.groupby('race_id').agg(md=('meeting_id','first'),n=('n','first')).join(t.top4).dropna()
rc=rc[rc.n>=8].reset_index().sort_values(['md','race_id']).set_index('race_id').copy(); rc['top4']=rc.top4-0.5
rc['i']=rc.groupby('md').cumcount(); cs=rc.groupby('md').top4.cumsum()-rc.top4; rc['lean']=(cs/rc.i.replace(0,np.nan)).where(rc.i>=3)
print('B',len(rc),rc.lean.notna().sum())
d=d.merge(rc[['lean']].reset_index(),on='race_id',how='left')
d=d[d.lean.notna()&d.p3.notna()&d.wpr.notna()&(d.n>=8)].copy(); print('C',len(d))
for c in('wpr','p3'): d[c+'_d']=d[c]-d.groupby('race_id')[c].transform('mean')
d['r']=d.wpr_d-d.p3_d; d['x']=d.bf-0.5
for lo,hi,name in((-1,-.10,'inside-favoured (lean<=-0.10)'),(-.10,-.04,'mild inside'),(-.04,.04,'neutral'),(.04,.10,'mild wide'),(.10,1,'wide-favoured (lean>=0.10)')):
    s=d[(d.lean>lo)&(d.lean<=hi)]; W=s[s.bf>=.67]; I=s[s.bf<=.33]
    se=np.sqrt(W.r.var()/len(W)+I.r.var()/len(I))
    print(f'{name:32s} races {s.race_id.nunique():6d} wide third minus inner third: {W.r.mean()-I.r.mean():+.2f} rating pts (se {se:.2f})')
k=np.polyfit(d.lean*d.x,d.r,1)[0]; print('slope on lean*x',round(k,2),'=> wide-vs-inner gap at lean 0.10:',round(k*.10*.8,2),'at 0.15:',round(k*.15*.8,2))
print('\n--- out of sample: fit k on 2022-24, test 2025 ---')
d['yr']=pd.to_datetime(d.date).dt.year; d['z']=d.lean*d.x
tr=d[d.yr<=2024]; te=d[d.yr==2025]
k=(tr.z*tr.r).sum()/(tr.z**2).sum(); print('k fit',round(k,2),' k on 2025 alone',round((te.z*te.r).sum()/(te.z**2).sum(),2))
base=((te.r-te.r.mean())**2).mean()
for kk in (0,4,8,12,k,24):
    print(f'  k={kk:5.1f}: test MSE {((te.r-te.r.mean()-kk*te.z)**2).mean():.4f} (gain vs none {base-((te.r-te.r.mean()-kk*te.z)**2).mean():+.4f})')
# by lean strength
te=te.assign(lb=pd.cut(te.lean,[-1,-.1,-.04,.04,.1,1]))
print(te.groupby('lb',observed=True).apply(lambda s: pd.Series(dict(n=len(s),slope=(s.z*s.r).sum()/(s.z**2).sum() if (s.z**2).sum()>0 else np.nan))).round(1))
