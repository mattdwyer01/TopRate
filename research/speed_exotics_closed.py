"""Closed-race check for the market top-5/6 first-four box: estimated return by field size and quarter, and the real TAB dividends. usage: PYTHONPATH=.:research python research/speed_exotics_closed.py R_CACHE.csv"""
import sys, numpy as np, pandas as pd
sys.path.insert(0,'research'); sys.path.insert(0,'.')
import speed_exotics_select as SEL, speed_exotics_nuggets as N
P=SEL.dividend_pairs(); fit=SEL.fit_div(P)
R=pd.read_csv(sys.argv[1])
R['ed3']=SEL.est_div(R.h3,R.field,fit['Trifecta']); R['ed4']=SEL.est_div(R.h4,R.field,fit['FirstFour'])
R['train']=R.date<'2026-02-01'
cut=R.m_ent.quantile([.2,.4]).values; print('entropy 20th/40th percentile',cut.round(3),'| Q0 mean field',R[R.m_ent<=cut[0]].field.mean().round(1),'mean fav chance',R[R.m_ent<=cut[0]].m_top1.mean().round(2))
Q=R[R.m_ent<=cut[0]]
def roi(g,hit,ed,c): return (g[hit]*g[ed]).sum()/(c*len(g))-1
print('\nQ0 (closed races) by field size, est ROI of market top-6 FF / top-5 FF / Spd top-6 FF; hit x implied')
Q=Q.assign(fb=pd.cut(Q.field,[0,6,7,8,10,30]))
for fb,g in Q.groupby('fb',observed=True):
    print(f"  field {fb}: n {len(g):4d}  m6ff {roi(g,'m6_ff','ed4',360)*100:+4.0f}%  m5ff {roi(g,'m5_ff','ed4',120)*100:+4.0f}%  s6ff {roi(g,'s6_ff','ed4',360)*100:+4.0f}%  m6 hit {g.m6_ff.mean()*100:.0f}%")
print('\nQ0 by quarter, m6 ff est ROI:')
Q['q']=pd.to_datetime(Q.date).dt.to_period('Q')
for q,g in Q.groupby('q'): print(f"  {q}: n {len(g):4d} {roi(g,'m6_ff','ed4',360)*100:+4.0f}%  m5 ff {roi(g,'m5_ff','ed4',120)*100:+4.0f}%")
# REAL dividends, market pools by entropy
import runners_io
r=runners_io.read_runners(); r=r[(r.date.astype(str)>='2026-10-02')&(r.scratched.fillna(0)==0)].copy()
r['v']=r.venue.astype(str).str.upper(); r['px']=pd.to_numeric(r.starting_price_sp,errors='coerce').fillna(pd.to_numeric(r.fixed_win_price,errors='coerce'))
dv=pd.read_csv('tab_dividends.csv'); dv=dv[dv['product'].isin(['Trifecta','FirstFour'])&(dv.status=='Paying')].drop_duplicates(['date','venue','race_no','product'])
rows=[]
for (dt,ven,rn),g in r.groupby([r.date.astype(str),'v','race']):
    sub=dv[(dv.date==dt)&(dv.venue.str.split(' @ ').str[0]==ven)&(dv.race_no==rn)]
    t=sub[sub['product']=='Trifecta']; f=sub[sub['product']=='FirstFour']
    if t.empty or f.empty or g.px.isna().any() or (g.px<=1).any() or g.tab_number.isna().any() or len(g)<6: continue
    book=(1/g.px).sum()
    if not 1.05<=book<=2.0: continue
    p=(1/g.px)/book; ent=float(-(p*np.log(p)).sum()/np.log(len(p)))
    g=g.sort_values('px'); tabs=g.tab_number.astype(int).tolist()
    t3={int(x) for x in str(t.iloc[0].selections).split('/')}; f4={int(x) for x in str(f.iloc[0].selections).split('/')}
    row=dict(ent=ent,field=len(g),tdiv=t.iloc[0].amount,fdiv=f.iloc[0].amount)
    for n in (5,6): row[f'm{n}_tri']=int(t3<=set(tabs[:n])); row[f'm{n}_ff']=int(f4<=set(tabs[:n]))
    rows.append(row)
X=pd.DataFrame(rows); print('\nREAL TAB dividends, market top-N boxes, 2 to 21 Oct,',len(X),'races')
for lab,m in (('closed (entropy <= 20th pct)',X.ent<=cut[0]),('next 20-40 pct',(X.ent>cut[0])&(X.ent<=cut[1])),('everything else',X.ent>cut[1])):
    g=X[m]
    for n,c in ((5,120),(6,360)):
        ret=g[f'm{n}_ff']*g.fdiv; ex=ret.copy()
        if g[f'm{n}_ff'].sum()>=3: ex.loc[ret.sort_values(ascending=False).index[:3]]=0
        print(f"  {lab:30s} m{n} ff ${c}: races {len(g):3d} hits {int(g[f'm{n}_ff'].sum()):3d} return {(ret.sum()/(c*len(g))-1)*100:+4.0f}% (ex top3 {(ex.sum()/(c*len(g))-1)*100:+4.0f}%)")
