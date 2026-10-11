"""Predict TopRate's hand-reviewed Race Strength (RS = winner's ATW) from the inputs the KB article lists.

Stages: 1 load results + per-race RS (exact from atw), 2 per-run features (prior ratings at today's weight, WFA),
3 per-race features (ratings, margin spread, time vs par, sectionals, market, incidents), 4 LightGBM + ablation.
Needs: pandas numpy lightgbm.  Run from repo root: python analysis/wpr_race_strength.py [cache_dir]
Held-out (races from 2025-03): RMSE ~2.1, MAE ~1.6, 72% within 2 points; RS sd is 6.45.

CAVEAT (11 Oct 2026): those numbers lean on TopRate's sect_i_* columns. They are NOT derived from the real race time
(correlation with GPS race time within track and distance is -0.004) and correlate 0.65 with RS, so they probably
carry TopRate's own ratings. With only independent inputs (ratings, margins, market, GPS time and sectionals) RMSE is
about 3.3 (3.6 with no time at all). See the own-ratings entry in CLAUDE.md.
"""
import sys, glob, os, numpy as np, pandas as pd, lightgbm as lgb
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from wpr_recreate import racing_age, k_per_length
S = (sys.argv[1] if len(sys.argv) > 1 else "/tmp/wpr_rs_cache") + "/"
os.makedirs(S, exist_ok=True)

# ---- stage 1: results + per-race RS
rr = pd.concat(pd.read_csv(f, low_memory=False) for f in sorted(glob.glob("race_results_20*.csv.gz")))
rr.to_pickle(S + "rr.pkl")
# ---- stage 1b: per-race RS
d=rr
d=d[d.atw.notna()&d.marginFinish.notna()&(d.isBarrierTrial!=1)].copy()
d['m']=np.where(d.positionFinish==1,0,d.marginFinish)
rows=[]
for rid,g in d.groupby('race_id'):
    if len(g)<6 or g.m.nunique()<5: continue
    x=g.m.values;y=g.atw.values
    b,a=np.polyfit(x,y,1);res=y-(a+b*x)
    rows.append((rid,g.date.iloc[0],g.distance.iloc[0],g.going.iloc[0],g.trackGrading.iloc[0],g.track.iloc[0],g.winners_time.iloc[0],g.race_class.iloc[0],a,-b,res.std(),np.abs(res).max(),len(g)))
r=pd.DataFrame(rows,columns='rid date dist going tg track wt cls RS k rs rmax n'.split())
r.to_pickle(S+'atw_slopes.pkl')
print(len(r),'resid sd quantiles',r.rs.quantile([.1,.25,.5,.75,.9]).round(3).tolist())
r=r[(r.rs<0.5)&(r.k>0)]
print(len(r))
r['kd']=r.k*r.dist
print(r.groupby(pd.cut(r.dist,[0,900,1000,1100,1200,1300,1400,1500,1600,1800,2000,2200,2600,5000]),observed=True).agg(k=('k','median'),kd=('kd','median'),ksd=('k','std'),n=('k','size')).round(3))
# ---- stage 2: per-run features
d=rr.copy()
d=d[d.isBarrierTrial!=1].copy()
d=d.sort_values(['horse_id','date','race_id']).reset_index(drop=True)
g=d.groupby('horse_id')
for i in range(1,7): d[f's{i}']=g.wpr.shift(i)
d['p1']=d.s1;d['p3']=d[['s1','s2','s3']].mean(axis=1);d['p6max']=d[[f's{i}' for i in range(1,7)]].max(axis=1)
d['pw']=(d.s1*4+d.s2*3+d.s3*2+d.s4*1).div(((d[['s1','s2','s3','s4']].notna())*np.array([4,3,2,1])).sum(axis=1).replace(0,np.nan))
d['peak']=g.wpr.transform(lambda s:s.shift().cummax())
d['npri']=g.wpr.transform(lambda s:s.shift().expanding().count())
d['gap_days']=(pd.to_datetime(d.date)-pd.to_datetime(g.date.shift())).dt.days
tab=pd.read_csv('analysis/wpr_wfa_table.csv')
d['age']=pd.Series(racing_age(d.date,d.horse_foaled),index=d.index).fillna(4).clip(2,4);d['mon']=pd.to_datetime(d.date).dt.month;d['db']=(d.distance//100).clip(8,24)
d=d.merge(tab,on=['age','mon','db'],how='left')
# adult (true 4+) wfa fallback ok via age clip 4. weight adj
d['fm']=d.horse_sex.isin(['F','M'])*2.0
d['wadj']=0.8*(d.weightCarried+d.fm-d.wfa_tab)
d['k']=k_per_length(d.distance);d['m']=np.where(d.positionFinish==1,0,d.marginFinish)
for c in ['p1','p3','p6max','pw','peak']: d['x_'+c]=d[c]+d.wadj
d['price']=d.priceStarting.where(d.priceStarting>1)
d['steward']=d.comments_steward.notna().astype(int)
vid=d.comments_video.fillna('').str.lower()
d['v_wide']=vid.str.contains('wide|three deep|3 wide').astype(int);d['v_check']=vid.str.contains('check|hampered|held up|bump|shift|interfer').astype(int)
d['v_slow']=vid.str.contains('slow|start').astype(int)
d.to_pickle(S+'runs_feat.pkl');print(len(d),d.wfa_tab.notna().mean(),d.price.notna().mean(),d.comments_video.notna().mean(),d.steward.mean())
# ---- stage 3: per-race features
d=pd.read_pickle(S+'runs_feat.pkl')
sl=pd.read_pickle(S+'atw_slopes.pkl');sl=sl[(sl.rs<0.5)&(sl.k>0)].set_index('rid')
d=d[d.race_id.isin(sl.index)&d.m.notna()].copy()
print('races',d.race_id.nunique())
for c in ['p1','p3','pw','p6max','peak']: d['i_'+c]=d['x_'+c]+d.k*d.m
d['pr']=1/d.price; d['pr']=d.pr/d.groupby('race_id').pr.transform('sum')
def topmean(s):
    s=s.dropna();return s.nlargest(max(3,len(s)//2)).mean() if len(s) else np.nan
g=d.groupby('race_id')
R=pd.DataFrame({'n':g.size(),'date':g.date.first(),'track':g.track.first(),'dist':g.distance.first(),'going':g.going.first(),'tg':g.trackGrading.first(),'cls':g.race_class.first(),
 'wt':g.winners_time.first(),'mmean':g.m.mean(),'msd':g.m.std(),'mmax':g.m.max(),'m3':g.m.apply(lambda s:s.nsmallest(4).iloc[-1] if len(s)>3 else np.nan),'mmed':g.m.median(),
 'frac_rated':g.npri.apply(lambda s:(s>=2).mean()),'npri_mean':g.npri.mean(),'gap_med':g.gap_days.median()})
for c in ['p1','p3','pw','p6max','peak']:
    col='i_'+c
    R[c+'_mean']=g[col].mean();R[c+'_med']=g[col].median();R[c+'_top']=g[col].apply(topmean);R[c+'_sd']=g[col].std()
    R[c+'_mkt']=d.assign(w=d[col]*d.pr).groupby('race_id').w.sum()/d.assign(w=d.pr.where(d[col].notna())).groupby('race_id').w.sum()
# winner-specific
w=d[d.positionFinish==1].drop_duplicates('race_id').set_index('race_id')
for c in ['sect_i_time','sect_i_early','sect_i_l200','sect_i_l400','sect_i_l600','sect_i_l800','sect_i_400_200','sect_i_600_400','sect_ld_early','time_last600m','price','i_p3','i_peak','x_p3','npri']:
    R['w_'+c]=w[c]
R['sect_mean']=g.sect_i_time.mean();R['sect_max']=g.sect_i_time.max()
R['l600_mean']=g.sect_i_l600.mean();R['l200_mean']=g.sect_i_l200.mean();R['early_mean']=g.sect_i_early.mean()
R['fav']=g.price.min();R['overround']=g.price.apply(lambda s:(1/s).sum())
R['corr_mkt']=d.groupby('race_id').apply(lambda x:np.corrcoef(np.log(x.price[x.price.notna()&x.x_p3.notna()]),-x.x_p3[x.price.notna()&x.x_p3.notna()])[0,1] if (x.price.notna()&x.x_p3.notna()).sum()>4 else np.nan)
for c in ['steward','v_wide','v_check','v_slow']: R['inc_'+c]=g[c].mean()
# overall time: par from earlier races at same track/dist/going
R['going_n']=R.going.str.extract(r'(\d+)').astype(float)[0]
full=pd.read_pickle(S+'rr.pkl');full=full[(full.isBarrierTrial!=1)&(full.winners_time>20)].drop_duplicates('race_id')[['race_id','date','track','distance','going','winners_time']].sort_values(['date','race_id']).reset_index(drop=True)
full['key']=full.track+'|'+full.distance.astype(str)+'|'+full.going;full['key2']=full.track+'|'+full.distance.astype(str)
full['key3']=full.distance.astype(str)+'|'+full.going
for kk,nm in [('key','par_exp'),('key2','par2'),('key3','par3')]:
    full[nm]=full.groupby(kk).winners_time.transform(lambda x:x.shift().expanding(min_periods=8).median())
    full['td_'+nm]=(full.winners_time-full[nm])/full[nm]*100
full['mtg']=full.track+'|'+full.date
for c in ['td_par_exp','td_par2','td_par3']:
    sm=full.groupby('mtg')[c].transform('sum');kc=full.groupby('mtg')[c].transform('count')
    full['o_'+c]=(sm-full[c].fillna(0))/(kc-full[c].notna()).replace(0,np.nan)
full['par_n']=full.groupby('key').winners_time.transform(lambda x:x.shift().expanding().count())
R=R.join(full.set_index('race_id')[['par_exp','par2','par3','td_par_exp','td_par2','td_par3','o_td_par_exp','o_td_par2','o_td_par3','par_n']])
R['tdev']=R.td_par_exp;R['tdev2']=R.td_par2;R['tdev3']=R.td_par3
R['mtg']=R.track+'|'+R.date
for c in ['p3_mean','p3_mkt','sect_max','p3_med']:
    sm=R.groupby('mtg')[c].transform('sum');k=R.groupby('mtg')[c].transform('count')
    R['mtgo_'+c]=(sm-R[c].fillna(0))/(k-R[c].notna()).replace(0,np.nan)
R['speed']=R.dist/R.wt
R['month']=pd.to_datetime(R.date).dt.month
R['RS']=sl.RS.reindex(R.index)
R['state_trk']=R.track.astype('category').cat.codes;R['cls_c']=R.cls.astype('category').cat.codes
R=R[R.RS.notna()&(R.dist<=2600)&(R.n>=5)]
R.to_pickle(S+'RS_full.pkl');print(R.shape);print(R.isna().mean().sort_values().tail(8))
# ---- stage 4: model
R=pd.read_pickle(S+'RS_full.pkl').sort_values('date')
G={
 'ratings':[c for c in R.columns if c.split('_')[0] in('p1','p3','pw','p6max','peak') and c.endswith(('_mean','_med','_top','_sd'))]+['frac_rated','npri_mean','gap_med','w_i_p3','w_i_peak','w_x_p3','w_npri','mtgo_p3_mean','mtgo_p3_med'],
 'margins':['n','mmean','msd','mmax','m3','mmed'],
 'time':['wt','speed','tdev','tdev2','tdev3','o_td_par_exp','o_td_par2','o_td_par3','par_n'],
 'sectionals':[c for c in R.columns if c.startswith('w_sect') or c in('w_time_last600m','sect_mean','sect_max','l600_mean','l200_mean','early_mean','mtgo_sect_max')],
 'market':[c for c in R.columns if c.endswith('_mkt')]+['w_price','fav','overround','corr_mkt','mtgo_p3_mkt'],
 'incidents':[c for c in R.columns if c.startswith('inc_')],
 'context':['dist','going_n','tg','cls_c','state_trk','month'],
}
for k in G: G[k]=[c for c in dict.fromkeys(G[k]) if c in R.columns]
cut=R.date.searchsorted('2025-03-01') if False else int((R.date<'2025-03-01').sum())
tr,te=R.iloc[:cut],R.iloc[cut:]
P=dict(objective='regression',learning_rate=0.03,num_leaves=15,min_data_in_leaf=40,bagging_fraction=0.8,bagging_freq=1,feature_fraction=0.7,lambda_l2=5,verbose=-1,seed=1)
def fit(F,ret=False):
    v=tr.iloc[-int(len(tr)*.12):];t=tr.iloc[:-int(len(tr)*.12)]
    b=lgb.train(P,lgb.Dataset(t[F],t.RS),2000,valid_sets=[lgb.Dataset(v[F],v.RS)],callbacks=[lgb.early_stopping(100,verbose=False)])
    p=b.predict(te[F],num_iteration=b.best_iteration);e=te.RS-p
    out=(np.sqrt((e**2).mean()),np.abs(e).mean(),b.best_iteration)
    return (out,b,p) if ret else out
print('train',len(tr),'test',len(te),'RS sd test',te.RS.std().round(2))
allF=[c for k in G for c in G[k]]
(r,b,p)=fit(allF,True);print('ALL   RMSE %.3f MAE %.3f iters %d'%r)
print('within 1: %.1f%%  within 2: %.1f%%  within 3: %.1f%%'%tuple(100*(np.abs(te.RS-p)<=t).mean() for t in(1,2,3)))
print('--- only one group + context')
for k in G:
    if k=='context':continue
    print('%-11s RMSE %.3f MAE %.3f'%((k,)+fit(G[k]+G['context'])[:2]))
print('--- all minus one group')
for k in G:
    if k=='context':continue
    F=[c for kk in G if kk!=k for c in G[kk]];print('-%-10s RMSE %.3f MAE %.3f'%((k,)+fit(F)[:2]))
imp=pd.Series(b.feature_importance('gain'),index=allF).sort_values(ascending=False);print((imp/imp.sum()).head(15).round(3).to_string())
te=te.assign(pred=p,err=te.RS-p);te.to_pickle(S+'RS_test_pred.pkl')
print(te.groupby(pd.cut(te.dist,[0,1100,1300,1600,2000,2600])).err.agg(['mean','std','count']).round(2))

# ---- stage 5: time-to-rating offsets, same-card ratings, huber, quarterly walk-forward retrain
# (quarterly expanding-window retrain: RMSE ~2.01, MAE ~1.49, 74% within 2; a 2-year window is worse)
R=R.reset_index() if 'race_id' not in R.columns else R
R=R.sort_values(['date','race_id']).reset_index(drop=True)
R['k']=np.maximum(2750/R.dist,1.5)
R['ks']=R.k*R.w_sect_i_time
R['off']=R.RS-R.ks                     # true time->rating offset (known for past races only)
R['imp_off']=R.p3_med-R.ks;R['imp_off1']=R.p1_med-R.ks;R['imp_offm']=R.p3_mkt-R.ks
R['bias']=R.RS-R.p3_med                # true RS minus ratings-implied (past only)
# history of true offsets / biases (strictly earlier races)
def lag(keycols,col,n,name):
    g=R.groupby(keycols)[col]
    R[name]=g.transform(lambda s:s.shift().rolling(n,min_periods=3).mean())
R['mtg']=R.track+'|'+R.date
lag('track','off',40,'h_off_trk40');lag('track','off',10,'h_off_trk10');lag('track','bias',40,'h_bias_trk40')
R['key2']=R.track+'|'+R.dist.astype(str);lag('key2','off',15,'h_off_key15')
lag('mtg','off',20,'h_off_mtg');lag('mtg','bias',20,'h_bias_mtg')
R['h_mtg_n']=R.groupby('mtg').cumcount()
# same-card other races, ratings-only (no target)
for c in ['imp_off','imp_off1']:
    sm=R.groupby('mtg')[c].transform('sum');kc=R.groupby('mtg')[c].transform('count')
    R['o_'+c]=(sm-R[c].fillna(0))/(kc-R[c].notna()).replace(0,np.nan)
R['est_off_hist']=R.h_off_mtg.fillna(R.h_off_trk10)
R['pred_hist']=R.ks+R.est_off_hist
NEW=['imp_off','imp_off1','imp_offm','h_off_trk40','h_off_trk10','h_bias_trk40','h_off_key15','h_off_mtg','h_bias_mtg','h_mtg_n','o_imp_off','o_imp_off1','est_off_hist','pred_hist','ks']
cut=int((R.date<'2025-03-01').sum());tr,te=R.iloc[:cut],R.iloc[cut:]
P=dict(objective='regression',learning_rate=0.03,num_leaves=15,min_data_in_leaf=40,bagging_fraction=0.8,bagging_freq=1,feature_fraction=0.7,lambda_l2=5,verbose=-1)
def fit(F,target='RS',seeds=(1,),ret=False):
    v=tr.iloc[-int(len(tr)*.12):];t=tr.iloc[:-int(len(tr)*.12)]
    def y(df): return df.RS-(df.ks if target=='off' else 0)
    ps=[]
    for sd in seeds:
        b=lgb.train({**P,'seed':sd},lgb.Dataset(t[F],y(t)),3000,valid_sets=[lgb.Dataset(v[F],y(v))],callbacks=[lgb.early_stopping(100,verbose=False)])
        ps.append(b.predict(te[F],num_iteration=b.best_iteration))
    p=np.mean(ps,0)+(te.ks if target=='off' else 0);e=te.RS-p
    r=(np.sqrt(np.nanmean(e**2)),np.nanmean(np.abs(e)))
    return (r,p,b) if ret else r
base=[c for k in G for c in G[k]]

nohist=[c for c in NEW if not c.startswith(('h_','est_','pred_'))]
F=base+nohist
P.update(objective='huber',alpha=3.0,num_leaves=31,min_data_in_leaf=25,learning_rate=0.03)
R['q']=pd.PeriodIndex(R.date,freq='Q').astype(str)
qs=sorted(R.q[R.date>='2025-03-01'].unique())
def run(window=None,seeds=(1,2,3)):
    out=[]
    for q in qs:
        tst=R[R.q==q]
        if q=='2025Q1': tst=tst[tst.date>='2025-03-01']
        trn=R[R.date<tst.date.min()]
        if window: trn=trn[trn.date>=(pd.Timestamp(tst.date.min())-pd.Timedelta(days=window)).strftime('%Y-%m-%d')]
        v=trn.iloc[-int(len(trn)*.1):];t=trn.iloc[:-int(len(trn)*.1)]
        ps=[]
        for sd in seeds:
            b=lgb.train({**P,'seed':sd},lgb.Dataset(t[F],t.RS),3000,valid_sets=[lgb.Dataset(v[F],v.RS)],callbacks=[lgb.early_stopping(100,verbose=False)])
            ps.append(b.predict(tst[F],num_iteration=b.best_iteration))
        out.append(tst.assign(p=np.mean(ps,0)))
    o=pd.concat(out);e=o.RS-o.p
    return o,np.sqrt((e**2).mean()),e.abs().mean()
for w in (None,730):
    o,r,m=run(w);print('walk-forward quarterly, window',w,'RMSE %.3f MAE %.3f  n=%d  mean err %.2f'%(r,m,len(o),(o.RS-o.p).mean()))
    print((o.RS-o.p).groupby(o.q).mean().round(2).to_dict())
    e=o.RS-o.p;print('within 1/2/3: %.1f/%.1f/%.1f%%'%tuple(100*(e.abs()<=t).mean() for t in(1,2,3)))
o.to_pickle(S+'RS_walkfwd.pkl')
R.to_pickle(S+'RS_full2.pkl')
