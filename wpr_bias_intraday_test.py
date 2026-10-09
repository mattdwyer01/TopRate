"""Read-only: does the day-of track-bias input still help when only finishing order is known (intraday), as it is until the authoritative results arrive?
Compares the suitability adjustment under three views of the SAME 2025-07+ main-model runners (oos_main.csv.gz from wpr_oos_2025_backtest_build.py):
  A no bias (all day-of bias inputs blank, what the first race of a meeting sees)
  B intraday bias (finish order only: positions 1-4 known, the rest set to the mean of the remaining positions, no 800m positions, so the front-bias
    inputs stay blank and only the inside/outside draw bias is read)
  C full bias (800m positions and every finishing position, what the model was trained on)
Scored by how well p0 + adj + weight predicts the actual WPR. usage: python wpr_bias_intraday_test.py oos_main.csv.gz"""
import sys, json; sys.path.insert(0,'.'); sys.path.insert(0,'projection')
import numpy as np, pandas as pd, lightgbm as lgb
import features as F
oos=pd.read_csv(sys.argv[1]); oos['date']=pd.to_datetime(oos.date)
H=F.load_history().sort_values(['horse_id','date','race_id']).reset_index(drop=True); ph=F.build_pos_hist(H)
Y=F.load_results_all()
S_full=F.build_suit(Y,ph,bias_since='2025-06-28'); S_full=S_full[S_full.date>='2025-07-01'].drop_duplicates(['race_id','horse_id'])
Yd=Y.copy(); fin=pd.to_numeric(Yd.positionFinish,errors='coerce'); N=Yd.field_size
Yd['positionFinish']=np.where(fin<=4,fin,np.where(fin.notna(),(5+N)/2,np.nan)); Yd['position800m']=np.nan
S_deg=F.build_suit(Yd,ph,bias_since='2025-06-28'); S_deg=S_deg[S_deg.date>='2025-07-01'].drop_duplicates(['race_id','horse_id'])
BIAS=['fa_cum','oa_cum','fa_last','oa_last','n_prev']
mix=S_full.merge(S_deg[['race_id','horse_id']+BIAS],on=['race_id','horse_id'],how='left',suffixes=('','_d'))
for c in BIAS: mix[c]=mix[c+'_d']
mix=mix.drop(columns=[c+'_d' for c in BIAS])
sf=json.load(open('projection/models/suitability_features.json')); sm=lgb.Booster(model_file='projection/models/suitability_model.txt')
def predict(S,mask=False):
    Hh=H[H.date>='2025-07-01'][['race_id','horse_id','distance','going','barrier','field_size']].copy(); Hh['dist']=Hh.distance; Hh['going_num']=F._num(Hh.going); Hh['bf']=(Hh.barrier-1)/(Hh.field_size-1)
    Z=oos[['race_id','horse_id']].merge(Hh[['race_id','horse_id','bf','field_size','dist','going_num']],on=['race_id','horse_id'],how='left')
    Z=Z.merge(S.drop(columns=[c for c in ('bf','field_size','dist','going_num') if c in S.columns]),on=['race_id','horse_id'],how='left')
    Z=Z.merge(ph[['race_id','horse_id','m800_hist3','own_rel']],on=['race_id','horse_id'],how='left')
    if mask:
        for c in BIAS: Z[c]=np.nan
    Z['sty']=Z.pos_hist3-0.5
    Z['i_front'],Z['i_front2']=Z.fa_cum*Z.sty,Z.fa_last*Z.sty
    Z['i_out'],Z['i_out2']=Z.oa_cum*(Z.bf-0.5),Z.oa_last*(Z.bf-0.5)
    Z['j_style'],Z['j_p8_x']=Z.j_dev*Z.sty,Z.j_p8-Z.pos_hist3
    for c in sf:
        if c not in Z.columns: Z[c]=np.nan
    return Z, sm.predict(Z[sf])
ZA,aA=predict(S_full,mask=True); ZB,aB=predict(mix); ZC,aC=predict(S_full)
D=oos[['race_id','horse_id','date','track','wpr','p0','wt_rel']].copy(); D['A']=aA; D['B']=aB; D['C']=aC
D['n_prev']=ZB.n_prev.values; D['oa_b']=ZB.oa_cum.values
D['wt']=-0.4*D.wt_rel.fillna(0)
for v in 'ABC': D['e'+v]=D.wpr-(D.p0+D[v]+D.wt)
D=D[D.eA.notna()]
print('runners',len(D),'| share with intraday oa bias present: %.1f%%'%(D.oa_b.notna().mean()*100))
def rep(name,x):
    print(f'{name:40} n={len(x):6}  RMSE A(no bias) {np.sqrt((x.eA**2).mean()):.4f}  B(intraday) {np.sqrt((x.eB**2).mean()):.4f}  C(full) {np.sqrt((x.eC**2).mean()):.4f}  | MAE A {x.eA.abs().mean():.4f} B {x.eB.abs().mean():.4f} C {x.eC.abs().mean():.4f}')
rep('all',D)
for lo,hi in((0,1),(1,3),(3,6),(6,20)): rep(f'races already run at meeting {lo}-{hi-1}',D[(D.n_prev>=lo)&(D.n_prev<hi)])
rep('has intraday oa bias',D[D.oa_b.notna()])
print('mean |B-A| %.3f  mean |C-A| %.3f  corr(B-A, C-A) %.3f'%((D.B-D.A).abs().mean(),(D.C-D.A).abs().mean(),np.corrcoef(D.B-D.A,D.C-D.A)[0,1]))
x=D[D.oa_b.notna()]; print('on runners with bias: slope of (actual - A-pred) on (B-A): %.3f ; on (C-A): %.3f'%(np.polyfit(x.B-x.A,x.eA,1)[0],np.polyfit(x.C-x.A,x.eA,1)[0]))
