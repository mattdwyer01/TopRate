"""Builds hierarchical-shrinkage tables of GPS trip outcomes (extra ground, lane, settle, gap to leader at 800m)
by track, distance, barrier group, going bucket and rail bucket. Input: gps_all_h.pkl (VIC/SA + QLD GPS runs joined to results).
Usage: python gps_trip_build.py <gps_all_h.pkl> [--holdout]   (--holdout builds on <2024-07 and reports test-set RMSE vs flat baseline)"""
import sys,json,os,numpy as np,pandas as pd
HERE=os.path.dirname(os.path.abspath(__file__));OUT=os.path.join(HERE,'gps_trip_tables')
T=['extra','lane','settle','gap800'];K={'extra':40,'lane':40,'settle':60,'gap800':60}
LEV=[('band',['band']),('band+bar',['band','bg']),('band+bar+going',['band','bg','gb']),('band+bar+going+rail',['band','bg','gb','rl']),('track+band+bar',['track','band','bg']),('track+dist+bar',['track','dist','bg']),('track+dist+bar+going',['track','dist','bg','gb']),('track+dist+bar+going+rail',['track','dist','bg','gb','rl'])]
def prep(a):
    a=a.copy();a['band']=pd.cut(a.distance,[0,1150,1450,1850,9999],labels=['sprint<=1100','1200-1400','1500-1800','2000+']).astype(str)
    a['bg']=pd.cut(a.barrier,[0,3,6,9,12,99],labels=['1-3','4-6','7-9','10-12','13+']).astype(str)
    a['gb']=pd.cut(a.going_s,[-1,4,7,20],labels=['dry','soft','heavy']).astype(str).replace('nan','syn/unk')
    a['rl']=pd.cut(a.rail_m,[-1,0.5,3,6,9,100],labels=['true','1-3m','4-6m','7-9m','10m+']).astype(str).replace('nan','unk')
    a['dist']=(a.distance/100).round().astype(int)*100;return a
def tables(a):
    out={}
    for t in T:
        x=a[a[t].notna()];lv={'root':pd.DataFrame({'n':[len(x)],'mean':[x[t].mean()]})}
        for name,keys in LEV:lv[name]=x.groupby(keys)[t].agg(n='size',mean='mean').reset_index()
        out[t]=lv
    return out
def predict(tabs,df,t):
    est=np.full(len(df),tabs[t]['root']['mean'].iloc[0])
    for name,keys in LEV:
        m=tabs[t][name].set_index(keys);idx=pd.MultiIndex.from_frame(df[keys]) if len(keys)>1 else pd.Index(df[keys[0]])
        mm=m.reindex(idx);n=mm['n'].fillna(0).values;mu=mm['mean'].values;w=n/(n+K[t]);est=np.where(n>0,w*np.nan_to_num(mu)+(1-w)*est,est)
    return est
if __name__=='__main__':
    a=prep(pd.read_pickle(sys.argv[1]))
    if '--holdout' in sys.argv:
        tr=a[a.date<'2024-07-01'];te=a[a.date>='2024-07-01'];tb=tables(tr)
        for t in T:
            b=te[te[t].notna()];p=predict(tb,b,t);print(t,'flat-mean RMSE %.3f | table RMSE %.3f | sd %.3f'%(np.sqrt(((b[t]-tr[t].mean())**2).mean()),np.sqrt(((b[t]-p)**2).mean()),b[t].std()))
    else:
        tb=tables(a)
        for t in T:
            for name,df in tb[t].items():df.round(3).to_csv(os.path.join(OUT,f'{t}__{name.replace("+","_")}.csv'),index=False)
        print('written',len(os.listdir(OUT)),'tables')
