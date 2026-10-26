"""Exact ATW offset: the offset on each runner page fetched for a KNOWN race (data/tr_runners/<date>.json.gz, row run_id) = page rating minus the results files' plain
wpr for the same past runs. Joined to that race's conditions (runners.csv) to find the rule. Run with PYTHONPATH=."""
import glob, gzip, json
import numpy as np, pandas as pd
import runners_io
plain = pd.concat([pd.read_csv(f, usecols=['horse_id', 'date', 'wpr'], low_memory=False) for f in sorted(glob.glob('race_results_20[12]*.csv.gz')) if '_rc' not in f])
plain = plain.dropna().drop_duplicates(['horse_id', 'date']).set_index(['horse_id', 'date']).wpr
rows = []
for f in sorted(glob.glob('data/tr_runners/*.json.gz')):
    d = json.load(gzip.open(f, 'rt'))
    for r in d['rows'].values():
        offs = []
        for run in r.get('form') or []:
            if run.get('isBarrierTrial') or run.get('isJumpout') or run.get('wpr') is None: continue
            k = (r['horse_id'], run['date'])
            if k in plain.index: offs.append(run['wpr'] - plain[k])
        if len(offs) >= 2:
            rows.append(dict(file=d['date'], run_id=r['run_id'], horse_id=r['horse_id'], horse=r['horse'], n=len(offs), off=float(np.median(offs)), osd=float(np.std(offs)),
                             foaled=r.get('horse_foaled'), whtoday=r.get('weight_handicap_today'), venue=r.get('venue'), race_no=r.get('race_no'), date=r.get('date')))
O = pd.DataFrame(rows)
print(len(O), 'rows; within-row sd of offset: mean', O.osd.mean(), 'p95', O.osd.quantile(.95))
rn = runners_io.read_runners()
rn['run_id'] = pd.to_numeric(rn.run_id, errors='coerce')
M = O.merge(rn[['run_id', 'distance', 'horse_age', 'horse_sex', 'weight_carried', 'jockey', 'race_class', 'going', 'prize_money', 'state']].drop_duplicates('run_id'), on='run_id', how='left')
M.to_pickle('/tmp/atw_exact.pkl')
print(M.isna().mean())
print(M[['off', 'whtoday', 'weight_carried', 'horse_age']].describe())
