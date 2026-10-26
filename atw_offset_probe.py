"""Probe (26 Oct 2026): is the runner page of a PAST run id rated for that run's own race, and what is the ATW offset by month?

Known rule (CLAUDE.md, atw_offset_exact.py): page rating = plain results wpr + 0.8 x (W_std - W), W the weight carried after the apprentice claim, W_std the
weight-for-age scale weight of the race (age, sex, month, distance). The offset was only measurable for 18 to 27 Oct 2026, because those pages were fetched
for known upcoming races. This fetches the page of a sample of HISTORICAL run ids (results files, stratified by month) and records, per page, the offset
against the results files' plain wpr together with that run's own weight, age, sex, distance and date, and the page's own `weightHandicap`.
The question it answers: when the page's weightHandicap equals the historical run's weight, the page is rated for that run's race and the offset gives W_std
for that month and distance; when it does not, the page is rated for the horse's CURRENT next race and the sample is useless for months (the diagnostic printed says which).

Output: data/atw_probe/<tag>.json.gz ({rows: [...]}). Needs TOPRATE_EMAIL, TOPRATE_PASSWORD, TOPRATE_ANON_KEY.
Usage: python atw_offset_probe.py --from 2023-01 --to 2026-09 --per-month 40 [--seed 1] [--tag probe1] [--workers 3]
"""
import argparse
import glob
import gzip
import json
import os
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import numpy as np
import pandas as pd

import toprate_race_fetch as f
import toprate_runner_fetch as rf

OUT = Path(__file__).parent / "data" / "atw_probe"


def load_results():
    cols = ['run_id', 'horse_id', 'date', 'wpr', 'weightCarried', 'distance', 'horse_age', 'horse_sex', 'isBarrierTrial', 'is_jumpout', 'race_class', 'track']
    d = pd.concat([pd.read_csv(p, usecols=lambda c: c in cols, low_memory=False) for p in sorted(glob.glob('race_results_20[12]*.csv.gz')) if '_rc' not in p])
    d['date'] = d.date.astype(str).str[:10]
    return d


def sample(d, start, end, per_month, seed):
    s = d[(d.isBarrierTrial.astype(str) != 'True') & (d.is_jumpout.astype(str) != 'True')].dropna(subset=['run_id', 'wpr', 'weightCarried', 'distance', 'horse_age'])
    s = s[~s.race_class.astype(str).str.contains('Hurdle|Steeple', case=False)]
    s = s[(s.run_id < 7_000_000_000_000) & (s.date.str[:7] >= start) & (s.date.str[:7] <= end)]
    s = s.assign(mo=s.date.str[:7])
    return s.groupby('mo', group_keys=False).apply(lambda x: x.sample(min(per_month, len(x)), random_state=seed)).reset_index(drop=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--from', dest='start', default='2023-01')
    ap.add_argument('--to', dest='end', default='2026-09')
    ap.add_argument('--per-month', type=int, default=40)
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--tag', default='probe1')
    ap.add_argument('--workers', type=int, default=3)
    ap.add_argument('--limit', type=int, default=0)
    a = ap.parse_args()
    d = load_results()
    plain = d.dropna(subset=['wpr', 'horse_id']).drop_duplicates(['horse_id', 'date'])
    plain['horse_id'] = pd.to_numeric(plain.horse_id, errors='coerce')
    pmap = plain.set_index(['horse_id', 'date']).wpr.to_dict()
    S = sample(d, a.start, a.end, a.per_month, a.seed)
    if a.limit:
        S = S.head(a.limit)
    print(f'{len(S)} historical run ids over {S.mo.nunique()} months', flush=True)
    email, password, anon = (os.environ[k].strip() for k in ('TOPRATE_EMAIL', 'TOPRATE_PASSWORD', 'TOPRATE_ANON_KEY'))
    session = f.login(email, password, anon)
    rows, failed, empty = [], 0, 0
    items = list(S.itertuples())
    for i in range(0, len(items), 300):
        chunk = items[i:i + 300]
        if session.get('expires_at', 0) - time.time() < 600:
            session = f.login(email, password, anon)
        with ThreadPoolExecutor(max_workers=a.workers) as ex:
            res = list(ex.map(lambda r: (r, *rf.fetch_runner(session, int(r.run_id))), chunk))
        for r, rd, err in res:
            if rd is None:
                failed += 1
                continue
            if rd.get('empty'):
                empty += 1
                continue
            offs = []
            for run in rd.get('form') or []:
                if run.get('isBarrierTrial') or run.get('isJumpout') or run.get('wpr') is None:
                    continue
                k = (float(r.horse_id), run['date'])
                if k in pmap:
                    offs.append(run['wpr'] - pmap[k])
            dates = [x.get('date') for x in (rd.get('form') or []) if x.get('date')]
            rows.append(dict(run_id=int(r.run_id), horse_id=int(r.horse_id), date=r.date, wt=float(r.weightCarried), dist=float(r.distance), age=float(r.horse_age),
                             sex=str(r.horse_sex), n=len(offs), off=float(np.median(offs)) if offs else None, osd=float(np.std(offs)) if offs else None,
                             page_wh=rd.get('weightHandicap'), page_foaled=rd.get('horseFoaled'), last_form=max(dates) if dates else None,
                             first_form=min(dates) if dates else None))
        print(f'  {min(i + 300, len(items))}/{len(items)} fetched, failed {failed}, empty {empty}, kept {len(rows)}', flush=True)
    OUT.mkdir(parents=True, exist_ok=True)
    path = OUT / f'{a.tag}.json.gz'
    with gzip.GzipFile(path, 'wb', mtime=0) as gz:
        gz.write(json.dumps({'rows': rows}, separators=(',', ':')).encode())
    R = pd.DataFrame(rows)
    R['page_wh'] = pd.to_numeric(R.page_wh, errors='coerce')
    ok = R.dropna(subset=['page_wh'])
    print('pages', len(R), 'with a page weight', len(ok))
    print('page weightHandicap equals that run\'s weight:', round(float((ok.page_wh == ok.wt).mean()), 3))
    print('mean |page_wh - run weight|', round(float((ok.page_wh - ok.wt).abs().mean()), 2))
    print('within-page sd of offset: mean', round(float(R.osd.mean()), 3))
    print('last form date vs run date (page lists runs after the run):', round(float((R.last_form > R.date).mean()), 3))
    R['mo'] = R.date.str[5:7]
    print(R.groupby('mo').off.agg(['count', 'mean']).round(2).to_string())


if __name__ == '__main__':
    main()
