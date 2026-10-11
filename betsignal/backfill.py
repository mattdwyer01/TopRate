"""Backfills bet signals for past days into bet_signals_history.json (read once by the dashboard, under the live bet_signals.json).

Two parts, both OUT OF SAMPLE for the days they cover, and both flagged so the dashboard never mixes them with live passes:
  sp    days the results files cover: a model trained only on days BEFORE the window (production features/parameters, 3 seeds) scores the window
        against the closing starting price (the price the 2022 to 2026 backtest used).
  last  days after the results files end (they lag a few days): the production model scores each fully drawn and priced race against the last
        recorded fixed price in toprate_runners.csv. Races containing a horse with a run the history does not hold yet are skipped, as live.
Neither is a price taken before the jump, so the scoreboard keeps them apart from live bets. usage:
  python betsignal/backfill.py [--days 25]   (about 8 minutes)
Compact format: runs[run_id] = [price, model win probability, edge (probability x price), tier 'S'|'V'|'', market rank, source 'sp'|'last']; days[date] = source.
"""
import argparse
import json
import os
import sys
from datetime import datetime, timedelta, timezone

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import numpy as np
import pandas as pd
import lightgbm as lgb

from betsignal import features as F
from betsignal import score as S
from betsignal.train import PARAMS, SEEDS, logit

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, 'bet_signals_history.json')


def part_sp(start, end, meta):
    H = F.load_history()
    cats = meta['cats']
    D = F.batch_features(H, cats)
    tr = D[D.date < start]
    te = D[(D.date >= start) & (D.date <= end)].copy()
    print(f'sp part: training on {len(tr):,} runs before {start.date()}, scoring {len(te):,} runs in {te.race_id.nunique()} races', flush=True)
    raw = 0
    for sd in SEEDS:
        m = lgb.train(dict(PARAMS, seed=sd), lgb.Dataset(tr[F.FEATURES], tr.win, init_score=logit(tr.pm)), meta['rounds'])
        raw = raw + m.predict(te[F.FEATURES], raw_score=True) / len(SEEDS)
    s = raw + logit(te.pm).values
    e = S.win_probabilities(s, te.race_id, te.index).values
    te['pmod'] = e / pd.Series(e, index=te.index).groupby(te.race_id).transform('sum').values
    te['ev'] = te.pmod * te.sp
    te['tier'] = [S.tier(a, b, c) for a, b, c in zip(te.ev, te.sp, te.rank_m)]
    te['tier'] = S.no_first_starter_races(te.tier, te.race_id, te.nruns)
    return te[['race_id', 'horse_id', 'date', 'sp', 'pmod', 'ev', 'tier', 'rank_m']]


def part_last(after, meta):
    import runners_io
    R = runners_io.read_runners()
    boosters = [lgb.Booster(model_file=os.path.join(S.MODELS, f'bet_seed{s}.txt')) for s in meta['seeds']]
    state = S.ensure_state(pd.Timestamp(datetime.now(timezone.utc)))
    through = state['through']
    today = (datetime.now(timezone.utc) + timedelta(hours=10)).strftime('%Y-%m-%d')
    out = []
    for day in sorted(d for d in R.date.unique() if str(after.date()) < str(d) <= today):
        gap = R[(R.date > str(through.date())) & (R.date < day) & (R.scratched != 1)]
        stale = set(pd.to_numeric(gap.horse_id, errors='coerce').dropna().astype(int))
        # every race of the day counts as unstarted; races still to jump are left to the live scorer
        U = S.eligible_rows(R[R.date == day], pd.Timestamp(day, tz='UTC') - pd.Timedelta(days=2), stale)
        U = U[U.start <= pd.Timestamp(datetime.now(timezone.utc)).tz_convert('UTC')]
        if U.empty:
            continue
        X = S.score(U, meta, boosters, state)
        out.append(X[['run_id', 'race_id', 'date', 'sp', 'pmod', 'ev', 'tier', 'rank_m']])
        print(f'last part: {day} scored {len(X)} runners in {X.race_id.nunique()} races, tiers S {int((X.tier == "S").sum())} V {int((X.tier == "V").sum())}', flush=True)
    return pd.concat(out) if out else pd.DataFrame()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--days', type=int, default=25)
    a = ap.parse_args()
    sys.path.insert(0, ROOT)
    import runners_io
    meta = json.load(open(os.path.join(S.MODELS, 'meta.json')))
    last_results = pd.Timestamp(meta['trained_through'])
    start = last_results - pd.Timedelta(days=a.days - 1)

    A = part_sp(start, last_results, meta)
    ids = runners_io.read_runners()[['run_id', 'race_id', 'horse_id']].drop_duplicates('run_id')
    ids['horse_id'] = pd.to_numeric(ids.horse_id, errors='coerce')
    A = A.merge(ids, on=['race_id', 'horse_id'], how='left')
    A = A[A.run_id.notna()]
    B = part_last(last_results, meta)

    runs, days = {}, {}
    for src, X in (('sp', A), ('last', B)):
        if len(X) == 0:
            continue
        for r in X.itertuples():
            runs[str(int(r.run_id))] = [round(float(r.sp), 2), round(float(r.pmod), 4), round(float(r.ev), 3), r.tier, int(r.rank_m), src]
            days[pd.Timestamp(r.date).strftime('%Y-%m-%d')] = src
    out = dict(v=1, made=datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ'), trained_through=meta['trained_through'], days=dict(sorted(days.items())), runs=runs)
    with open(OUT, 'w') as f:
        json.dump(out, f, separators=(',', ':'))
    n_s = sum(1 for v in runs.values() if v[3] == 'S')
    n_v = sum(1 for v in runs.values() if v[3] == 'V')
    print(f'wrote {len(runs):,} runners over {len(days)} days (Select {n_s}, Volume {n_v}); {os.path.getsize(OUT) / 1e6:.1f} MB')


if __name__ == '__main__':
    main()
