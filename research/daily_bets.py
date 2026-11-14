"""Daily bet list for the owner's manual betting rules (13 Nov 2026). Research tool: places no bets, writes nothing to the repo.

Usage, from the repo root after pulling the latest main:  python research/daily_bets.py 2026-11-14 [--from 13:00]
Needs node 22+ (computes the dashboard Rating with frontend/src/lib/raceModel.ts itself, so the Rating matches the race page).

Rules (see research/DAILY_BETS.md for the reasons and the running results):
  WIN      $50 fixed price: Rating #1 leads #2 by 2+ points, price over $2, no first starter or 1-2 run horse in the race, not a bush meeting.
  VOLUME   v2 from volume_rules.py ($25 a race split, settled at Betfair SP), minus any horse that is also the win bet (win bet only).
  QUADDIE  $25 flexi: each leg = within 2 Rating points of the top, plus within 6 forecast in the first half of the trip map; if the
           ticket is over 600 combinations every leg uses within 4 instead. Meeting's biggest race $40k+, no first starter in any leg
           (checked on the projection log, nruns == 0), legs average 8+ runners. Early quaddie ends on race max(4, N-4), late on the last.
  WATCH    volume_rules.v2_watch: runners near the $3 floor and what changes if they cross it.
"""
import glob, gzip, json, os, shutil, subprocess, sys, tempfile
from datetime import datetime
from zoneinfo import ZoneInfo

import numpy as np
import pandas as pd

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, ROOT)
os.chdir(ROOT)
import volume_rules as V  # noqa: E402

MEL = ZoneInfo('Australia/Melbourne')
WIN_LEAD, WIN_MIN_PRICE = 2.0, 2.0
Q_ANY, Q_HALF, Q_HALF_FALLBACK, Q_MAX_COMBOS = 2.0, 6.0, 4.0, 600
Q_MIN_TOP_PRIZE, Q_MIN_AVG_FIELD, BUSH_MAX_PRIZE = 40000, 8.0, 20000
# Heavy tracks (14 Nov 2026, owner's call): every bet at a meeting rated Heavy 8 or worse is staked at half. Basis (stand-ins, 2024 to 8 Oct 2026):
# Volume v2 lost 15.7% on 1,033 heavy races against about 7% on good and soft; the rating misses by 11.8 points on heavy against 8.4 on good.
HEAVY_FROM, HEAVY_FACTOR = 8, 0.5


def heavy_venues(day):
    """venues whose going (runners.csv, TAB's reading) is Heavy 8 or worse on the day"""
    R = V.read_runners(day)
    n = pd.to_numeric(R.going.astype(str).str.extract(r'(\d+)')[0], errors='coerce')
    return set(R.venue[n >= HEAVY_FROM])


def mel(s):
    return pd.Timestamp(s).tz_convert(MEL) if pd.Timestamp(s).tzinfo else pd.Timestamp(s).tz_localize('UTC').tz_convert(MEL)


def load(day):
    p = json.load(open('toprate_data.json'))
    races = [x for x in p['RACES'] if x['date'] == day]
    L = pd.read_csv('wpr_projection_log.csv.gz', low_memory=False)
    L = L[L.date.astype(str) == day]
    proj = dict(zip(L.run_id.astype(str), pd.to_numeric(L.proj, errors='coerce')))
    nruns = dict(zip(L.run_id.astype(str), pd.to_numeric(L.nruns, errors='coerce')))
    model = dict(zip(L.run_id.astype(str), L.model))
    for x in races:   # the payload can lag the projection log (it is refreshed by the poller), so the log wins
        for u in x['runners']:
            v = proj.get(str(u['rid']))
            if v is not None and v == v:
                u['wpjp'] = float(v)
    return p, races, proj, nruns, model


def gaps_table():
    g = {}
    for f in sorted(glob.glob('data/trip_map_archive/*.json.gz')):
        for v in json.load(gzip.open(f))['races'].values():
            for r in v['runners']:
                if r.get('gap') is not None:
                    g[str(r['rid'])] = r['gap']
    for v in json.load(open('trip_map.json'))['races'].values():
        for r in v['runners']:
            if r.get('gap') is not None:
                g[str(r['rid'])] = r['gap']
    return g


def ratings(races, beta):
    """Dashboard Rating per runner via the frontend's own computeEffectiveRace (node, TypeScript stripped)."""
    tmp = tempfile.mkdtemp()
    for f in ('raceModel.ts', 'ratedPrice.ts'):
        s = open(f'frontend/src/lib/{f}').read().replace("from './ratedPrice'", "from './ratedPrice.ts'")
        open(os.path.join(tmp, f), 'w').write(s)
    open(os.path.join(tmp, 'run.ts'), 'w').write("""
import fs from 'node:fs'
import { computeEffectiveRace } from './raceModel.ts'
const inp = JSON.parse(fs.readFileSync(process.argv[2], 'utf8'))
const out: Record<string, number | null> = {}
for (const x of inp.races) {
  const R = x.runners.map((r: any) => ({ runId: r.rid, projectedWpr: r.wpjp ?? null, atwOffset: null, nett: null, projectionSd: r.wpjsd ?? null,
    directChance: r.dm > 0 ? r.dm : null, projectionModel: r.wpjm, projectionContributions: null }))
  const eff = computeEffectiveRace(R as any, {}, {}, inp.beta, new Set<string>())
  for (const r of x.runners) out[r.rid] = eff[r.rid]?.effectiveProjectedWpr ?? null
}
fs.writeFileSync(process.argv[3], JSON.stringify(out))
""")
    live = [dict(rid=str(x['race_id']), runners=[u for u in x['runners'] if not u.get('scr')]) for x in races]
    json.dump(dict(races=live, beta=beta), open(os.path.join(tmp, 'in.json'), 'w'))
    subprocess.run(['node', '--experimental-strip-types', '--no-warnings', 'run.ts', 'in.json', 'out.json'], cwd=tmp, check=True)
    out = json.load(open(os.path.join(tmp, 'out.json')))
    shutil.rmtree(tmp, ignore_errors=True)
    return out


def main():
    day = sys.argv[1]
    since = sys.argv[sys.argv.index('--from') + 1] if '--from' in sys.argv else None
    p, races, proj, nruns, model = load(day)
    heavy = heavy_venues(day)
    gaps = gaps_table()
    starts = {}   # (venue, horse) -> TopRate career starts, from data/tr_fields/<day>.json
    try:
        for r in json.load(open(f'data/tr_fields/{day}.json')).get('rows', []):
            if r.get('career_starts') is not None:
                starts[(str(r.get('venue', '')).lower(), str(r.get('horse', '')).lower())] = int(r['career_starts'])
    except Exception:
        pass
    rt = ratings(races, p['PRICE_BETA'])
    top_prize = {}
    for x in races:
        if x.get('prize') is not None:
            top_prize[x['venue']] = max(top_prize.get(x['venue'], 0), float(x['prize']))

    info, rows, winsel = {}, [], set()
    for x in races:
        L = [u for u in x['runners'] if not u.get('scr')]
        n = len(L)
        # a runner counts as a first starter (no rating, nruns 0 or a debut estimate) only if TopRate's field file does not show earlier starts (14 Nov 2026: Sha Tin R5
        # #7 Highland Cross had 1 start and no rating, which wrongly ruled out the early quaddie)
        first = any((nruns.get(str(u['rid'])) == 0 or u.get('wpjm') == 'debut' or u.get('wpjp') is None)
                    and not starts.get((x['venue'].lower(), str(u.get('h') or '').lower())) for u in L)
        light = any(model.get(str(u['rid'])) != 'main' or nruns.get(str(u['rid'])) == 0 for u in L)
        rated = sorted([u for u in L if rt.get(str(u['rid'])) is not None and nruns.get(str(u['rid'])) != 0],
                       key=lambda u: -rt[str(u['rid'])])
        gs = sorted(gaps[str(u['rid'])] for u in L if str(u['rid']) in gaps)
        pools = {}
        if len(rated) >= 2:
            top = rt[str(rated[0]['rid'])]
            for half in (Q_HALF, Q_HALF_FALLBACK):
                pool = []
                for u in rated:
                    off = top - rt[str(u['rid'])]
                    g = gaps.get(str(u['rid']))
                    rk = (sum(1 for v in gs if v < g) + 1) if g is not None else None
                    in_half = rk is not None and n > 1 and (rk - 1) / (n - 1) <= 0.5 + 1e-9
                    if off <= Q_ANY or (off <= half and in_half):
                        pool.append(u.get('tab'))
                pools[half] = pool
            lead = top - rt[str(rated[1]['rid'])]
            tp = rated[0]
            bush = top_prize.get(x['venue'], 1e9) <= BUSH_MAX_PRIZE
            if lead >= WIN_LEAD and not first and not light and (tp.get('fx') or 0) > WIN_MIN_PRICE and not bush:
                winsel.add((x['venue'], x['race'], tp.get('tab')))
                rows.append((mel(x['start_time']), 'WIN', f"{x['venue']} R{x['race']}",
                             f"#{tp.get('tab')} {tp['h']} ${tp.get('fx'):.2f} (lead {lead:.1f}, ${50 * (HEAVY_FACTOR if x['venue'] in heavy else 1):g}{', heavy, half stake' if x['venue'] in heavy else ''})"))
        info[(x['venue'], x['race'])] = dict(x=x, n=n, first=first, pools=pools, undeclared=any((u.get('tab') or 0) <= 0 for u in L))

    for v in sorted({k[0] for k in info}):
        rs = {r: i for (vv, r), i in info.items() if vv == v}
        N = max(rs)
        sets = [('late', [N - 3, N - 2, N - 1, N])] if N >= 4 else []
        if N >= 6:
            e = max(4, N - 4)
            sets.insert(0, ('early', [e - 3, e - 2, e - 1, e]))
        for nm, legs in sets:
            if any(l not in rs for l in legs):
                continue
            I = [rs[l] for l in legs]
            label = f"{v} {nm} R{legs[0]}-R{legs[-1]}"
            why = None
            if top_prize.get(v, 0) < Q_MIN_TOP_PRIZE:
                why = 'biggest race under $40k'
            elif any(i['first'] for i in I):
                why = 'first starter in R' + ','.join(str(l) for l, i in zip(legs, I) if i['first'])
            elif np.mean([i['n'] for i in I]) < Q_MIN_AVG_FIELD:
                why = f"legs average {np.mean([i['n'] for i in I]):.2f} runners"
            elif any(i['undeclared'] or not i['pools'] for i in I):
                why = 'field not declared or not rated'
            if why:
                print(f"no quaddie {label}: {why}", file=sys.stderr)
                continue
            c6 = int(np.prod([len(i['pools'][Q_HALF]) for i in I]))
            use, tag = Q_HALF, 'within 6'
            if c6 > Q_MAX_COMBOS:
                use, tag = Q_HALF_FALLBACK, f'within 4 fallback ({c6} combos at 6)'
            c = int(np.prod([len(i['pools'][use]) for i in I]))
            sel = ' / '.join(','.join(str(t) for t in i['pools'][use]) for i in I)
            qf = HEAVY_FACTOR if v in heavy else 1
            rows.append((mel(I[0]['x']['start_time']), 'QUADDIE', label, f"{sel}  [{c} combos, {tag}, ${25 * qf:g} flexi {100 * 25 * qf / c:.1f}%{', heavy, half stake' if qf < 1 else ''}]"))

    R = V.read_runners(day)
    rid = pd.to_numeric(R.run_id, errors='coerce').astype('Int64').astype(str)
    R['wprp_proj'] = rid.map(proj).fillna(pd.to_numeric(R.wprp_proj, errors='coerce'))
    R['wprp_model'] = [('debut' if nruns.get(r) == 0 else m) for r, m in zip(rid, R.wprp_model)]
    b, _ = V.evaluate(R, gaps, 'fixed', V.read_overrides(), None)
    v2 = b[b.v2]
    for (_, st), g in v2.groupby(['race_id', 'start_time']):
        g = g[[(x.venue, int(x.race), int(x.tab_number)) not in winsel for x in g.itertuples()]].sort_values('price')
        if g.empty:
            continue
        rows.append((mel(st), 'VOLUME v2', f"{g.venue.iloc[0]} R{int(g.race.iloc[0])}",
                     ', '.join(f"#{int(x.tab_number)} {x.horse} ${x.price:g}" for x in g.itertuples()) + f"  (${25 * (HEAVY_FACTOR if g.venue.iloc[0] in heavy else 1) / len(g):.2f} each, Betfair SP{', heavy, half stake' if g.venue.iloc[0] in heavy else ''})"))
    for line in V.v2_watch(R, b, gaps, V.read_overrides(), None):
        t = line.strip().split(' ')[0]
        head = line.strip().split(' ', 1)[1].split(':')[0]          # "Venue R6"
        wv, _, wr = head.rpartition(' R')
        if any((wv, int(wr), tab) in winsel and f"drop [#{tab} " in line for tab in range(1, 30)):
            continue     # same horse as the win bet, there is no Volume bet on it to watch
        hh = datetime.strptime(t, '%I:%M%p')
        rows.append((datetime.combine(datetime.fromisoformat(day), hh.time(), tzinfo=MEL), 'WATCH', '', line.strip().split(' ', 1)[1]))

    order = {'QUADDIE': 0, 'WIN': 1, 'VOLUME v2': 2, 'WATCH': 3}
    rows.sort(key=lambda r: (pd.Timestamp(r[0]), order[r[1]]))
    cut = datetime.combine(datetime.fromisoformat(day), datetime.strptime(since, '%H:%M').time(), tzinfo=MEL) if since else None
    print(f"payload {p['RUN_ISO']}  projection log made up to {pd.read_csv('wpr_projection_log.csv.gz', usecols=['made']).made.max()}")
    for t, k, race, txt in rows:
        if cut is not None and pd.Timestamp(t) < pd.Timestamp(cut):
            continue
        print(f"{pd.Timestamp(t).strftime('%-I:%M')} | {k:9s} | {race:28s} | {txt}")


if __name__ == '__main__':
    main()
