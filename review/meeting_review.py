"""Meeting-level review of the live Proj against what happened (Oct 2026).
Reads the projection log (rows made before the jump), runners.csv (results, prices, going) and, when it has landed, the runner-page rating (data/tr_form)
for the rating miss. Outcome first: finishing order, where the winner ranked, the 2 / 4 gap lines, the favourite; rating columns fill in as pages land.
Descriptive only: it never changes the model. Run: python review/meeting_review.py 2026-10-17 [--out DIR]"""
import argparse, glob, gzip, json, os
import numpy as np
import pandas as pd

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
INNER, CORE = 4.0, 2.0                      # the dashboard's gap lines from the top Proj


def load(date):
    L = pd.read_csv(os.path.join(ROOT, 'wpr_projection_log.csv.gz'))
    L = L[(L.date == date)].sort_values('made').drop_duplicates('run_id', keep='last')   # latest projection made before the jump
    cols = ['run_id', 'horse_id', 'venue', 'state', 'race', 'race_id', 'distance', 'going', 'track_grading', 'rail_position', 'start_time', 'horse', 'tab_number',
            'barrier', 'jockey', 'scratched', 'won', 'placed', 'finish_position', 'resulted', 'interim_resulted', 'starting_price_sp', 'fixed_win_price', 'margin_finish',
            'wpr_actual', 'race_shape_early', 'comments_steward']
    R = pd.read_csv(os.path.join(ROOT, 'runners.csv'), low_memory=False)
    R = R[[c for c in cols if c in R.columns]]
    x = L.merge(R, on='run_id', how='left')
    x['price'] = x.starting_price_sp.where(x.starting_price_sp > 1, x.fixed_win_price)
    x = x[x.scratched.fillna(0) != 1].copy()
    # runner-page rating of the run, when the horse has been declared again
    rows = []
    for f in sorted(glob.glob(os.path.join(ROOT, 'data', 'tr_form', date[:7] + '*.json.gz'))):
        for r in json.load(gzip.open(f, 'rt'))['runs'].values():
            if r['date'] == date and r.get('wpr') is not None and not r.get('isBarrierTrial'):
                rows.append((int(r['horse_id']), r['wpr'], r.get('position800m'), r.get('positionSettled'), r.get('marginFinish')))
    T = pd.DataFrame(rows, columns=['horse_id', 'page_wpr', 'p800', 'pset', 'mfin'])
    x['horse_id'] = pd.to_numeric(x.horse_id, errors='coerce')
    return x.merge(T.drop_duplicates('horse_id'), on='horse_id', how='left')


def review(x):
    out = []
    for (venue, race), g in x.groupby(['venue', 'race']):
        g = g.copy()
        g['rank'] = g.proj.rank(ascending=False, method='min')
        top = g.proj.max()
        g['gap'] = top - g.proj
        done = g.won.notna().any() and (g.won == 1).any()
        d = dict(venue=venue, race=int(race), n=len(g), rated=int(g.proj.notna().sum()), done=bool(done), going=g.going.iloc[0], dist=g.distance.iloc[0])
        if done:
            w = g[g.won == 1].iloc[0]
            fav = g.loc[g.price.idxmin()] if g.price.notna().any() else None
            tp = g.loc[g.proj.idxmax()]
            d.update(winner=w.horse, w_rank=w['rank'], w_gap=w.gap, w_price=w.price, top_pick=tp.horse, top_lead=float(tp.proj - g.proj.nlargest(2).iloc[-1]) if g.proj.notna().sum() > 1 else np.nan, top_won=bool(tp.won == 1), top_price=tp.price,
                     in2=bool(w.gap <= CORE), in4=bool(w.gap <= INNER), fav_won=bool(fav is not None and fav.won == 1), fav_rank=(fav['rank'] if fav is not None else np.nan),
                     w_model=w.model, w_nruns=w.nruns)
            m = g[g.page_wpr.notna() & g.proj.notna()]
            if len(m) >= 3:
                d.update(miss_mean=float((m.page_wpr - m.proj).mean()), miss_n=len(m))
        out.append(d)
    return pd.DataFrame(out)


def text(date, x, r):
    L = [f'# Meeting review {date}', '']
    for venue, v in r.groupby('venue'):
        dn = v[v.done]
        s0 = x[x.venue == venue].iloc[0]
        L += [f'## {venue} ({s0.state}), going {v.going.iloc[0]}, rail {s0.rail_position}', '']
        if dn.empty:
            L += [f'No resulted races yet ({len(v)} races). Check: results missing or meeting not yet run.', '']; continue
        chk = []
        if len(dn) < len(v): chk.append(f'{len(v) - len(dn)} of {len(v)} races have no result')
        if pd.isna(s0.going): chk.append('going missing')
        thin = v[v.rated < v.n - 1]
        if len(thin): chk.append('races with 2+ unrated runners: ' + ', '.join(f'R{q.race} ({q.n - q.rated} of {q.n})' for _, q in thin.iterrows()))
        long_tp = dn[(dn.top_price >= 30) & (dn.top_lead >= 2)]
        if len(long_tp): chk.append('top Proj priced $30+ with a 2+ lead: ' + ', '.join(f'R{q.race} {q.top_pick} ${q.top_price:.0f}' for _, q in long_tp.iterrows()))
        if chk: L += ['Checks: ' + '; '.join(chk) + '.', '']
        L += [f'Races resulted: {len(dn)} of {len(v)}. Top Proj won {int(dn.top_won.sum())} ({dn.top_won.mean():.0%}); favourite won {int(dn.fav_won.sum())} ({dn.fav_won.mean():.0%}); '
              f'winner inside 2 of the top: {int(dn.in2.sum())}, inside 4: {int(dn.in4.sum())}; mean winner rank {dn.w_rank.mean():.1f}.']
        no_proj = dn[dn.w_rank.isna()]
        if len(no_proj): L.append(f'Winners with no Proj: {len(no_proj)} (' + ', '.join(no_proj.winner) + ').')
        if dn.miss_mean.notna().any():
            L.append(f'Rating miss where page ratings have landed: mean {dn.miss_mean.mean():+.1f} over {int(dn.miss_n.sum())} runs (+ = ran better than Proj).')
        L += ['', '| R | Winner | Rank | Gap | SP | Top Proj (result) | Fav rank |', '|---|---|---|---|---|---|---|']
        for _, q in dn.iterrows():
            L.append(f"| {q.race} | {q.winner} | {q.w_rank:.0f} | {q.w_gap:.1f} | {q.w_price:.2f} | {q.top_pick} ({'won' if q.top_won else 'lost'} @ {q.top_price:.2f}) | {q.fav_rank:.0f} |")
        sur = dn[(dn.w_gap > 8) | (dn.w_rank >= 6)]
        L += ['', 'Biggest surprises (winner 8+ off the top or ranked 6th or worse): ' + ('; '.join(f"R{q.race} {q.winner} (rank {q.w_rank:.0f}, gap {q.w_gap:.1f}, ${q.w_price:.2f}, {q.w_model} model, {q.w_nruns:.0f} prior runs)" for _, q in sur.iterrows()) or 'none') + '.', '']
    return '\n'.join(L)


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('date'); ap.add_argument('--out')
    a = ap.parse_args()
    x = load(a.date); r = review(x); t = text(a.date, x, r)
    if a.out:
        os.makedirs(a.out, exist_ok=True); open(os.path.join(a.out, a.date + '.md'), 'w').write(t)
    print(t)
