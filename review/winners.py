"""Winner-by-winner section of the daily review (Oct 2026). Read-only, changes no model.
For every race winner: price and market rank, where the Proj had it, the rating it earned against the Proj, how it was ridden (800m position, barrier, margin),
gear and weight changes, TopRate Nett and our Spd, the stewards' comment, and a one-line read of why it surprised or did not.
Also tags every runner (style, barrier third, price band, Proj rank, distance, gear change, weight change, age) so the weekly and monthly roll-ups can compare
winners with the whole field and show which kinds of horse win more or less than their share."""
import os
import numpy as np
import pandas as pd

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
COLS = ['run_id', 'gear_changes', 'weight_previous', 'wpr_nett', 'spd_fig', 'horse_age']


def enrich(x, date):
    """x is daily_review.load(date); adds runners.csv facts (matched on run_id) and per-runner tags."""
    r = pd.read_csv(os.path.join(ROOT, 'runners.csv'), usecols=lambda c: c in COLS + ['date'], low_memory=False)
    r = r[r.date == date].drop(columns='date').drop_duplicates('run_id')
    x = x.merge(r, on='run_id', how='left')
    x['mrank'] = x.groupby('race_id').price.rank(method='min')
    x['prank'] = x.groupby('race_id').proj.rank(ascending=False, method='min')
    x['wchg'] = x.weight_carried - x.weight_previous
    x['style'] = pd.cut(x.sf, [0, 0.2, 0.4, 0.7, 1.01], labels=['led or on pace', 'handy', 'midfield', 'back']).astype(object)
    x['bthird'] = pd.cut(x.bf, [0, 1 / 3, 2 / 3, 1.01], labels=['inner barrier', 'middle barrier', 'wide barrier']).astype(object)
    x['pband'] = pd.cut(x.price, [0, 3, 6, 12, 1e9], labels=['under $3', '$3 to $6', '$6 to $12', 'over $12']).astype(object)
    x['rband'] = pd.cut(x.prank, [0, 1, 3, 5, 99], labels=['Proj rank 1', 'Proj rank 2-3', 'Proj rank 4-5', 'Proj rank 6+']).astype(object)
    x['dband'] = pd.cut(x.distance, [0, 1200, 1600, 9999], labels=['up to 1200m', '1201-1600m', 'over 1600m']).astype(object)
    x['gearflag'] = np.where(x.gear_changes.fillna('').astype(str).str.contains('FIRST TIME', case=False), 'gear first time', None)
    x['wband'] = pd.cut(x.wchg, [-99, -1.5, 1.5, 99], labels=['weight down 1.5kg+', 'weight steady', 'weight up 1.5kg+']).astype(object)
    return x


TAGS = ['style', 'bthird', 'pband', 'rband', 'dband', 'gearflag', 'wband']


def tag_stats(x):
    """{tag: {runners, winners}} over runners that finished (non-finishers are not tagged winners or losers)."""
    f = x[x.fin.notna()]
    out = {}
    for c in TAGS:
        for k, g in f.groupby(c):
            out[k] = dict(n=int(len(g)), w=int((g.fin == 1).sum()))
    return out


def move(w):
    """Position change from 800m to 400m and price move (starting price against the top price)."""
    out = []
    if pd.notna(w.p800) and pd.notna(w.p400) and w.p800 != w.p400:
        out.append(f'{int(w.p800)}th at 800m to {int(w.p400)} at 400m')
    if pd.notna(w.ptop) and pd.notna(w.price) and w.ptop > 0 and abs(w.ptop / w.price - 1) >= 0.15:
        out.append(f'price ${w.ptop} top to ${w.price} SP ({"firmed" if w.price < w.ptop else "drifted"})')
    return ', '.join(out)


def read(w):
    notes = []
    if pd.notna(w.prank) and w.prank >= 6:
        notes.append('Proj had it well down' + (', the market had it near the top' if pd.notna(w.mrank) and w.mrank <= 3 else ', and so did the market' if pd.notna(w.mrank) and w.mrank >= 6 else ''))
    elif pd.notna(w.prank) and w.prank <= 2:
        notes.append('Proj had it right')
    if pd.notna(w.miss):
        if w.miss >= 8: notes.append(f'ran {w.miss:.0f} above its Proj')
        elif w.miss <= -8: notes.append(f'won on a rating {-w.miss:.0f} below its Proj')
    if w.style == 'led or on pace' and w.bthird == 'wide barrier': notes.append('crossed from a wide barrier to lead')
    if isinstance(w.gearflag, str): notes.append('gear first time')
    if pd.notna(w.wchg) and abs(w.wchg) >= 3: notes.append(f'weight {w.wchg:+.1f}kg on last start')
    return '; '.join(notes) if notes else 'nothing unusual'


def section(x):
    L = ['## Every winner', '']
    for (venue, race), g in x.groupby(['venue', 'race']):
        w = g[g.fin == 1]
        if w.empty: continue
        w = w.iloc[0]
        n = int(g.run_id.count())
        marg = f', margin {abs(w.margin):.1f}L' if 'margin' in w and pd.notna(w.margin) else ''
        sty = f'{w.style}, ' if isinstance(w.style, str) else ''
        L.append(f"- {venue} R{int(race)} {w.horse} (${w.price}, market rank {int(w.mrank) if pd.notna(w.mrank) else '?'} of {n}; Proj rank {int(w.prank) if pd.notna(w.prank) else 'none'}"
                 + (f', rated {w.miss:+.1f} vs Proj' if pd.notna(w.miss) else '') + f"): {sty}barrier {int(w.barrier) if pd.notna(w.barrier) else '?'}{marg}, "
                 + f"{int(w.distance) if pd.notna(w.distance) else '?'}m {g.going.iloc[0]}, {w.race_class}. "
                 + (f"{w.jockey} / {w.trainer}. " if isinstance(w.jockey, str) else '')
                 + (f"Gear: {w.gear_changes}. " if isinstance(w.gearflag, str) else '')
                 + (f"Nett {w.wpr_nett:.0f}" if pd.notna(w.wpr_nett) else '') + (f", Spd {w.spd_fig:+.1f}L" if pd.notna(w.spd_fig) else '') + '. '
                 + (f"Sectionals vs standard: early {w.sect_e:+.1f}L, last 400m {w.sect_l:+.1f}L. " if pd.notna(w.sect_e) and pd.notna(w.sect_l) else '') + (move(w) + '. ' if move(w) else '')
                 + f"Read: {read(w)}. " + (f"Comment: {str(w.comment)[:110]}. " if isinstance(w.comment, str) and w.comment else '')
                 + (f"Stewards: {str(w.steward)[:110]}" if isinstance(w.steward, str) and w.steward else ''))
    L.append('')
    return L


def beaten_favourites(x):
    """Favourites (shortest price) that lost: where they finished, what they rated against the Proj, how they ran, why."""
    L = ['## Beaten favourites', '']
    k = 0
    for (venue, race), g in x.groupby(['venue', 'race']):
        if g.price.notna().sum() < 3 or (g.fin == 1).sum() != 1: continue
        f = g[g.price == g.price.min()]
        if len(f) != 1: continue
        f = f.iloc[0]
        win = g[g.fin == 1].iloc[0]
        if f.fin == 1: continue
        k += 1
        pos = f"finished {int(f.fin)}" if pd.notna(f.fin) else 'did not finish'
        L.append(f"- {venue} R{int(race)} {f.horse} (${f.price}, Proj rank {int(f.prank) if pd.notna(f.prank) else 'none'}) {pos}"
                 + (f", rated {f.miss:+.1f} vs Proj" if pd.notna(f.miss) else '') + f". {f.style + ', ' if isinstance(f.style, str) else ''}"
                 + (move(f) + '. ' if move(f) else '') + f"Winner {win.horse} (${win.price}, Proj rank {int(win.prank) if pd.notna(win.prank) else 'none'}). "
                 + (f"Comment: {str(f.comment)[:110]}. " if isinstance(f.comment, str) and f.comment else '')
                 + (f"Stewards: {str(f.steward)[:110]}" if isinstance(f.steward, str) and f.steward else ''))
    n = x[x.fin == 1].race_id.nunique()
    L.insert(1, f'{k} of {n} favourites lost.')
    L.append('')
    return L
