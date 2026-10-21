"""Boxed trifecta / first-four pools built from each rating (the dashboard Rating blend Proj .5 / Nett .3 / Spd .2, Proj, Nett, L3, Spd) and the market's own pool, on the
races since 26 Apr 2026 that have every rating (archived TopRate runner files joined to runners.csv, as in rating_measures2.py). Hit rate against the market-implied hit rate of the same
box (Harville on normalised SP), and estimated return from the dividend model in speed_exotics_select.py (fitted on the real TAB dividends). Caveats: the Proj in the log is mixed
model versions, the sample is about 6,000 races, and an estimated dividend is a screen.
usage: PYTHONPATH=.:research python research/speed_exotics_rating_pools.py
"""
import sys
from datetime import date

import numpy as np
import pandas as pd

import speed_rating as sr
import speed_exotics_select as SEL
from speed_exotics_edge import implied

KEY = ["date", "venue", "race", "horse"]
cols = KEY + ["wpr_nett", "wpr_avg_last3", "wprp_proj", "scratched", "finish_position", "fixed_win_price", "starting_price_sp", "field_source", "spd_fig"]
rd = lambda p: pd.read_csv(p, low_memory=False, usecols=lambda c: c in cols)


def load():
    leg = pd.concat([rd("archive/toprate/toprate_runners_archive.csv.gz"), rd("archive/toprate/toprate_runners.csv")], ignore_index=True)
    cur = pd.concat([rd("runners_archive.csv.gz"), rd("runners.csv")], ignore_index=True)
    for x in (leg, cur):
        x["date"] = x["date"].astype(str).str[:10]
        x["race"] = x["race"].astype(str)
    leg = leg.drop_duplicates(KEY, keep="last").set_index(KEY)
    cur = cur.drop_duplicates(KEY, keep="last").set_index(KEY)
    d = leg.combine_first(cur).reset_index()
    d = d[(d.date >= "2026-04-26") & (d.date <= "2026-10-11")]
    d = d[(d.scratched.fillna(0) != 1) & ~d.field_source.astype(str).str.contains("not in toprate", na=False)].reset_index(drop=True)
    d["spd_calc"] = sr.compute(d, today=date(2026, 5, 24))
    d["spd"] = d.spd_calc.where(d.spd_calc.notna(), pd.to_numeric(d.spd_fig, errors="coerce"))
    d["price"] = pd.to_numeric(d.starting_price_sp, errors="coerce")
    d["price"] = d.price.where(d.price > 1, pd.to_numeric(d.fixed_win_price, errors="coerce"))
    for c in ("wpr_nett", "wpr_avg_last3", "wprp_proj", "finish_position"):
        d[c] = pd.to_numeric(d[c], errors="coerce")
    d["rk"] = d.venue.astype(str) + "|" + d.date + "|" + d.race
    return d


def main():
    d = load()
    fit = SEL.fit_div(SEL.dividend_pairs())
    rows = []
    for rk, g in d.groupby("rk", sort=False):
        if len(g) < 6 or g.price.isna().any() or (g.price <= 1).any():
            continue
        book = (1 / g.price).sum()
        pos = g.finish_position.values
        if not 1.05 <= book <= 2.0 or sorted(pos[pos <= 4].tolist()) != [1, 2, 3, 4]:
            continue
        sigs = {"proj": g.wprp_proj, "nett": g.wpr_nett, "l3": g.wpr_avg_last3, "spd": g.spd}
        if any(s.notna().sum() < len(g) - 1 for s in sigs.values()):
            continue
        z = {}
        for k, s in sigs.items():
            sd = s.std()
            z[k] = ((s - s.mean()) / sd).fillna(0).values if sd and sd > 0 else np.zeros(len(g))
        z["rating"] = 0.5 * z["proj"] + 0.3 * z["nett"] + 0.2 * z["spd"]
        sp = g.price.values
        p = (1 / sp) / book
        z["market"] = -sp
        pos_f = np.where(np.isnan(pos), 99, pos)
        o = list(np.argsort(pos_f, kind="stable")[:4])
        pr, left, h3 = 1.0, 1.0, None
        for j, i in enumerate(o):
            pr *= p[i] / left
            left -= p[i]
            if j == 2:
                h3 = pr
        r = dict(date=g.date.iloc[0], field=len(g), h3=h3, h4=pr, fav=sp.min(), m_ent=float(-(p * np.log(p)).sum() / np.log(len(p))))
        for k, s in z.items():
            order = list(np.argsort(-s, kind="stable"))
            for N in (5, 6):
                pool = order[:N]
                r[f"{k}{N}_tri"] = int((pos_f[pool] <= 3).sum() == 3)
                r[f"{k}{N}_ff"] = int((pos_f[pool] <= 4).sum() == 4)
                r[f"{k}{N}_itri"] = implied(p, pool, 3)
                r[f"{k}{N}_iff"] = implied(p, pool, 4)
            r[f"{k}_n10_5"] = int((sp[order[:5]] > 10).sum())
        rows.append(r)
    R = pd.DataFrame(rows)
    R["ed3"] = SEL.est_div(R.h3, R.field, fit["Trifecta"])
    R["ed4"] = SEL.est_div(R.h4, R.field, fit["FirstFour"])
    print(f"{len(R)} races with every rating, clean book and a clean 1-4 finish, {R.date.min()} to {R.date.max()}")
    rng = np.random.default_rng(1)

    def line(g, hit, ed, cost, ic):
        ret = (g[hit] * g[ed]).values
        roi = ret.sum() / (cost * len(g)) - 1
        bs = [ret[rng.integers(0, len(g), len(g))].sum() / (cost * len(g)) - 1 for _ in range(400)]
        return f"hit {g[hit].mean()*100:5.1f}% (mkt-implied {g[ic].mean()*100:5.1f}%, x{g[hit].sum()/g[ic].sum():.2f}) est ROI {roi*100:+4.0f}% [{np.percentile(bs,5)*100:+.0f},{np.percentile(bs,95)*100:+.0f}]"

    for N, cost_t, cost_f in ((5, 60, 120), (6, 120, 360)):
        print(f"\n== top {N} pools, all races ==")
        for k in ("rating", "proj", "nett", "l3", "spd", "market"):
            print(f"{k:7s} tri ${cost_t}: {line(R, f'{k}{N}_tri', 'ed3', cost_t, f'{k}{N}_itri')}")
            print(f"{'':7s} ff  ${cost_f}: {line(R, f'{k}{N}_ff', 'ed4', cost_f, f'{k}{N}_iff')}")
    print("\n== Rating top 5 with 3+ over $10 ==")
    m = R["rating_n10_5"] >= 3
    for kind, ed, cost in (("tri", "ed3", 60), ("ff", "ed4", 120)):
        print(f"{kind}: n {int(m.sum())} {line(R[m], f'rating5_{kind}', ed, cost, f'rating5_i{kind}')}")
    print("\n== Rating pools in open races (entropy above its 60th percentile, field 10+) ==")
    m = (R.m_ent > R.m_ent.quantile(0.6)) & (R.field >= 10)
    for N, cost_t, cost_f in ((5, 60, 120), (6, 120, 360)):
        print(f"top {N}: n {int(m.sum())}  tri {line(R[m], f'rating{N}_tri', 'ed3', cost_t, f'rating{N}_itri')}\n            ff  {line(R[m], f'rating{N}_ff', 'ed4', cost_f, f'rating{N}_iff')}")
    R.to_csv(sys.argv[1] if len(sys.argv) > 1 else "/dev/null", index=False)


if __name__ == "__main__":
    main()
