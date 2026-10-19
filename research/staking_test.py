"""Staking schemes instead of flat (19 Oct 2026). For each pick rule: flat $1, equal return (stake 1/price, so a win always returns the same), stake proportional to
price, and fractional Kelly using an uplift over the market-implied chance fitted on the FIRST half of the dates and applied to the SECOND half (out of sample).
ROI = profit / total staked. Live sample: runners.csv 18 Sep onward (Proj, Spd, SP else last fixed). Large sample: results files 2025-07 to 8 Oct 2026, Spd only (SP).
usage: python research/staking_test.py
"""
import os
import sys

import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(__file__))


def schemes(s, uplift=None, kelly_frac=0.25):
    p = s.price.values
    w = s.won.values
    out = {}
    for name, st in (("flat", np.ones(len(s))), ("equal return", 1 / p), ("stake ~ price", p / p.mean())):
        out[name] = (st, (st * (w * p - 1)))
    if uplift is not None:
        ph = np.clip(s.imp.values * uplift, 0, 0.95)
        k = np.clip((ph * p - 1) / (p - 1), 0, None) * kelly_frac
        out["kelly (1/4)"] = (k, k * (w * p - 1))
    return out


def report(s, label, with_kelly=True):
    n = len(s)
    if n < 40:
        print(f"{label:34s} n={n}")
        return
    s = s.sort_values("date")
    h = n // 2
    first, second = s.iloc[:h], s.iloc[h:]
    up = first.won.sum() / first.imp.sum() if with_kelly else None
    print(f"{label:34s} n={n}  wins {int(s.won.sum())}  avg ${s.price.mean():.2f}  win {s.won.mean():.1%} vs implied {s.imp.mean():.1%}  (uplift fitted on 1st half {up:.2f})" if with_kelly else label)
    full = schemes(s)
    for nm, (st, pr) in full.items():
        cum = np.cumsum(pr)
        dd = (np.maximum.accumulate(cum) - cum).max()
        a = pr[:h].sum() / st[:h].sum()
        b = pr[h:].sum() / st[h:].sum()
        print(f"    {nm:14s} ROI {pr.sum() / st.sum():+6.1%}  halves {a:+5.0%}/{b:+5.0%}  profit {pr.sum():+8.1f}u on {st.sum():8.1f}u staked  max drawdown {dd:6.1f}u")
    if with_kelly:
        kk = schemes(second, up)["kelly (1/4)"]
        fl = schemes(second)["flat"]
        st, pr = kk
        print(f"    kelly (1/4) out of sample (2nd half only, n={len(second)}): bets {int((st > 0).sum())}, ROI {pr.sum() / max(st.sum(), 1e-9):+6.1%}, profit {pr.sum():+.2f}u on {st.sum():.2f}u staked  | flat 2nd half ROI {fl[1].sum() / fl[0].sum():+6.1%}")


def live():
    cols = ["date", "venue", "race", "horse", "spd_fig", "wprp_proj", "scratched", "won", "fixed_win_price", "starting_price_sp", "field_source"]
    d = pd.read_csv("runners.csv", low_memory=False, usecols=lambda c: c in cols)
    d = d[(d.date >= "2026-09-18") & (d.scratched.fillna(0) != 1) & ~d.field_source.astype(str).str.contains("not in toprate", na=False)]
    d["rk"] = d.venue.astype(str) + "|" + d.date + "|" + d.race.astype(str)
    d["price"] = pd.to_numeric(d.starting_price_sp, errors="coerce")
    d["price"] = d.price.where(d.price > 1, pd.to_numeric(d.fixed_win_price, errors="coerce"))
    g = d.groupby("rk")
    d = d[(g.won.transform("sum") == 1) & g.won.transform(lambda s: s.notna().all()) & g.price.transform(lambda s: s.notna().all())].copy()
    d["won"] = d.won.astype(int)
    d["book"] = d.groupby("rk").price.transform(lambda s: (1 / s).sum())
    d = d[(d.book >= 1.05) & (d.book <= 2.0)].copy()
    d["imp"] = (1 / d.price) / d.book
    d = d[d.spd_fig.notna() & d.wprp_proj.notna()]
    d = d[d.groupby("rk").spd_fig.transform("size") >= 5]
    d["rp"] = d.groupby("rk").wprp_proj.rank(ascending=False, method="first")
    d["rs"] = d.groupby("rk").spd_fig.rank(ascending=False, method="first")
    print(f"=== LIVE 18 Sep to now: {d.rk.nunique()} races")
    report(d[d.rp == 1], "Proj #1")
    report(d[d.rs == 1], "Spd #1")
    both = d[(d.rp == 1) & (d.rs == 1)]
    report(both, "Proj #1 and Spd #1 (same horse)")
    report(both[(both.price > 2) & (both.price <= 3)], "   same horse, $2-3")
    report(d[(d.rs == 1) & (d.price > 5)], "Spd #1 over $5")
    report(d[(d.rs == 2) & (d.price > 10)], "Spd #2 over $10")


def big():
    import late_speed_study as ls
    h = ls.build()
    h = h[h.date >= "2025-07-01"].copy()
    h["won"] = (h.positionFinish == 1).astype(int)
    h["price"] = pd.to_numeric(h.priceStarting, errors="coerce")
    h = h[h.spd.notna() & h.price.notna() & (h.price > 1)]
    g = h.groupby("race_id")
    h = h[(g.spd.transform("size") >= 5) & (g.won.transform("sum") == 1)].copy()
    h["book"] = h.groupby("race_id").price.transform(lambda s: (1 / s).sum())
    h = h[(h.book >= 1.05) & (h.book <= 2.0)].copy()  # CLAUDE.md 14 Oct: SP books under 1.05 are bad data and fake edges (a Kelly rule selects exactly them)
    h["imp"] = (1 / h.price) / h.book
    h["r"] = h.groupby("race_id").spd.rank(ascending=False, method="first")
    print(f"\n=== RESULTS FILES 2025-07 to 8 Oct 2026, Spd: {h.race_id.nunique()} races")
    report(h[h.r == 1], "Spd #1 any price")
    report(h[(h.r == 1) & (h.price > 5)], "Spd #1 over $5")
    report(h[(h.r == 2) & (h.price > 10)], "Spd #2 over $10")


if __name__ == "__main__":
    live()
    big()
