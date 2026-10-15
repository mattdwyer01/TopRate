"""Rated price calibration: softmax vs simulation (14 Oct 2026, read-only research script).

Question: the dashboard's Rated $ is a softmax of the projected ratings (beta 0.20). Would simulating each runner's rating with noise that depends
on the runner's record (and reading win AND place chances off the simulation) give better calibrated chances, and do overlays against the rated
price pay?

The real projection has no history yet (its log restarted 12 Oct 2026), so a STAND-IN rating is used: a linear model of the rating the horse will
run, from its own earlier ratings (w1, w2, w3, career mean and best, spell, weight, barrier, age), fitted on years before the test year.
It is weaker than the LightGBM projection, so the point is the comparison of ways of turning ratings into chances, not the absolute numbers.
Races with a first starter are left out (no stand-in rating for them). Clean-book races only (SP book 1.05 to 1.5). Walk-forward 2023 to 2026.

  A  softmax          p ~ exp(beta r)                      beta fitted by maximum likelihood on earlier years
  B  simulation, one noise level for every runner (normal)  noise sd fitted on earlier years
  C  simulation, noise by runner type (starts, spell)       sd by type measured on earlier years, one scale fitted
  M  calibrated market (one slope on log SP), as the yardstick

Win chances for B and C by numerical integration (exact), place chances by Monte Carlo (3 places for 8+ runners, 2 for 5 to 7) on a sample of races.

  python betsignal/rated_price_sim.py
"""
import os
import sys
import time

import numpy as np
import pandas as pd
from scipy.optimize import minimize_scalar
from scipy.special import log_ndtr

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
CACHE = os.environ.get("TUNE_CACHE", "/tmp/tune_cache")
TEST_YEARS = (2023, 2024, 2025, 2026)
PLACE_SAMPLE_RACES, PLACE_SIMS = 20000, 2000
RNG = np.random.default_rng(7)
COLS = ["race_id", "year", "win", "fin", "sp", "pm", "nruns", "w1", "w2", "w3", "wavg_all", "wbest", "days", "wt_rel", "bar_rel", "horse_age",
        "dist_ch", "wpr"]


def load():
    F = pd.read_pickle(f"{CACHE}/feat.pkl")[COLS].copy()
    book = (1 / F.sp).groupby(F.race_id).transform("sum")
    F = F[(book >= 1.05) & (book <= 1.5)]
    # no first starters and every runner has a last-start rating
    ok = F.groupby("race_id").apply(lambda g: (g.nruns >= 1).all() and g.w1.notna().all())
    F = F[F.race_id.isin(ok[ok].index)]
    return F.sort_values("race_id", kind="mergesort").reset_index(drop=True)


def design(F):
    w1 = F.w1.values
    w2 = np.where(F.w2.notna(), F.w2, w1)
    w3 = np.where(F.w3.notna(), F.w3, w2)
    X = np.column_stack([np.ones(len(F)), w1, w2, w3, F.wavg_all.fillna(F.w1).values, F.wbest.fillna(F.w1).values,
                         np.log1p(np.clip(F.days.fillna(30).values, 0, 400)), np.minimum(F.nruns.values, 30) / 10.0, F.wt_rel.fillna(0).values,
                         F.bar_rel.fillna(0.5).values, F.horse_age.fillna(4).values, np.clip(F.dist_ch.fillna(0).values, -800, 800) / 200.0])
    return X


def race_index(F):
    start = np.flatnonzero(np.r_[True, F.race_id.values[1:] != F.race_id.values[:-1]])
    size = np.diff(np.r_[start, len(F)])
    return start, size


def race_demean(v, start, size):
    rid = np.repeat(np.arange(len(start)), size)
    cnt = np.add.reduceat(~np.isnan(v), start)
    mean = np.add.reduceat(np.nan_to_num(v), start) / np.maximum(cnt, 1)
    return v - mean[rid]


def group_of(F):
    n = F.nruns.values
    g = np.where(n <= 2, 0, np.where(n <= 5, 1, np.where(n <= 11, 2, 3)))
    return g + 4 * (F.days.fillna(30).values > 100)


def by_size(start, size):
    for n in np.unique(size):
        idx = np.flatnonzero(size == n)
        yield int(n), idx, start[idx][:, None] + np.arange(n)[None, :]


def win_probs(mu, s):
    """Exact win probabilities for independent normals, by quadrature. mu, s: (R, n)."""
    R, n = mu.shape
    G = 256
    lo, hi = (mu - 6 * s).min(1), (mu + 6 * s).max(1)
    x = lo[:, None] + (hi - lo)[:, None] * np.linspace(0, 1, G)[None, :]
    z = (x[:, None, :] - mu[:, :, None]) / s[:, :, None]
    lc = log_ndtr(z)
    tot = lc.sum(1)
    integ = np.exp(-0.5 * z * z) / (np.sqrt(2 * np.pi) * s[:, :, None]) * np.exp(tot[:, None, :] - lc)
    dx = (hi - lo) / (G - 1)
    p = (integ.sum(2) - 0.5 * (integ[:, :, 0] + integ[:, :, -1])) * dx[:, None]
    return p / p.sum(1, keepdims=True)


def win_probs_all(F_mu, F_s, start, size, chunk=1500):
    out = np.zeros(len(F_mu))
    for n, idx, pos in by_size(start, size):
        for a in range(0, len(idx), chunk):
            p = pos[a:a + chunk]
            out[p] = win_probs(F_mu[p], F_s[p])
    return out


def softmax_probs(r, beta, start, size):
    rid = np.repeat(np.arange(len(start)), size)
    z = beta * r
    e = np.exp(z - np.maximum.reduceat(z, start)[rid])
    return e / np.add.reduceat(e, start)[rid]


def winner_ll(p, win, start):
    return float(np.log(np.clip(p[win == 1], 1e-9, 1)).mean())


def place_probs(mu, noise_fn, n, places):
    """Monte Carlo chance of finishing in the first `places`. mu (R, n)."""
    R = mu.shape[0]
    out = np.zeros((R, n))
    step = max(1, int(25e6 // (PLACE_SIMS * n)))
    for a in range(0, R, step):
        m = mu[a:a + step]
        v = m[:, None, :] + noise_fn(m.shape[0], PLACE_SIMS, n, a)
        thr = -np.partition(-v, places - 1, axis=2)[:, :, places - 1:places]
        out[a:a + step] = (v >= thr).mean(1)
    return out


def roi(bets):
    if not len(bets):
        return (0, np.nan, np.nan, np.nan)
    ex10 = bets.drop(bets[bets.win == 1].nlargest(10, "sp").index) if len(bets) > 20 else bets
    return (len(bets), bets.win.mean() * 100, (bets.sp * bets.win).mean() * 100 - 100, (ex10.sp * ex10.win).mean() * 100 - 100)


def main():
    t0 = time.time()
    F = load()
    print(f"races {F.race_id.nunique():,} (clean books, no first starters), runners {len(F):,} ({time.time()-t0:.0f}s)", flush=True)
    X = design(F)
    y = F.wpr.values
    start_all, size_all = race_index(F)
    G = group_of(F)
    rows = []
    store = []
    for ty in TEST_YEARS:
        tr = (F.year.values <= ty - 1)
        te = (F.year.values == ty)
        ok = tr & ~np.isnan(y)
        b, *_ = np.linalg.lstsq(X[ok], y[ok], rcond=None)
        r = X @ b                                            # stand-in rating
        # sub-frames keep races whole (sorted by race_id, year is constant within a race)
        def sub(mask):
            S = F[mask].reset_index(drop=True)
            return S, race_index(S)
        Ftr, (s_tr, z_tr) = sub(tr)
        Fte, (s_te, z_te) = sub(te)
        r_tr, r_te = r[tr], r[te]
        g_tr, g_te = G[tr], G[te]
        # noise by runner type: within-race demeaned residual sd on training runs with a known rating
        res = np.where(np.isnan(y[tr]), np.nan, y[tr] - r_tr)
        res = race_demean(res, s_tr, z_tr)
        sd_g = np.array([np.nanstd(res[g_tr == k]) if (g_tr == k).sum() > 200 else np.nan for k in range(8)])
        sd_g = np.where(np.isnan(sd_g), np.nanmean(sd_g), sd_g)
        # A: beta by maximum likelihood on a training sample
        sample = RNG.choice(len(s_tr), size=min(14000, len(s_tr)), replace=False)
        sample.sort()
        rows_s = np.concatenate([np.arange(s_tr[i], s_tr[i] + z_tr[i]) for i in sample])
        sub_F = Ftr.iloc[rows_s].reset_index(drop=True)
        s_s, z_s = race_index(sub_F)
        r_s, g_s = r_tr[rows_s], g_tr[rows_s]
        r_s_c = r_s - np.repeat(np.add.reduceat(r_s, s_s) / z_s, z_s)
        beta = minimize_scalar(lambda bb: -winner_ll(softmax_probs(r_s_c, bb, s_s, z_s), sub_F.win.values, s_s), bounds=(0.02, 0.6), method="bounded").x
        # B: one noise level; C: sd by type times one scale
        def ll_sim(sd_vec):
            return winner_ll(win_probs_all(r_s_c, sd_vec, s_s, z_s), sub_F.win.values, s_s)
        sB = minimize_scalar(lambda v: -ll_sim(np.full(len(r_s_c), v)), bounds=(3, 14), method="bounded", options={"xatol": 0.15}).x
        kC = minimize_scalar(lambda k: -ll_sim(k * sd_g[g_s]), bounds=(0.4, 1.6), method="bounded", options={"xatol": 0.03}).x
        print(f"\n== test {ty}: beta {beta:.3f} (noise sd equivalent {np.pi/np.sqrt(6)/beta:.1f}), B sd {sB:.2f}, C scale {kC:.2f}, sd by type "
              f"{np.round(kC*sd_g,1)}  ({time.time()-t0:.0f}s)", flush=True)
        # test year probabilities
        r_te_c = r_te - np.repeat(np.add.reduceat(r_te, s_te) / z_te, z_te)
        pA = softmax_probs(r_te_c, beta, s_te, z_te)
        pB = win_probs_all(r_te_c, np.full(len(r_te_c), sB), s_te, z_te)
        pC = win_probs_all(r_te_c, kC * sd_g[g_te], s_te, z_te)
        Fte = Fte.assign(pA=pA, pB=pB, pC=pC)
        # calibrated market on the same races (one slope on log pm, fitted on training)
        lpm_tr = np.log(Ftr.pm.values)
        lpm_tr_c = lpm_tr
        sl = minimize_scalar(lambda a: -winner_ll(softmax_probs(a * lpm_tr_c, 1.0, s_tr, z_tr), Ftr.win.values, s_tr), bounds=(0.5, 2.0), method="bounded").x
        Fte["pM"] = softmax_probs(sl * np.log(Fte.pm.values), 1.0, s_te, z_te)
        # place chances on a sample of test races
        samp = np.sort(RNG.choice(len(s_te), size=min(PLACE_SAMPLE_RACES // len(TEST_YEARS), len(s_te)), replace=False))
        pl = {k: [] for k in "ABC"}
        act = []
        for n, idx, pos in by_size(s_te, z_te):
            sel = np.intersect1d(idx, samp)
            if not len(sel):
                continue
            pp = s_te[sel][:, None] + np.arange(n)[None, :]
            places = 3 if n >= 8 else 2
            mu = r_te_c[pp]
            sg = (kC * sd_g[g_te])[pp]
            pl["A"].append(place_probs(mu, lambda R, S, nn, a: RNG.gumbel(size=(R, S, nn)) / beta, n, places).ravel())
            pl["B"].append(place_probs(mu, lambda R, S, nn, a: RNG.normal(size=(R, S, nn)) * sB, n, places).ravel())
            pl["C"].append(place_probs(mu, lambda R, S, nn, a, sg=sg: RNG.normal(size=(R, S, nn)) * sg[a:a + R, None, :], n, places).ravel())
            act.append((Fte.fin.values[pp] <= places).astype(float).ravel())
        for k in "ABC":
            store.append(dict(year=ty, model=k, p=np.concatenate(pl[k]), a=np.concatenate(act)))
        rows.append(Fte.drop(columns=[c for c in ("w2", "w3", "wavg_all", "wbest", "wt_rel", "bar_rel", "horse_age", "dist_ch") if c in Fte]))

    T = pd.concat(rows)
    W = T.groupby("race_id").apply(lambda g: pd.Series({m: np.log(g.loc[g.win == 1, m].iloc[0]) for m in ("pA", "pB", "pC", "pM")}))
    print("\n=== Win chances: mean log-likelihood of the winner (higher is better), test 2023-2026, %d races ===" % len(W))
    for m, name in (("pM", "M calibrated market"), ("pA", "A softmax on stand-in rating"), ("pB", "B simulation, one noise level"), ("pC", "C simulation, noise by runner type")):
        print(f"{name:38} {W[m].mean():8.4f}   by year " + " ".join(f"{W[T.groupby('race_id').year.first().reindex(W.index) == y][m].mean():.4f}" for y in TEST_YEARS))

    print("\n=== Place chances (3 places for 8+ runners, 2 for 5-7), sample of races: binary log-loss (lower is better) ===")
    P = pd.concat([pd.DataFrame(s) for s in store])
    for k, name in (("A", "A softmax (Gumbel noise)"), ("B", "B one noise level"), ("C", "C noise by runner type")):
        d = P[P.model == k]
        p = np.clip(d.p.values, 1e-4, 1 - 1e-4)
        ll = -(d.a.values * np.log(p) + (1 - d.a.values) * np.log(1 - p)).mean()
        print(f"{name:28} log-loss {ll:.4f}  mean predicted {p.mean():.3f} actual {d.a.mean():.3f}  n={len(d):,}")
    print("\nplace calibration, model C (predicted place chance band -> actual):")
    d = P[P.model == "C"]
    band = pd.cut(d.p, [0, .03, .07, .12, .2, .3, .45, .6, .8, 1.0])
    print(d.groupby(band, observed=True).agg(n=("a", "size"), predicted=("p", "mean"), actual=("a", "mean")).round(3).to_string())

    print("\n=== Win calibration, longshots (predicted win chance under 5%): predicted vs actual win rate ===")
    for m, name in (("pA", "A softmax"), ("pC", "C simulation by type"), ("pM", "M market")):
        d = T[T[m] < 0.05]
        print(f"{name:22} runners {len(d):,}  predicted {d[m].mean()*100:.2f}%  actual {d.win.mean()*100:.2f}%")

    print("\n=== Longshot calibration (15 Oct 2026): p' proportional to p^g within each race, g fitted on EARLIER test years only (model C) ===")
    from scipy.optimize import minimize_scalar as _ms
    def _ll(Tx, g):
        q = Tx.pC ** g
        q = q / q.groupby(Tx.race_id).transform("sum")
        return np.log(q[Tx.win == 1]).mean()
    yrs = list(TEST_YEARS)
    for i, ty in enumerate(yrs):
        if i == 0:
            continue
        past, cur = T[T.year.isin(yrs[:i])], T[T.year == ty]
        g = _ms(lambda x: -_ll(past, x), bounds=(0.8, 1.5), method="bounded").x
        q = cur.pC ** g
        q = q / q.groupby(cur.race_id).transform("sum")
        lo = cur.pC < 0.05
        print(f"{ty}: g {g:.3f}  winner log-lik {_ll(cur, 1.0):.4f} -> {_ll(cur, g):.4f}   longshots predicted {cur.pC[lo].mean()*100:.2f}% -> {q[lo].mean()*100:.2f}% (actual {cur.win[lo].mean()*100:.2f}%)")
    gall = _ms(lambda x: -_ll(T, x), bounds=(0.8, 1.5), method="bounded").x
    print(f"all years pooled g {gall:.3f}")
    qa = T.pC ** gall
    qa = qa / qa.groupby(T.race_id).transform("sum")
    T["band"] = pd.cut(T.pC, [0, .02, .05, .1, .2, .35, .5, 1])
    d = T.assign(q=qa).groupby("band", observed=True).agg(n=("win", "size"), before=("pC", "mean"), after=("q", "mean"), actual=("win", "mean"))
    print(d.round(4).to_string())

    print("\n=== Overlays against the RATED price (rating-only chances, no market in the model): flat $1 at SP ===")
    print(f"{'model':24} {'EV >':>5} {'bets':>7} {'win%':>6} {'ROI':>7} {'ex10':>7}")
    for m, name in (("pA", "A softmax"), ("pC", "C simulation by type")):
        for thr in (1.0, 1.1, 1.25, 1.5, 2.0):
            b = T[(T[m] * T.sp) > thr]
            n, w, r_, x = roi(b)
            print(f"{name:24} {thr:5.2f} {n:7} {w:6.1f} {r_:+7.1f} {x:+7.1f}")
    print("\nall runners flat: %+.1f%%   favourites flat: %+.1f%%" % (roi(T)[2], roi(T[T.sp == T.groupby('race_id').sp.transform('min')])[2]))
    print("\nEV > 1.25 by price band (model C):")
    b = T[(T.pC * T.sp) > 1.25].copy()
    b["band"] = pd.cut(b.sp, [1, 3, 6, 10, 20, 50, 1000])
    for k, g in b.groupby("band", observed=True):
        n, w, r_, x = roi(g)
        print(f"  ${k.left:.0f}-{k.right:.0f}: bets {n:6} win {w:5.1f}% ROI {r_:+7.1f}% ex10 {x:+7.1f}%")
    print(f"\ndone in {time.time()-t0:.0f}s")


if __name__ == "__main__":
    main()
