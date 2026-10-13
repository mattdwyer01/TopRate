"""Tune the own-ratings chain for the thing that matters: what the ratings add to the bet model beyond the market (13 Oct 2026, read-only).

Objective = walk-forward log-loss GAIN over the SP-normalised market, from the production bet-model recipe (LightGBM started from the
market logit, production features and parameters, one seed, higher learning rate for speed), when the rating columns (w1..w3, wavg3,
wbest, wavg_all, wavg3_rel, wavg3_mean) come from a candidate chain. Not next-run rating accuracy.

Folds: TUNE_FOLDS decide which candidate wins; HOLD_FOLDS (2025, 2026) are scored only for the baseline and the final pick.
The chain here is a numpy copy of own_ratings/chain.py (same maths, same defaults) plus extra knobs; `check_baseline` verifies it
reproduces the stored ratings.

  python -m own_ratings.tune --prep               # cache observations + rating-independent features
  python -m own_ratings.tune --baseline           # baseline on tune and hold folds
  python -m own_ratings.tune --search N --jobs 3  # coordinate / random search on the tune folds
  python -m own_ratings.tune --final '{"cap": 12}'  # candidate on all folds + robustness
"""
import argparse
import json
import os
import sys
import time

import numpy as np
import pandas as pd

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
CACHE = os.environ.get("TUNE_CACHE", "/tmp/tune_cache")
os.makedirs(CACHE, exist_ok=True)

BASE = dict(ms0=1.1, ms1=1.4, ms2=1.4, cap=10.0, gamma=1.0, kpow=1.0, exp_n=3, decay=1.0, hist_n=6, trim=0.25, min_priors=6,
            wcoef=0.5, rs_bias=0.0, level_ema=0.02)
BOUNDS = dict(ms0=(0.7, 1.6), ms1=(0.9, 2.0), ms2=(0.9, 2.0), cap=(5, 25), gamma=(0.6, 1.0), kpow=(0.7, 1.3), exp_n=(1, 6),
              decay=(0.4, 1.0), hist_n=(6, 12), trim=(0.0, 0.4), min_priors=(2, 10), wcoef=(0.0, 1.0), level_ema=(0.005, 0.1))
INT = {"exp_n", "hist_n", "min_priors"}
RATING_COLS = ["w1", "w2", "w3", "wavg3", "wbest", "wavg_all", "wavg3_rel", "wavg3_mean"]
TUNE_FOLDS, HOLD_FOLDS = (2023, 2024), (2025, 2026)


# ------------------------------------------------------------------ chain (numpy)
def prep_obs():
    from own_ratings import core, rebuild_history as R
    d = R.load_observations()
    o = R.prepare(d).drop(columns=["wpr"], errors="ignore")
    o = o.sort_values(["date", "race_id"], kind="mergesort").reset_index(drop=True)
    x = core.add_weight_terms(o, 1.0)        # wadj with coef 1.0 = the weight base; scaled by wcoef later
    o["wbase"] = x["wadj"].values
    o["horse_id"] = o["horse_id"].astype("int64")
    return o[["date", "race_id", "horse_id", "distance", "margin", "wbase"]]


def run_chain(o, p):
    """o: prep_obs frame. Returns wpr array (level corrected) aligned to o."""
    from own_ratings import core, rebuild_history as R
    dist = o.distance.values.astype(float)
    ms = np.where(dist < 1300, p["ms0"], np.where(dist <= 1800, p["ms1"], p["ms2"]))
    k = np.maximum(2750.0 / dist, 1.5) ** p["kpow"] * ms
    m = np.clip(o.margin.values.astype(float), 0, p["cap"]) ** p["gamma"] if p["gamma"] != 1.0 else np.clip(o.margin.values.astype(float), 0, p["cap"])
    hid = o.horse_id.values
    rid = o.race_id.values
    edges = np.flatnonzero(np.r_[True, rid[1:] != rid[:-1], True])
    n = len(o)
    atw = np.full(n, np.nan)
    hist = {}
    exp_n, hist_n, minp = int(p["exp_n"]), int(p["hist_n"]), int(p["min_priors"])
    w = p["decay"] ** np.arange(exp_n)[::-1]          # most recent last
    last_rs = 70.0
    ema = p["level_ema"]
    for a, b in zip(edges[:-1], edges[1:]):
        imp = []
        for j in range(a, b):
            hh = hist.get(hid[j])
            if hh is not None and len(hh) >= minp and not np.isnan(m[j]):
                t = hh[-exp_n:]
                ww = w[-len(t):]
                imp.append(float(np.dot(t, ww) / ww.sum()) + k[j] * m[j])
        if imp:
            rs = core.trimmed_mean(imp, p["trim"]) + p["rs_bias"]
            last_rs = (1 - ema) * last_rs + ema * rs
        else:
            rs = last_rs
        for j in range(a, b):
            if np.isnan(m[j]):
                continue
            av = rs - k[j] * m[j]
            atw[j] = av
            hl = hist.setdefault(hid[j], [])
            hl.append(av)
            if len(hl) > hist_n:
                del hl[0]
    wpr = atw + p["wcoef"] * o.wbase.values
    off = R.level_correction(o.date.values, wpr)
    return wpr + off


# ------------------------------------------------------------------ features / model
def prep_features():
    from betsignal import features as F
    H = F.load_history()
    cats = F.categories(H)
    D = F.batch_features(H, cats)
    D = D.sort_values(["horse_id", "date", "raceNumber"], kind="mergesort").reset_index(drop=True)
    return D, cats


def rating_features(D, wpr):
    """D sorted by horse_id, date, raceNumber with a unique index. Recomputes the rating columns exactly as betsignal.features does."""
    D = D.copy()
    D["wpr"] = wpr
    h = D.groupby("horse_id")
    for kk in (1, 2, 3):
        D[f"w{kk}"] = h.wpr.shift(kk)
    D["wavg3"] = D[["w1", "w2", "w3"]].mean(axis=1)
    D["wbest"] = h.wpr.transform(lambda s: s.shift(1).expanding().max())
    D["wavg_all"] = h.wpr.transform(lambda s: s.shift(1).expanding().mean())
    r = D.groupby("race_id")
    D["wavg3_rel"] = D.wavg3 - r.wavg3.transform("max")
    D["wavg3_mean"] = D.wavg3 - r.wavg3.transform("mean")
    return D


PARAMS = dict(objective="binary", learning_rate=0.08, num_leaves=15, min_data_in_leaf=400, feature_fraction=0.7, bagging_fraction=0.7,
              bagging_freq=1, lambda_l2=50, verbose=-1, seed=1, num_threads=2)


def fold_eval(D, ty):
    import lightgbm as lgb
    from betsignal import features as F
    from betsignal.score import tier
    logit = lambda p: np.log(p / (1 - p))
    tr, va, te = D[D.year <= ty - 2], D[D.year == ty - 1], D[D.year == ty].copy()
    m = lgb.train(PARAMS, lgb.Dataset(tr[F.FEATURES], tr.win, init_score=logit(tr.pm)), 1500,
                  valid_sets=[lgb.Dataset(va[F.FEATURES], va.win, init_score=logit(va.pm))], callbacks=[lgb.early_stopping(60, verbose=False)])
    s = m.predict(te[F.FEATURES], raw_score=True) + logit(te.pm).values
    te["s"] = s
    e = np.exp(s - te.groupby("race_id").s.transform("max").values)
    te["pmod"] = e / e.groupby(te.race_id).transform("sum")
    te["ev"] = te.pmod * te.sp
    w = te[te.win == 1]
    gain = float((-np.log(w.pm)).mean() - (-np.log(w.pmod)).mean())
    te["tier"] = [tier(a, b, c) for a, b, c in zip(te.ev, te.sp, te.rank_m)]
    te["ret"] = np.where(te.win == 1, te.sp, 0.0)
    sel = te[te.tier == "S"]
    return dict(year=ty, gain=gain, iters=m.best_iteration, n_sel=len(sel), sel_roi=float(sel.ret.mean() - 1) if len(sel) else np.nan,
                races=int(w.shape[0])), te


def evaluate(p, folds, o=None, D=None, keep=False):
    t = time.time()
    o = o if o is not None else pd.read_pickle(f"{CACHE}/obs.pkl")
    D = D if D is not None else pd.read_pickle(f"{CACHE}/feat.pkl")
    wpr = run_chain(o, p)
    key = pd.DataFrame({"race_id": o.race_id.values, "horse_id": o.horse_id.values, "wpr": wpr})
    k = D[["race_id", "horse_id"]].merge(key, on=["race_id", "horse_id"], how="left")
    DD = rating_features(D, k["wpr"].values)
    res, tes = [], []
    for ty in folds:
        r, te = fold_eval(DD, ty)
        res.append(r)
        tes.append(te)
    out = dict(params=p, folds=res, gain=float(np.mean([r["gain"] for r in res])), secs=round(time.time() - t))
    return (out, pd.concat(tes)) if keep else out


# ------------------------------------------------------------------ CLI
def _clip(p):
    q = dict(p)
    for kk, (lo, hi) in BOUNDS.items():
        q[kk] = min(max(q[kk], lo), hi)
        if kk in INT:
            q[kk] = int(round(q[kk]))
    return q


def _job(args):
    p, folds = args
    return evaluate(p, folds)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--prep", action="store_true")
    ap.add_argument("--baseline", action="store_true")
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--search", type=int, default=0)
    ap.add_argument("--jobs", type=int, default=3)
    ap.add_argument("--final", default="")
    ap.add_argument("--seed", type=int, default=0)
    a = ap.parse_args()
    if a.prep:
        t = time.time()
        prep_obs().to_pickle(f"{CACHE}/obs.pkl")
        print("obs", round(time.time() - t), flush=True)
        D, _ = prep_features()
        D.to_pickle(f"{CACHE}/feat.pkl")
        print("feat", len(D), round(time.time() - t), flush=True)
    if a.check:
        from betsignal import features as F
        o = pd.read_pickle(f"{CACHE}/obs.pkl")
        t = time.time()
        wpr = run_chain(o, BASE)
        print("chain secs", round(time.time() - t))
        st = F.own_ratings(pd.DataFrame({"race_id": o.race_id, "horse_id": o.horse_id}))["wpr"].values
        ok = ~np.isnan(st) & ~np.isnan(wpr)
        print("vs stored: n", ok.sum(), "mean abs diff", np.abs(st[ok] - wpr[ok]).mean(), "corr", np.corrcoef(st[ok], wpr[ok])[0, 1])
    if a.baseline:
        r = evaluate(BASE, TUNE_FOLDS + HOLD_FOLDS)
        print(json.dumps(r, default=float, indent=1))
    if a.search:
        from multiprocessing import Pool
        rng = np.random.default_rng(a.seed)
        best, best_g, log = dict(BASE), None, []
        res0 = evaluate(BASE, TUNE_FOLDS)
        best_g = res0["gain"]
        print("baseline tune gain", round(best_g, 5), flush=True)
        names = list(BOUNDS)
        with Pool(a.jobs) as pool:
            for rnd in range(a.search):
                cands = []
                for _ in range(a.jobs):
                    q = dict(best)
                    for kk in rng.choice(names, size=int(rng.integers(1, 3)), replace=False):
                        lo, hi = BOUNDS[kk]
                        q[kk] = q[kk] + rng.normal(0, 0.15 * (hi - lo))
                    cands.append(_clip(q))
                outs = pool.map(_job, [(c, TUNE_FOLDS) for c in cands])
                for o_ in outs:
                    log.append(o_)
                    print(f"round {rnd} gain {o_['gain']:.5f} ({o_['secs']}s)", {kk: o_["params"][kk] for kk in names if o_["params"][kk] != BASE[kk]}, flush=True)
                top = max(outs, key=lambda r: r["gain"])
                if top["gain"] > best_g + 0.0002:        # must beat the best by more than seed-level noise
                    best_g, best = top["gain"], top["params"]
                    print("  new best", round(best_g, 5), {kk: best[kk] for kk in names if best[kk] != BASE[kk]}, flush=True)
                json.dump(dict(best=best, best_gain=best_g, log=log), open(f"{CACHE}/search_{a.seed}.json", "w"), default=float)
    if a.final:
        p = dict(BASE, **json.loads(a.final))
        for name, pp in (("baseline", BASE), ("candidate", _clip(p))):
            r = evaluate(pp, TUNE_FOLDS + HOLD_FOLDS)
            print(name, json.dumps(r, default=float))


if __name__ == "__main__":
    main()
