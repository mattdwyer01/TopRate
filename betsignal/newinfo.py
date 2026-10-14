"""Do any NEW information sources add to a calibrated market? (13 Oct 2026, read-only research script)

Sources tested, each built strictly as-of (only events before the race date):
  trial  barrier-trial form since the horse's last race (rows the models drop today)
  sire   sire excess win rate over the market, overall / by distance band / wet track
  cmt    run-comment flags (trouble, slow away, wide, vet/excuse, effort tags), last run and last 3
  run    running positions: early position, closing kick, margin at 800m (last run, last 3)
  gps    ground lost to the winner from GPS tracking (VIC/SA/QLD, 2021 on), last run and last 3

Test: race-level conditional logit (softmax within a race) on clean-book races only (SP book between 1.05 and 1.5; races with an
impossible book are a data artefact, see CLAUDE.md 14 Oct 2026). Baseline = log market price + the existing rating-form columns.
For each group: gain in log-likelihood per race over the baseline, fitted on years before the test year, tested 2022 to 2026,
with a standard error from the per-race differences. Features are centred within the race.

  python betsignal/newinfo.py --build   # features -> /tmp/tune_cache/newinfo.pkl (a few minutes)
  python betsignal/newinfo.py --test
"""
import argparse
import glob
import os
import re
import sys

import numpy as np
import pandas as pd

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
CACHE = os.environ.get("TUNE_CACHE", "/tmp/tune_cache")

COLS = ["race_id", "date", "horse_id", "horse", "field_size", "positionFinish", "marginFinish", "position800m", "position400m",
        "margin800m", "isBarrierTrial", "sire", "comments_steward", "comments_video"]

PATTERNS = {
    "trouble": r"check|held up|blocked|bump|crowded|hamper|no room|shut off|tightened|clipped heels|inconvenienc|interfer|raced greenly",
    "slowaway": r"slowly away|began awkwardly|missed the start|dwelt|fumbled|stumbled|lost ground|began slowly|jumped awkwardly",
    "wide": r"wide without cover|\b(four|five|six|seven|eight|4|5|6|7|8) wide",
    "excuse": r"\bvet\b|lame|bled|heart|distress|fractious|injur|lost (a )?plate|lost (a )?shoe|saddle|slipped|unsuited|reluctant|resented",
    "tagdis": r"\[[^\]]*(disappoint|poor|ordinary|flat|unsuited|lacklustre)[^\]]*\]",
    "taggood": r"\[[^\]]*(solid|good|strong|impressive|brave|pleasing|tried hard|excellent|sound)[^\]]*\]",
}


def load_all():
    parts = []
    for f in sorted(glob.glob(os.path.join(ROOT, "race_results_20*.csv.gz"))):
        d = pd.read_csv(f, usecols=lambda c: c in COLS, low_memory=False)
        parts.append(d)
    d = pd.concat(parts, ignore_index=True)
    d["race_id"] = pd.to_numeric(d.race_id, errors="coerce")
    d["horse_id"] = pd.to_numeric(d.horse_id, errors="coerce")
    d["date"] = pd.to_datetime(d.date.astype(str).str[:10])
    return d.dropna(subset=["horse_id", "race_id"]).drop_duplicates(["race_id", "horse_id"])


def norm(s):
    return s.astype(str).str.lower().str.replace(r"[^a-z0-9]", "", regex=True)


def load_gps():
    out = []
    for f in sorted(glob.glob(os.path.join(ROOT, "data", "gps", "rc_gps_runs_20*.parquet"))):
        g = pd.read_parquet(f, columns=["start_utc", "horse", "dist_vs_winner_m"])
        g["date"] = (pd.to_datetime(g.start_utc, utc=True) + pd.Timedelta(hours=10)).dt.tz_localize(None).dt.normalize()
        out.append(g[["date", "horse", "dist_vs_winner_m"]])
    for f in sorted(glob.glob(os.path.join(ROOT, "data", "gps", "rq_gps_runs_20*.parquet"))):
        g = pd.read_parquet(f, columns=["race_date", "horse", "dist_vs_winner_m"])
        g["date"] = pd.to_datetime(g.race_date).dt.normalize()
        out.append(g[["date", "horse", "dist_vs_winner_m"]])
    g = pd.concat(out, ignore_index=True)
    g["hn"] = norm(g.horse)
    return g.dropna(subset=["dist_vs_winner_m"]).drop_duplicates(["date", "hn"])


def cum_ex(D, keys, k):
    """Shrunk excess win rate vs the market for a key, using only earlier dates."""
    d = D.groupby(keys + ["date"]).agg(n=("win", "size"), e=("_ex", "sum")).reset_index().sort_values(keys + ["date"])
    g = d.groupby(keys)
    d["cn"] = g.n.cumsum() - d.n
    d["ce"] = g.e.cumsum() - d.e
    d["v"] = d.ce / (d.cn + k)
    return D[keys + ["date"]].merge(d[keys + ["date", "v"]], on=keys + ["date"], how="left")["v"].values


def build():
    D = pd.read_pickle(f"{CACHE}/feat.pkl")                       # tune.py --prep output: production features, sorted horse/date
    R = load_all()
    base = D[["race_id", "horse_id", "date", "days", "going_n", "distance", "win", "pm", "sp", "year", "field_size", "nruns",
              "w1", "wavg3", "wbest", "wavg_all"]].copy()
    raw = R[R.isBarrierTrial != True][["race_id", "horse_id", "horse", "sire", "comments_steward", "comments_video", "positionFinish",
                                       "position800m", "position400m", "margin800m"]]
    base = base.merge(raw, on=["race_id", "horse_id"], how="left")
    base["_ex"] = base.win - base.pm
    F = pd.DataFrame(index=base.index)
    # ---- trial
    tr = R[R.isBarrierTrial == True][["horse_id", "date", "positionFinish", "marginFinish", "field_size"]].rename(
        columns={"date": "tdate", "positionFinish": "tpos", "marginFinish": "tmarg", "field_size": "tfield"})
    tr = tr.assign(date=tr.tdate).sort_values("date")
    left = base[["horse_id", "date", "days"]].reset_index().sort_values("date")
    m = pd.merge_asof(left, tr, on="date", by="horse_id", allow_exact_matches=False).set_index("index").sort_index()
    since = (m.date - m.tdate).dt.days
    recent = since.notna() & (since <= 60) & (m.days.isna() | (since < m.days))
    F["trial"] = recent.astype(float)
    F["trial_win"] = (recent & (m.tpos == 1)).astype(float)
    F["trial_top3"] = (recent & (m.tpos <= 3)).astype(float)
    F["trial_marg"] = np.where(recent, np.clip(pd.to_numeric(m.tmarg, errors="coerce").fillna(8), 0, 8), 0.0)
    F["trial_fresh"] = (recent & (m.days.fillna(999) > 60)).astype(float)         # trial since a spell
    # ---- sire
    B = base
    F["sire_ex"] = cum_ex(B, ["sire"], 100)
    B["db"] = np.where(B.distance < 1300, 0, np.where(B.distance <= 1800, 1, 2))
    B["wet"] = (B.going_n >= 7).astype(int)
    F["sire_db_ex"] = cum_ex(B, ["sire", "db"], 60)
    F["sire_wet_ex"] = cum_ex(B, ["sire", "wet"], 60)
    # ---- comments (per-horse history of D rows)
    txt = (B.comments_video.fillna("") + " " + B.comments_steward.fillna("")).str.lower()
    o = B.sort_values(["horse_id", "date"]).index
    for name, pat in PATTERNS.items():
        flag = txt.str.contains(pat, regex=True).astype(float)
        g = flag.loc[o].groupby(B.horse_id.loc[o])
        F[f"c_{name}_1"] = g.shift(1).reindex(B.index)
        F[f"c_{name}_3"] = g.transform(lambda s: s.shift(1).rolling(3, min_periods=1).sum()).reindex(B.index)
    # ---- running positions
    fs = B.field_size.replace(0, np.nan)
    early = pd.to_numeric(B.position800m, errors="coerce") / fs
    kick = (pd.to_numeric(B.position400m, errors="coerce") - pd.to_numeric(B.positionFinish, errors="coerce")) / fs
    marg8 = np.clip(pd.to_numeric(B.margin800m, errors="coerce"), 0, 15)
    for name, s in (("early", early), ("kick", kick), ("m800", marg8)):
        g = s.loc[o].groupby(B.horse_id.loc[o])
        F[f"r_{name}_1"] = g.shift(1).reindex(B.index)
        F[f"r_{name}_3"] = g.transform(lambda x: x.shift(1).rolling(3, min_periods=1).mean()).reindex(B.index)
    # ---- gps ground lost
    G = load_gps()
    B["hn"] = norm(B.horse)
    gl = B[["hn", "date"]].merge(G[["date", "hn", "dist_vs_winner_m"]], on=["date", "hn"], how="left")["dist_vs_winner_m"].values
    gl = pd.Series(np.clip(gl, -5, 60), index=B.index)
    print("gps coverage of D rows:", round(float(gl.notna().mean()), 3), flush=True)
    g = gl.loc[o].groupby(B.horse_id.loc[o])
    F["gps_gl_1"] = g.shift(1).reindex(B.index)
    F["gps_gl_3"] = g.transform(lambda x: x.shift(1).rolling(3, min_periods=1).mean()).reindex(B.index)
    out = pd.concat([B[["race_id", "horse_id", "date", "year", "win", "pm", "sp", "nruns", "w1", "wavg3", "wbest", "wavg_all"]], F], axis=1)
    out.to_pickle(f"{CACHE}/newinfo.pkl")
    print("saved", out.shape, flush=True)


GROUPS = {
    "trial": ["trial", "trial_win", "trial_top3", "trial_marg", "trial_fresh"],
    "sire": ["sire_ex", "sire_db_ex", "sire_wet_ex"],
    "cmt": [f"c_{n}_{k}" for n in PATTERNS for k in (1, 3)],
    "run": [f"r_{n}_{k}" for n in ("early", "kick", "m800") for k in (1, 3)],
    "gps": ["gps_gl_1", "gps_gl_3"],
}
BASE_COLS = ["w1", "wavg3", "wbest", "wavg_all"]


def design(T, cols, mu_sd=None):
    g = T.groupby("race_id")
    X = [np.log(T.pm.values)]
    for c in cols:
        v = T[c]
        X.append((v - g[c].transform("mean")).fillna(0.0).values)
    X = np.column_stack(X)
    if mu_sd is None:
        mu_sd = (X.mean(0), X.std(0) + 1e-9)
        mu_sd[0][0], mu_sd[1][0] = 0.0, 1.0
    return (X - mu_sd[0]) / mu_sd[1], mu_sd


def race_ll(X, seg, win, b):
    sizes = np.diff(np.r_[seg, len(X)])
    rid = np.repeat(np.arange(len(seg)), sizes)
    z = X @ b
    e = np.exp(z - np.maximum.reduceat(z, seg)[rid])
    p = e / np.add.reduceat(e, seg)[rid]
    return np.log(p[win == 1]), p


def fit(X, seg, win, l2=30.0):
    from scipy.optimize import minimize
    sizes = np.diff(np.r_[seg, len(X)])
    rid = np.repeat(np.arange(len(seg)), sizes)

    def f(b):
        z = X @ b
        e = np.exp(z - np.maximum.reduceat(z, seg)[rid])
        p = e / np.add.reduceat(e, seg)[rid]
        ll = -np.log(p[win == 1]).sum() + l2 * (b[1:] @ b[1:])
        g = -(X[win == 1].sum(0) - (p[:, None] * X).sum(0)) + 2 * l2 * np.r_[0, b[1:]]
        return ll, g
    b0 = np.zeros(X.shape[1])
    b0[0] = 1.0
    return minimize(f, b0, jac=True, method="L-BFGS-B").x


def test(years=(2022, 2023, 2024, 2025, 2026), groups=None):
    A = pd.read_pickle(f"{CACHE}/newinfo.pkl")
    book = (1 / A.sp).groupby(A.race_id).transform("sum")
    A = A[(book >= 1.05) & (book <= 1.5)].sort_values("race_id", kind="mergesort").reset_index(drop=True)
    print("clean-book rows", len(A), "races", A.race_id.nunique(), flush=True)
    sets = {"baseline": BASE_COLS}
    for k, v in (groups or GROUPS).items():
        sets[k] = BASE_COLS + v
    sets["ALL"] = BASE_COLS + [c for v in (groups or GROUPS).values() for c in v]
    diffs = {k: [] for k in sets if k != "baseline"}
    peryear = {k: {} for k in diffs}
    for ty in years:
        tr, te = A[A.year <= ty - 1], A[A.year == ty]
        segtr = np.flatnonzero(np.r_[True, tr.race_id.values[1:] != tr.race_id.values[:-1]])
        segte = np.flatnonzero(np.r_[True, te.race_id.values[1:] != te.race_id.values[:-1]])
        ll = {}
        for k, cols in sets.items():
            Xtr, ms = design(tr, cols)
            Xte, _ = design(te, cols, ms)
            b = fit(Xtr, segtr, tr.win.values)
            ll[k], _ = race_ll(Xte, segte, te.win.values, b)
        for k in diffs:
            d = ll[k] - ll["baseline"]
            diffs[k].append(d)
            peryear[k][ty] = d.mean()
        print("year", ty, "done", flush=True)
    print(f"\n{'group':9} {'gain/race':>10} {'se':>8} {'t':>6}   by year (x1e4)")
    for k, ds in diffs.items():
        d = np.concatenate(ds)
        se = d.std() / np.sqrt(len(d))
        print(f"{k:9} {d.mean()*1e4:10.2f} {se*1e4:8.2f} {d.mean()/se:6.2f}   " + " ".join(f"{peryear[k][y]*1e4:+6.1f}" for y in years))


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--build", action="store_true")
    ap.add_argument("--test", action="store_true")
    a = ap.parse_args()
    if a.build:
        build()
    if a.test:
        test()
