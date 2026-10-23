"""Spd the way Proj is built (22 Oct 2026, research/spd_formula_ctx.py). The rating for a runner is the predicted speed figure (lengths vs par, higher = faster) of its next run:
a formula (weights by earlier-run count) on the horse's last eight figures, plus a LightGBM context correction, plus (3+ earlier figures) the relevance model that judges each
earlier run against today's race. Same code as the Proj build (projection/ctx.py), different target: the run's own time-based speed figure (speed_rating.figures).
Held-out 2026 (13,203 races): winner log-lik -2.0935 for the old Spd (EWM + days and weight terms) against -2.0125, top pick 21.1% to 25.1%, within-race RMSE 4.085 to 3.883.

speed_rating.compute() uses this when the artifacts in speed_models/ exist and falls back to the old calculation for a runner the model cannot rate.
Train: PYTHONPATH=. python speed_model.py --train     (about 30 to 40 minutes; refit as the results grow)
Check: PYTHONPATH=. python speed_model.py --check"""
import json
import os
import sys
import warnings
from pathlib import Path

import numpy as np
import pandas as pd

import speed_rating as sr
from projection import ctx as C

DIR = Path(__file__).parent
OUT = DIR / "speed_models"
META = OUT / "spd_model.json"
CTX_FILE = OUT / "spd_ctx.txt"
REL_FILE = OUT / "spd_rel.txt"
FIRST_YEAR = 2019          # figure history read (the relevance features use every earlier run)
TR_FROM = pd.Timestamp("2023-07-01")
ES_FROM = pd.Timestamp("2025-07-01")
CUT = pd.Timestamp("2026-01-01")
P = dict(learning_rate=0.1, num_leaves=63, min_child_samples=200, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1, n_jobs=4)
if os.environ.get('SPD_LR'): P.update(learning_rate=float(os.environ['SPD_LR']))
HUBER_ALPHA = float(os.environ.get('HUBER', '4'))   # 23 Oct 2026: Huber alpha 4 (lengths), as the Proj context models; HUBER=0 gives mean loss. Learning rate 0.1: Huber at 0.03 needs hours
if HUBER_ALPHA > 0: P.update(objective='huber', alpha=HUBER_ALPHA)
K = C.K


def frame(first_year=FIRST_YEAR):
    """Every run with a speed figure (column wpr, lengths vs par) plus the history columns ctx needs, sorted by horse and date."""
    d = sr.figures(sr.load_results(first_year))
    rp = pd.DataFrame(dict(
        key=d.horse.astype(str).str.lower().str.strip().values, date=pd.to_datetime(d.date).values, wpr=d.sp.values, track=d.track.values,
        distance=pd.to_numeric(d.distance, errors="coerce").values, going=d.going.values, weightCarried=pd.to_numeric(d.weightCarried, errors="coerce").values,
        barrier=pd.to_numeric(d.barrier, errors="coerce").values, field_size=pd.to_numeric(d.field_size, errors="coerce").values, race_class=d.race_class.values,
        trackGrading=d.trackGrading.values, jockey=d.jockey.values, positionFinish=pd.to_numeric(d.positionFinish, errors="coerce").values,
        marginFinish=pd.to_numeric(d.marginFinish, errors="coerce").values, race_id=d.race_id.values))
    rp = rp.dropna(subset=["key", "date", "wpr"]).sort_values(["key", "date"]).drop_duplicates(["key", "date"], keep="last").reset_index(drop=True)
    rp["horse_id"] = pd.factorize(rp.key)[0].astype(float)
    rp["going_n"] = C.going_num(rp.going)
    rp["grade"] = pd.to_numeric(rp.trackGrading, errors="coerce")
    rp["cls"] = C.class_code(rp.race_class)
    rp["vn"] = C.venue_key(rp.track)
    rp["venue"] = rp.vn
    rp["jockey"] = rp.jockey.astype(object).where(rp.jockey.notna(), None)
    g = rp.groupby("horse_id")
    for k in range(1, K + 1):
        rp[f"r{k}"] = g.wpr.shift(k)
    rp["n"] = g.cumcount().astype(float)
    rp["d_last"] = (rp.date - g.date.shift(1)).dt.days.astype(float)
    rp["l_dist"], rp["l_going"], rp["l_wt"], rp["l_mgn"] = g.distance.shift(1), g.going_n.shift(1), g.weightCarried.shift(1), g.marginFinish.shift(1)
    rp["l_posf"] = (rp.positionFinish / rp.field_size).groupby(rp.horse_id).shift(1)
    return rp


def fit_formula(rp, before):
    trn = rp[rp.date < before]
    co = {}
    for nn in range(1, K + 1):
        a = trn[trn.n.clip(upper=K) == nn]
        c = [f"r{k}" for k in range(1, nn + 1)]
        a = a.dropna(subset=c)
        co[nn] = np.linalg.lstsq(np.c_[np.ones(len(a)), a[c].values], a.wpr.values, rcond=None)[0]
    return co


def prepare(rp, co):
    """Adds the formula, its residual and the context columns the live path needs on the history frame."""
    rp = rp.copy()
    rp["f"] = C.formula_pred(rp, co, None)
    rp = C.context_columns(rp)
    rp["resid"] = rp.wpr - rp.f
    return rp


def winner_test(te):
    """Conditional-logit winner test on complete held-out races (5+ runners, one winner): z-score of the prediction in the race, scale cross-fitted on date halves."""
    from scipy.optimize import minimize
    t = te.dropna(subset=["p_rel", "positionFinish"]).copy()
    t["won"] = (t.positionFinish == 1).astype(int)
    g = t.groupby("race_id").won
    t = t[(g.transform("sum") == 1) & (g.transform("size") >= 5)].copy()
    t["rid"] = t.race_id.astype("category").cat.codes
    gm = t.groupby("rid").p_rel
    t["z"] = ((t.p_rel - gm.transform("mean")) / gm.transform("std").replace(0, np.nan)).fillna(0.0)

    def ll(df, b):
        s_ = b * df.z.values
        mx = pd.Series(s_).groupby(df.rid.values).transform("max").values
        return (s_ - (np.log(pd.Series(np.exp(s_ - mx)).groupby(df.rid.values).transform("sum").values) + mx))[df.won.values == 1]
    from scipy.optimize import minimize as mn
    dts = sorted(t.date.unique()); half = dts[len(dts) // 2]
    A, B = t[t.date < half], t[t.date >= half]
    out, tops = [], []
    for a_, b_ in ((A, B), (B, A)):
        b = mn(lambda w: -ll(a_, w[0]).mean(), [0.3], method="L-BFGS-B").x[0]
        out.append(ll(b_, b)); x = b_.assign(s=b * b_.z); tops.append(x.loc[x.groupby("rid").s.idxmax()].won.values)
    print(f"winner test: {t.rid.nunique():,} races, winner log-lik {np.concatenate(out).mean():.4f}, top pick {100 * np.concatenate(tops).mean():.1f}%")


def train():
    import lightgbm as lgb
    rp = frame()
    print(f"{len(rp):,} speed figures, {rp.horse_id.nunique():,} horses, {rp.date.min().date()} to {rp.date.max().date()}")
    co = fit_formula(rp, CUT)
    print("formula weights, 8+ runs:", np.round(co[K], 3))
    rp = prepare(rp, co)
    rp = C.add_jockey(rp, C.jockey_table(rp))
    rp = C.add_venue(rp, rp)
    classes = sorted(rp.cls.dropna().unique().tolist())
    rp["cls_c"] = C._cls(rp.cls, classes)
    need = rp[(rp.date >= TR_FROM) & rp.f.notna()]
    print(f"relevance features for {len(need):,} rows...")
    need = pd.concat([need, C.rel_features(need, rp)], axis=1)
    F0, F1 = C.FEATS, C.FEATS + C.REL_FEATS
    tr = need[need.date < ES_FROM]
    va = need[(need.date >= ES_FROM) & (need.date < CUT)]
    te = need[need.date >= CUT].copy()

    def fitm(feats, rows=None):
        m = lgb.LGBMRegressor(n_estimators=4000, **P).fit(tr[feats], tr.resid, eval_set=[(va[feats], va.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
        return m
    m0, m1 = fitm(F0), fitm(F1)
    n0, n1 = m0.best_iteration_, m1.best_iteration_
    te["p_formula"] = te.f
    te["p_ctx"] = te.f + m0.predict(te[F0])
    te["p_rel"] = np.where(te.n >= C.REL_MIN_RUNS, te.f + m1.predict(te[F1]), te.p_ctx)
    r = lambda x: float(np.sqrt(np.nanmean(np.asarray(x) ** 2)))
    big = te.groupby("race_id").wpr.transform("size") >= 5
    for lab, c in (("formula", "p_formula"), ("formula + context", "p_ctx"), ("deployed (relevance for 3+ runs)", "p_rel")):
        e = te.wpr - te[c]
        w = (e - e.groupby(te.race_id).transform("mean"))[big]
        print(f"held out {lab:34s} RMSE {r(e):.3f}  within-race {r(w):.3f}  (n={len(te):,})")
    miss = te.wpr - te.p_rel
    print(f"held out all runs: mean miss {miss.mean():+.2f}, median {miss.median():+.2f}, within 2 lengths {100*(miss.abs()<=2).mean():.1f}%, within 4 {100*(miss.abs()<=4).mean():.1f}%")
    winner_test(te)
    if os.environ.get('SPD_DUMP'):
        te[['key', 'date', 'p_rel', 'wpr', 'race_id', 'positionFinish']].to_pickle(os.environ['SPD_DUMP'])
    if os.environ.get('SPD_EVAL_ONLY'):
        return
    live = te[te.date >= pd.Timestamp("2026-09-01")]
    sd_new, mu_new = float(live.p_rel.std()), float(live.p_rel.mean())
    scale = 1.0
    print(f"new prediction on 2026-09+ runs: mean {mu_new:.2f}, sd {sd_new:.2f}; figure mean {live.wpr.mean():.2f}, sd {live.wpr.std():.2f}")
    # final fit on every run from TR_FROM, tree count from the held-out stage
    allr = need
    fin0 = lgb.LGBMRegressor(n_estimators=int(n0 * 1.1), **P).fit(allr[F0], allr.resid)
    fin1 = lgb.LGBMRegressor(n_estimators=int(n1 * 1.1), **P).fit(allr[allr.n >= C.REL_MIN_RUNS][F1], allr[allr.n >= C.REL_MIN_RUNS].resid)
    OUT.mkdir(exist_ok=True)
    fin0.booster_.save_model(str(CTX_FILE))
    fin1.booster_.save_model(str(REL_FILE))
    meta = dict(feats=F0, rel_feats=F1, rel_min_runs=C.REL_MIN_RUNS, classes=classes, n_trees=int(n0 * 1.1), n_trees_rel=int(n1 * 1.1),
                coef={str(k): v.tolist() for k, v in co.items()}, fit_to=str(rp.date.max().date()), mu_new=mu_new, sd_new=sd_new, scale=scale)
    META.write_text(json.dumps(meta))
    print("written", META, CTX_FILE, REL_FILE)


def load():
    if not (META.exists() and CTX_FILE.exists() and REL_FILE.exists()):
        return None
    import lightgbm as lgb
    meta = json.loads(META.read_text())
    return meta, lgb.Booster(model_file=str(CTX_FILE)), lgb.Booster(model_file=str(REL_FILE))


def predict(runners_df, rows, today=None, art=None, hist=None):
    """Predicted speed figure for the runner rows `rows` (boolean mask on runners_df), NaN where the horse has no earlier figure. Series on runners_df.index."""
    art = art or load()
    out = pd.Series(np.nan, index=runners_df.index)
    if art is None or not rows.any():
        return out
    meta, booster, rel = art
    co = {int(k): np.array(v) for k, v in meta["coef"].items()}
    rp = hist if hist is not None else prepare(frame(), co)
    ids = dict(zip(rp.key, rp.horse_id))
    R = runners_df.loc[rows]
    keys = R["horse"].astype(str).str.lower().str.strip()
    fs = R.groupby("race_id")["horse"].transform("size") if "race_id" in R.columns else pd.Series(np.nan, index=R.index)
    T = pd.DataFrame({
        "horse_id": keys.map(ids).astype(float).values, "date": pd.to_datetime(R["date"].astype(str).str[:10]).values, "jockey": R["jockey"].values,
        "venue": R["venue"].values, "distance": R["distance"].values, "going": R["going"].values,
        "weightCarried": pd.to_numeric(R["weight_carried"], errors="coerce").values if "weight_carried" in R.columns else np.nan,
        "barrier": R["barrier"].values, "field_size": fs.values, "race_class": R["race_class"].values, "trackGrading": R["track_grading"].values}, index=R.index)
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        f, corr = C.predict(T, meta=meta, booster=booster, rp=rp, rel_booster=rel, co=co, clip=None)
    out.loc[R.index] = f + corr
    return out


if __name__ == "__main__":
    if "--train" in sys.argv:
        train()
    elif "--check" in sys.argv:
        import runners_io
        r = runners_io.read_runners(low_memory=False)
        t = sr._melbourne_today()
        r = r[r["date"].astype(str) >= t.isoformat()].copy()
        p = predict(r, pd.Series(True, index=r.index))
        old = sr.compute(r)
        print(f"{int(p.notna().sum()):,} of {len(r):,} rated; old Spd rated {int(old.notna().sum()):,}")
        both = p.notna() & old.notna()
        print("corr with old rating:", round(float(np.corrcoef(p[both], old[both])[0, 1]), 3), "| mean new", round(float(p[both].mean()), 2), "old", round(float(old[both].mean()), 2),
              "| sd new", round(float(p[both].std()), 2), "old", round(float(old[both].std()), 2))
    else:
        print(__doc__)
