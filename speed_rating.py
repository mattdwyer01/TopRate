"""speed_rating.py -- the pre-race speed rating shown on the Race page (added 16 Oct 2026).

What it is: for every earlier run of a horse, a time-based speed figure in lengths against par (positive = faster than par): the run's finish time
(winners_time + 0.147 s x beaten margin, winner's own margin clipped to 0) minus a par time for the track, distance, class, going, grading, field size,
season and mean weight (a LightGBM fitted on winners' times, speed_models/par_v2.txt) minus a same-day venue variant from the other races that day.
The rating is the recency-weighted mean of the horse's earlier figures (EWM, halflife 4 runs, at least 2 runs), as of the day before the race.

Why this version: research/speed_rating_variants.py (15,111 races 2025-07+, 16 Oct 2026). Par v2 plus a long recency-weighted memory was the best
simple calculation (top pick wins 20.0% vs 17.0% for the mean of the last 3 on par v1; added to L3 +0.012 nats vs +0.005). A learned LightGBM on the
figure history was a little better still (20.3%, +0.015) but needs a second artifact and is relative to the field, so it was not used.
Recent runs: figures need winners_time. The results files carry it but stop on 8 Oct 2026 (the racing.com results file that followed has none), so every
day after the last day those files cover is read from the runner-page store (data/tr_form), which the daily runner-page fetch keeps up to date, so the
rating stays current without anything extra. A horse with fewer than 2 earlier figures has no rating.

usage:
  python speed_rating.py --train      refit the par model (writes speed_models/par_v2.txt), run once a year
  python speed_rating.py --check      print the rating for upcoming runners in runners.csv
"""
import glob
import json
import re
import sys
from datetime import date, datetime, timedelta
from pathlib import Path
from zoneinfo import ZoneInfo

import numpy as np
import pandas as pd

DIR = Path(__file__).parent
MODEL = DIR / "speed_models" / "par_v2.txt"
FORM_DIR = DIR / "data" / "tr_form"
SEC = 0.147                  # seconds per length
HALFLIFE = 4.0               # runs
MIN_RUNS = 2
TRAIN_FROM = "2020-01-01"
TRAIN_TO = "2025-12-31"      # 2026 runs are out of sample for the par model, like the research test
COLUMN = "spd_fig"
WINDOW_DAYS = 28             # rows dated within this many days before today (and every later date) are (re)computed
YEARS_BACK = 2               # results files read: this year and the previous ones
USE = ["race_id", "date", "horse", "track", "distance", "going", "positionFinish", "marginFinish", "field_size", "weightCarried", "winners_time",
       "isBarrierTrial", "race_class", "trackGrading"]
CATS = ["track", "gname", "cls", "grading"]
FEATS = ["distance", "gnum", "field_size", "doy", "mw"]


def _melbourne_today():
    return datetime.now(ZoneInfo("Australia/Melbourne")).date()


def _norm(d):
    d["date"] = pd.to_datetime(d["date"])
    d = d[d["isBarrierTrial"].fillna(False).astype(bool) == False]
    d = d[~d["race_class"].astype(str).str.contains("HUR|STE|JUMP", case=False, na=False)]
    d = d.dropna(subset=["horse", "winners_time", "marginFinish", "distance"])
    d = d[(d["winners_time"] > 20) & (d["winners_time"] < 400)].drop_duplicates(["race_id", "horse"])
    d["gnum"] = d["going"].astype(str).str.extract(r"(\d+)").astype(float)
    d["gname"] = d["going"].astype(str).str.extract(r"([A-Za-z]+)")[0]
    d["cls"] = d["race_class"].astype(str).str.replace(r"\d+", "", regex=True)
    return d


def load_form_runs(after):
    """Runs after the date `after` from the runner-page store (data/tr_form, kept up to date by the daily runner-page fetch): TopRate's own record of every
    past run of every horse that has been declared again, with the race's winning time and each runner's margin. Partial fields (only runners whose page
    was fetched), so the venue-day allowance is built from the races that are known. Where both sources cover a day they agree (winning time 100%,
    margin 99.96% of 2,666 runs, 20 Sep to 8 Oct 2026)."""
    import gzip
    runs = []
    for f in sorted(FORM_DIR.glob("*.json.gz")):
        if f.stem < str(after)[:7]:
            continue
        try:
            with gzip.open(f, "rt") as fh:
                runs += list(json.load(fh).get("runs", {}).values())
        except Exception:
            continue
    if not runs:
        return pd.DataFrame(columns=USE)
    t = pd.DataFrame(runs)
    t = t[t["date"].astype(str) > str(after)]
    for c in ("isJumpout", "isBarrierTrial", "winnersTime", "marginFinish", "starters", "weightCarried", "trackGrading", "class"):
        if c not in t.columns:
            t[c] = np.nan
    t["isBarrierTrial"] = t["isBarrierTrial"].fillna(False).astype(bool) | t["isJumpout"].fillna(False).astype(bool)
    t["marginFinish"] = t["marginFinish"].where(t["marginFinish"].notna() | (t["positionFinish"] != 1), 0.0)
    d = pd.DataFrame({"race_id": t["raceId"], "date": t["date"], "horse": t["horse"], "track": t["track"], "distance": t["distance"], "going": t["going"],
                      "positionFinish": t["positionFinish"], "marginFinish": t["marginFinish"], "field_size": t["starters"], "weightCarried": t["weightCarried"],
                      "winners_time": t["winnersTime"], "isBarrierTrial": t["isBarrierTrial"], "race_class": t["class"], "trackGrading": t["trackGrading"]})
    return d


def load_results(first_year, form_from=None):
    """Results files from first_year, then the runner-page store for every day after the last day the files cover (or after form_from, for testing)."""
    files = [f for f in sorted(glob.glob(str(DIR / "race_results_20*.csv.gz"))) if not f.endswith("_rc.csv.gz") and int(f[-11:-7]) >= first_year]
    d = pd.concat([pd.read_csv(f, usecols=lambda c: c in USE, low_memory=False) for f in files], ignore_index=True)
    d["date"] = pd.to_datetime(d["date"])
    after = pd.Timestamp(form_from) if form_from else d["date"].max()
    d = d[d["date"] <= after]
    f = load_form_runs(after.date())
    if len(f):
        d = pd.concat([d, f], ignore_index=True)
    return _norm(d)


def races_table(d):
    r = d.groupby("race_id").agg(date=("date", "first"), track=("track", "first"), distance=("distance", "first"), gname=("gname", "first"), cls=("cls", "first"),
                                 winners_time=("winners_time", "first"), field_size=("field_size", "first"), grading=("trackGrading", "first"),
                                 gnum=("gnum", "first"), mw=("weightCarried", "mean")).reset_index()
    r["doy"] = r["date"].dt.dayofyear
    r["perkm"] = r["winners_time"] / r["distance"] * 1000
    return r


def _X(r, cats=None):
    X = r[FEATS + CATS].copy()
    for c in CATS:
        X[c] = X[c].astype(str).astype("category")
    return X


def train():
    import lightgbm as lgb
    d = load_results(int(TRAIN_FROM[:4]))
    r = races_table(d)
    tr = (r["date"] >= TRAIN_FROM) & (r["date"] <= TRAIN_TO)
    P = dict(objective="l2", learning_rate=0.05, num_leaves=63, min_data_in_leaf=20, feature_fraction=0.9, lambda_l2=5, cat_smooth=10, verbose=-1, num_threads=4)
    X = _X(r)
    m = lgb.train(P, lgb.Dataset(X[tr], r["perkm"][tr]), 500)
    MODEL.parent.mkdir(exist_ok=True)
    m.save_model(str(MODEL))
    print(f"par model -> {MODEL} ({MODEL.stat().st_size / 1e6:.1f} MB), {int(tr.sum()):,} races {TRAIN_FROM} to {TRAIN_TO}")


def _variant(r, dev_s):
    """Shrunk mean of the OTHER races' clipped residual (seconds) at the same venue and day."""
    x = dev_s.clip(-6, 6)
    key = [r["track"], r["date"]]
    n = x.groupby(key).transform("count")
    s = x.groupby(key).transform("sum")
    m = n - x.notna().astype(int)
    others = (s - x.fillna(0)) / m.clip(lower=1)
    return np.where(m >= 2, others * (m / (m + 2.0)), 0.0)


def figures(d):
    """Per-run speed figure (lengths vs par) for every run in d."""
    import lightgbm as lgb
    booster = lgb.Booster(model_file=str(MODEL))
    r = races_table(d)
    r["par"] = booster.predict(_X(r)) * r["distance"] / 1000
    dev = r["winners_time"] - r["par"]
    r["fast"] = -(dev - _variant(r, dev)) / SEC
    d = d.merge(r[["race_id", "fast"]], on="race_id", how="left")
    d["sp"] = d["fast"] - d["marginFinish"].clip(lower=0, upper=25)
    return d.dropna(subset=["sp"])


def history(d):
    """(key, date, rating after this run): the EWM of the horse's figures including this run."""
    d = figures(d)
    d["key"] = d["horse"].astype(str).str.lower().str.strip()
    d = d.sort_values(["key", "date"])
    d["rating"] = d.groupby("key", sort=False)["sp"].transform(lambda s: s.ewm(halflife=HALFLIFE, min_periods=MIN_RUNS).mean())
    return d.dropna(subset=["rating"])[["key", "date", "rating"]].sort_values("date")


def compute(runners_df, today=None):
    """Speed rating (lengths vs par, higher = faster) for runners dated in the last WINDOW_DAYS or later; NaN elsewhere. Index matches runners_df."""
    today = today or _melbourne_today()
    out = pd.Series(np.nan, index=runners_df.index)
    dts = pd.to_datetime(runners_df["date"].astype(str).str[:10], errors="coerce")
    sel = dts >= pd.Timestamp(today - timedelta(days=WINDOW_DAYS))
    if not sel.any() or not MODEL.exists():
        return out
    h = history(load_results(today.year - YEARS_BACK))
    q = pd.DataFrame({"date": dts[sel], "key": runners_df.loc[sel, "horse"].astype(str).str.lower().str.strip()}).sort_values("date")
    m = pd.merge_asof(q.reset_index(), h, on="date", by="key", allow_exact_matches=False, tolerance=pd.Timedelta(days=400)).set_index("index")
    out.loc[m.index] = m["rating"].values
    return out


def apply(runners_df, today=None):
    """Write the rating into runners_df[COLUMN] (existing values outside the window are kept)."""
    new = compute(runners_df, today)
    if COLUMN not in runners_df.columns:
        runners_df[COLUMN] = np.nan
    runners_df[COLUMN] = pd.to_numeric(runners_df[COLUMN], errors="coerce")
    upd = new.notna()
    runners_df.loc[upd, COLUMN] = new[upd].round(2)
    print(f"  speed rating: {int(upd.sum()):,} of {len(runners_df):,} runners rated")
    return runners_df


if __name__ == "__main__":
    if "--train" in sys.argv:
        train()
    elif "--check" in sys.argv:
        import runners_io
        r = runners_io.read_runners(low_memory=False)
        t = _melbourne_today()
        r = r[r["date"].astype(str) >= t.isoformat()].copy()
        r = apply(r)
        print(r[["date", "venue", "race", "horse", COLUMN]].dropna(subset=[COLUMN]).head(20).to_string())
    else:
        print(__doc__)
