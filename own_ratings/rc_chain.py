"""own_ratings/rc_chain.py -- own WPR for every state from racing.com results (data/gps/rc_results_runs_*.parquet).

History (up to --start) is seeded from TopRate's ratings in race_results_20*.csv.gz; from --start on, each race is chained from
racing.com's margins, weights and distances alone (no TopRate input). Sex and birth date come from the history table by horse
name (racing.com has neither); horses never seen before get a rating from the race but no weight/age term, so their wpr_own is
atw plus the race's mean weight term. Where TopRate also rated the run (until 5 Oct 2026) the two are compared.

  python -m own_ratings.rc_chain [--start 2026-09-12] [--rc data/gps/rc_results_runs_2026.parquet] [--out own_wpr_rc.csv.gz]
"""
import argparse
import glob

import numpy as np
import pandas as pd

from . import chain, core
from .rc_join import load_rc_results, norm_horse

COLS = ["race_id", "date", "horse_id", "horse", "distance", "weightCarried", "horse_sex", "horse_foaled", "wpr",
        "marginFinish", "positionFinish", "isBarrierTrial", "is_jumpout"]


def load_history():
    files = [f for f in sorted(glob.glob("race_results_20*.csv.gz")) if "_rc" not in f]   # never read our own extension back in
    d = pd.concat((pd.read_csv(f, usecols=lambda c: c in COLS, low_memory=False) for f in files), ignore_index=True)
    d = d[(d.isBarrierTrial != 1) & (d.is_jumpout.fillna(0) != 1)].drop_duplicates(["race_id", "horse_id"])
    d["h"] = d.horse.map(norm_horse)
    return d


def horse_attrs(hist):
    """latest (horse_id, sex, foaled) per normalised name."""
    h = hist.sort_values("date").drop_duplicates("h", keep="last")
    return h.set_index("h")[["horse_id", "horse_sex", "horse_foaled"]]


def build_obs(rc, attrs, start):
    o = rc[(rc.race_date >= start) & rc.finish.notna()].copy()
    o = o.join(attrs, on="h")
    o["horse_id"] = o["horse_id"].where(o["horse_id"].notna(), "rc" + o["horse_code"].astype(str))
    o["race_id"] = o.meeting_code.astype(str) + "_" + o.race_no.astype(int).astype(str).str.zfill(2)
    o = o.rename(columns={"race_date": "date", "race_distance": "distance", "weight_kg": "weightCarried"})
    o["margin"] = np.where(o.finish == 1, 0.0, o.margin_l)
    return o


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--start", default="2026-09-12")
    ap.add_argument("--rc", default=None, help="one parquet file (default: all data/gps/rc_results_runs_*.parquet)")
    ap.add_argument("--out", default=None)
    a = ap.parse_args()
    rc = load_rc_results(a.rc) if a.rc else load_rc_results()
    hist = load_history()
    past = hist[(hist.date < a.start) & hist.wpr.notna() & (hist.date >= "2024-01-01")]
    h = chain.seed_history(past)
    print(f"seeded {len(h)} horses from {len(past)} TopRate-rated runs before {a.start}")
    obs = build_obs(rc, horse_attrs(hist), a.start)
    print(f"racing.com runs from {a.start}: {len(obs)} in {obs.race_id.nunique()} races, "
          f"{obs.horse_id.astype(str).str.startswith('rc').mean():.1%} horses new to the history table")
    o = chain.run_chain(obs, h)
    # horses without age/sex: use the race's mean weight term so wpr_own stays on the same level
    o["wadj_f"] = o.wadj.fillna(o.groupby("race_id").wadj.transform("mean")).fillna(0.0)
    o["wpr_own"] = o.atw + o.wadj_f
    cmp = o.merge(hist[hist.wpr.notna()][["date", "h", "wpr"]].drop_duplicates(["date", "h"]), on=["date", "h"], how="inner")
    if len(cmp):
        cmp["err"] = cmp.wpr_own - cmp.wpr
        cmp["r_own"] = cmp.groupby("race_id").wpr_own.rank(ascending=False)
        cmp["r_tr"] = cmp.groupby("race_id").wpr.rank(ascending=False)
        print(f"vs TopRate on {len(cmp)} runs ({cmp.date.min()} to {cmp.date.max()}): MAE {cmp.err.abs().mean():.2f} "
              f"RMSE {np.sqrt((cmp.err ** 2).mean()):.2f} bias {cmp.err.mean():+.2f} within-race rank corr {cmp.r_own.corr(cmp.r_tr):.3f}")
        print(cmp.groupby("date").err.agg(["size", "mean", lambda s: s.abs().mean()]).rename(columns={"<lambda_0>": "mae"}).round(2).to_string())
    print(f"n_inform mean {o.n_inform.mean():.1f}; races with no informing runner: {(o.groupby('race_id').n_inform.first() == 0).mean():.1%}")
    if a.out:
        keep = ["date", "race_id", "meeting_code", "state", "venue", "horse", "horse_id", "distance", "weightCarried", "finish", "margin",
                "atw", "wpr_own", "rs_hat", "n_inform"]
        o[[c for c in keep if c in o.columns]].to_csv(a.out, index=False)
        print("wrote", a.out)


if __name__ == "__main__":
    main()
