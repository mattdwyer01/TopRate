"""own_ratings/build_results_ext.py -- write our own-rated runs after TopRate stopped as race_results_2026_rc.csv.gz.

The projection code (projection/features.py, run.py, add_weight_adj.py) reads every race_results_20*.csv.gz, so a file with the
same columns is picked up with no change to it. Rows are racing.com results from the day after TopRate's last rated run, with
`wpr` = our own rating (own_ratings/rc_chain.py: history seeded from TopRate, every later race chained from racing.com margins).
Jockey, trainer, class, going and run_id come from toprate_runners.csv when the horse matches (own_ratings/rc_join.py), the rest
is left blank. Numeric stand-in ids (above 8e9) are used for races and horses TopRate never had, so id columns stay numeric.
The file is rebuilt from scratch on every run (deterministic: TopRate history + racing.com results), nothing accumulates.

  python -m own_ratings.build_results_ext [--start 2026-10-06] [--out race_results_2026_rc.csv.gz]
"""
import argparse

import numpy as np
import pandas as pd

import runners_io
from . import chain, core, rc_chain
from .rc_join import load_rc_results, match_runners

RACE_BASE = 8_000_000_000
HORSE_BASE = 9_000_000_000


def build(start=None, rc=None, hist=None, runners=None):
    rc = load_rc_results() if rc is None else rc
    hist = rc_chain.load_history() if hist is None else hist
    rated = hist[hist.wpr.notna()]
    last = rated.date.max()
    start = start or str((pd.to_datetime(last) + pd.Timedelta(days=1)).date())
    past = rated[(rated.date < start) & (rated.date >= "2024-01-01")]
    h = chain.seed_history(past)
    obs = rc_chain.build_obs(rc, rc_chain.horse_attrs(hist), start)
    o = chain.run_chain(obs, h)
    o["wadj_f"] = o.wadj.fillna(o.groupby("race_id").wadj.transform("mean")).fillna(0.0)
    o["wpr_own"] = o.atw + o.wadj_f

    # enrich from our runners file where the horse matches (jockey, trainer, class, going, TopRate race/run ids)
    runners = runners_io.read_runners() if runners is None else runners
    runners = runners[runners["date"].astype(str).str[:10] >= start]
    mm = match_runners(runners, rc)                          # run_id, venue (ours), meeting_code, race_no, h per matched runner
    extra = [c for c in ["race_id", "going", "track_grading", "race_class", "jockey", "trainer"] if c in runners.columns]
    mm = mm.merge(runners[["run_id"] + extra].rename(columns={"race_id": "race_id_tr", "going": "going_tr"}), on="run_id", how="left")
    # one TopRate-style race id and track name per racing.com race: the commonest among its matched runners
    race_lvl = mm.groupby(["meeting_code", "race_no"]).agg(race_id_tr=("race_id_tr", lambda s: s.mode().iloc[0]),
                                                           track_tr=("venue", lambda s: s.mode().iloc[0])).reset_index()
    run_lvl = (mm.drop_duplicates(["meeting_code", "race_no", "h"])
                 [["meeting_code", "race_no", "h", "run_id", "going_tr"] + [c for c in extra if c not in ("race_id", "going")]])
    o = o.merge(race_lvl, on=["meeting_code", "race_no"], how="left").merge(run_lvl, on=["meeting_code", "race_no", "h"], how="left")

    out = pd.DataFrame({
        "race_id": o.race_id_tr.fillna(RACE_BASE + o.meeting_code.astype(float) * 100 + o.race_no.astype(float)).astype("int64"),
        "date": o.date,
        "horse_id": [int(x) if not str(x).startswith("rc") else HORSE_BASE + int(str(x)[2:]) for x in o.horse_id],
        "horse": o.horse,
        "track": o.track_tr.fillna(o.venue),
        "distance": o.distance,
        "going": o.going_tr.fillna(o.going),
        "wpr": o.wpr_own.round(2),
        "weightCarried": o.weightCarried,
        "barrier": o.barrier,
        "field_size": o.groupby("race_id").horse.transform("size"),
        "race_class": o.get("race_class"),
        "trackGrading": o.get("track_grading"),
        "horse_age": core.racing_age(o.date, o.horse_foaled) if "horse_foaled" in o else np.nan,
        "horse_sex": o.horse_sex,
        "jockey": o.get("jockey"),
        "trainer": o.get("trainer"),
        "positionFinish": o.finish,
        "marginFinish": o.margin,
        "priceStarting": o.sp,
        "isBarrierTrial": 0,
        "is_jumpout": 0,
        "run_id": o.run_id,
        "wpr_source": "own_rc",
    })
    return out.drop_duplicates(["race_id", "horse_id"]), start


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--start", default=None)
    ap.add_argument("--out", default="race_results_2026_rc.csv.gz")
    a = ap.parse_args()
    out, start = build(a.start)
    out.to_csv(a.out, index=False)
    print(f"wrote {a.out}: {len(out)} runs, {out.race_id.nunique()} races, {out.date.min()} to {out.date.max()} (start {start}); "
          f"TopRate-style race ids {(out.race_id < RACE_BASE).mean():.1%}, jockey known {out.jockey.notna().mean():.1%}")


if __name__ == "__main__":
    main()
