"""Settle runner rows and extend the horse form history from racing.com results and our own ratings.

toprate.au no longer answers (403), so update_results() cannot settle races and wpr_form_history.csv.gz stopped growing on 8 Oct 2026.
This step does their job from data we have:

  1. runners.csv: for every row of a date racing.com has results for and that is not yet `resulted`, set finish_position, won,
     placed, starting_price_sp, margin_finish, wpr_actual (our own rating of the run, the own-chain ratings file),
     wpr_actual_rank, resulted = 1 and interim_resulted = 1. Values follow update_results(): the winner's margin_finish is
     minus the margin to the runner-up, everyone else's is the margin to the winner.
  2. wpr_form_history.csv.gz: append one row per rated run (own file, plus TopRate-rated runs of the results files that the form feed
     never captured) so the horse page's Recent runs table and chart show them. The rating is OUR plain WPR for the run (no ATW shift).

Idempotent: rows already resulted, and form rows already present for (horse, date), are left alone.

  python -m own_ratings.apply_results --dry-run          report only
  python -m own_ratings.apply_results                    write runners.csv and wpr_form_history.csv.gz in place
"""
import argparse
import glob
import gzip
import io
import sys

import numpy as np
import pandas as pd

import runners_io
from own_ratings.rc_join import load_rc_results, match_runners, norm_horse

FORM_FILE = "wpr_form_history.csv.gz"
FORM_FROM = "2025-01-01"          # form rows are filled from here (the form feed missed runs before 8 Oct 2026; 103k runs back to Jan 2025 added 14 Oct 2026)


def _num(s):
    return pd.to_numeric(s, errors="coerce")


def settle_runners(runners: pd.DataFrame, rc: pd.DataFrame, own: pd.DataFrame):
    """Return (runners, n_rows, n_races). `runners` is the all-string runners frame (read with dtype=str)."""
    rc_dates = set(rc.race_date.astype(str).unique())
    # Scratched rows are skipped (the column holds "1" or "1.0"): a horse entered in two races of a day and scratched from one would
    # otherwise take the other race's result by name.
    scr = pd.to_numeric(runners.scratched, errors="coerce").fillna(0) == 1
    todo = runners[(runners.date.astype(str).str[:10].isin(rc_dates)) & (runners.resulted.astype(str) != "1") & ~scr]
    if todo.empty:
        return runners, 0, 0
    sub = todo[["run_id", "date", "venue", "horse"]].copy()
    sub["distance"] = _num(todo["distance"])
    m = match_runners(sub, rc)
    if m.empty:
        return runners, 0, 0
    m["finish"] = _num(m["finish"])
    m["margin_l"] = _num(m["margin_l"])
    m["sp"] = _num(m["sp"])
    m["rid"] = m["run_id"].astype(str)
    # race key = rc meeting + race number (a race is one rc race)
    m["rk"] = m["meeting_code"].astype(str) + "_" + m["race_no"].astype(str)
    # own rating of the run, by (date, horse)
    o = own.copy()
    o["h"] = o.horse.map(norm_horse)
    o["d"] = o.date.astype(str).str[:10]
    o = o.dropna(subset=["wpr"]).drop_duplicates(["d", "h"], keep="last")
    m["h"] = m["horse"].map(norm_horse)
    m["d"] = m["date"].astype(str).str[:10]
    m = m.merge(o[["d", "h", "wpr"]], on=["d", "h"], how="left")
    fin = m[m.finish.between(1, 60)]
    # winner's margin is minus the lead over the runner-up
    second = fin[fin.finish == 2].groupby("rk").margin_l.min()
    m["mf"] = m.margin_l
    win = m.finish == 1
    m.loc[win, "mf"] = -m.loc[win, "rk"].map(second).fillna(0.0)
    m["rank"] = m.groupby("rk").wpr.rank(ascending=False, method="min")
    idx = runners.index[runners.run_id.astype(str).isin(set(m.rid))]
    byrid = m.set_index("rid")
    r = runners.loc[idx]
    rid = r.run_id.astype(str)
    f = rid.map(byrid.finish)
    ran = f.between(1, 60)
    out = runners.copy()
    out.loc[idx, "finish_position"] = np.where(ran, f.round().astype("Int64").astype(str), "")
    out.loc[idx, "won"] = np.where(f == 1, "1", "0")
    out.loc[idx, "placed"] = np.where(f.between(1, 3), "1", "0")
    sp = rid.map(byrid.sp)
    out.loc[idx, "starting_price_sp"] = np.where(sp > 1, sp.round(2).astype(str), out.loc[idx, "starting_price_sp"])
    mf = rid.map(byrid.mf)
    out.loc[idx, "margin_finish"] = np.where(ran & mf.notna(), mf.round(2).astype(str), "")
    w = rid.map(byrid.wpr)
    out.loc[idx, "wpr_actual"] = np.where(w.notna(), w.round(1).astype(str), "")
    rk = rid.map(byrid["rank"])
    out.loc[idx, "wpr_actual_rank"] = np.where(rk.notna(), rk.astype("Int64").astype(str), "")
    out.loc[idx, "resulted"] = "1"
    out.loc[idx, "interim_resulted"] = "1"
    return out, len(idx), m.rk.nunique()


def new_form_rows(own: pd.DataFrame, ratings: pd.DataFrame) -> pd.DataFrame:
    """Rated runs from FORM_FROM on that the form file does not hold, in the form file's columns.

    `ratings` is the own-chain output (rebuild_history: date, horse_id, horse, wpr); the race facts come from the results files. The
    rating is OUR plain WPR; nothing from TopRate's wpr column is used.
    """
    fh = pd.read_csv(FORM_FILE, usecols=["horse", "date"], low_memory=False)
    have = set(zip(fh.horse.astype(str).str.strip().str.lower(), fh.date.astype(str).str[:10]))
    r = ratings.dropna(subset=["wpr"]).copy()
    r["d"] = r.date.astype(str).str[:10]
    r["hl"] = r.horse.astype(str).str.strip().str.lower()
    r = r[r.d >= FORM_FROM]
    r = r[[(h, d) not in have for h, d in zip(r.hl, r.d)]].drop_duplicates(["hl", "d"], keep="last")
    if r.empty:
        return r
    parts = []
    for p in sorted(glob.glob("race_results_20*.csv.gz")):
        d = pd.read_csv(p, low_memory=False)
        d["date"] = d.date.astype(str).str[:10]
        parts.append(d[d.date >= FORM_FROM])
    res = pd.concat(parts, ignore_index=True)
    res["hl"] = res.horse.astype(str).str.strip().str.lower()
    res = res.drop_duplicates(["hl", "date"], keep="first")
    res = res.merge(r[["hl", "d", "wpr"]].rename(columns={"wpr": "own_wpr"}), left_on=["hl", "date"], right_on=["hl", "d"], how="inner")
    cols = list(pd.read_csv(FORM_FILE, nrows=0).columns)
    out = pd.DataFrame(index=res.index, columns=cols, dtype=object)
    for c in cols:
        if c in res.columns:
            out[c] = res[c]
    # TopRate's sectional indexes, race-shape reads and rating status are its own analysis: never copied into the form history
    for c in cols:
        if c.startswith(("sect_", "raceShape")) or c == "wprStatus":
            out[c] = None
    out["scrape_date"] = res["date"]
    out["wpr"] = res["own_wpr"].round(1)
    out["venue"] = res["track"] if "track" in res else None
    return out.reset_index(drop=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--no-form", action="store_true")
    ap.add_argument("--ratings", default="own_ratings_history.csv.gz", help="own-chain output from rebuild_history (needed for the form rows)")
    a = ap.parse_args()
    rc = load_rc_results()
    ratings = pd.read_csv(a.ratings, low_memory=False)      # own chain from rebuild_history: no TopRate rating anywhere in its inputs
    own = ratings
    path = runners_io.live_path()
    if str(path).endswith("runners.csv"):
        runners = pd.read_csv(path, dtype=str, keep_default_na=False, low_memory=False)
        new, n, races = settle_runners(runners, rc, own)
        print(f"runners: {n} rows in {races} races settled")
        if n and not a.dry_run:
            new.to_csv(path, index=False)
    else:
        print("runners.csv not found, nothing to do")
    if not a.no_form:
        rows = new_form_rows(own, ratings)
        print(f"form history: {len(rows)} new rows ({rows.date.min() if len(rows) else '-'} to {rows.date.max() if len(rows) else '-'})")
        if len(rows) and not a.dry_run:
            fh = pd.read_csv(FORM_FILE, low_memory=False)
            allrows = pd.concat([fh, rows[fh.columns]], ignore_index=True)
            allrows.to_csv(FORM_FILE, index=False, compression="gzip")


if __name__ == "__main__":
    sys.exit(main())
