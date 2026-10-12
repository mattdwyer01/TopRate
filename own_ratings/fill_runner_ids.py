"""Give runner rows built from racing.com fields (field_source = racing.com) the ids and early prices the scorers need.

Those rows start without a horse_id (the bet-signal scorer, the ATW offsets and other code keyed by horse_id skip a race unless every
runner has one) and, for races more than ~2 hours away, without a price (the TAB poller only prices races inside that window).

  horse_id   TopRate's id for the horse name from the results files (latest run wins); a horse the results files do not know gets the same
             stand-in id our own ratings file uses, HORSE_BASE + racing.com horse code (own_ratings/build_results_ext.py).
  prices     fixed_win_price / open_price from the racing.com field file (data/rc_fields/<date>.json, the book's latest win price), only for
             rows that still have none, so a TAB price is never overwritten. It is an early price, not a closing one.

Idempotent. Operates on the all-string runners frame so nothing else in the file changes.

  python -m own_ratings.fill_runner_ids --dry-run
  python -m own_ratings.fill_runner_ids
"""
import argparse
import glob
import sys

import pandas as pd

import rc_field_rows
import runners_io
from own_ratings.build_results_ext import HORSE_BASE
from own_ratings.rc_join import norm_horse


def horse_id_map() -> dict:
    """{normalised horse name: horse_id}, the id of the horse's latest run in any results file."""
    parts = []
    for p in sorted(glob.glob("race_results_20*.csv.gz")):
        d = pd.read_csv(p, usecols=["horse", "horse_id", "date"], low_memory=False)
        parts.append(d.dropna(subset=["horse", "horse_id"]))
    d = pd.concat(parts, ignore_index=True)
    d["h"] = d.horse.map(norm_horse)
    d["horse_id"] = pd.to_numeric(d.horse_id, errors="coerce")
    d = d.dropna(subset=["horse_id"]).sort_values("date", kind="stable")
    d["real"] = d.horse_id < HORSE_BASE
    # a TopRate id beats a stand-in; among equals the latest run wins
    d = d.sort_values(["real", "date"], kind="stable")
    return {h: int(i) for h, i in zip(d.h, d.horse_id)}


def fill(runners: pd.DataFrame):
    """Return (runners, n_ids, n_prices). `runners` is the all-string frame."""
    out = runners.copy()
    rc = out.get("field_source", pd.Series("", index=out.index)).astype(str) == "racing.com"
    scr = pd.to_numeric(out.scratched, errors="coerce").fillna(0) == 1
    need_id = rc & (out.horse_id.astype(str).str.strip() == "")
    px = pd.to_numeric(out.fixed_win_price, errors="coerce")
    need_px = rc & ~scr & px.isna() & (out.resulted.astype(str) != "1")
    if not (need_id.any() or need_px.any()):
        return out, 0, 0
    ids = horse_id_map() if need_id.any() else {}
    n_id = n_px = 0
    races = out[need_id | need_px].groupby(["date", "venue", "race"], sort=False).groups
    for (date, venue, race), idx in races.items():
        date = str(date)[:10]
        try:
            dist = float(out.loc[idx[0], "distance"])
        except (TypeError, ValueError):
            dist = None
        m, r = rc_field_rows.find_race(date, venue, int(float(race)), dist)
        byname = {norm_horse(u.get("horse")): u for u in (r or {}).get("runners", [])}
        for i in idx:
            h = norm_horse(out.at[i, "horse"])
            u = byname.get(h) or {}
            if need_id[i]:
                hid = ids.get(h)
                if hid is None and u.get("horse_code"):
                    hid = HORSE_BASE + int(u["horse_code"])
                if hid is not None:
                    out.at[i, "horse_id"] = str(int(hid))
                    n_id += 1
            if need_px[i] and u.get("win_price") and float(u["win_price"]) > 1:
                out.at[i, "fixed_win_price"] = str(round(float(u["win_price"]), 2))
                if str(out.at[i, "open_price"]).strip() == "":
                    out.at[i, "open_price"] = out.at[i, "fixed_win_price"]
                n_px += 1
    return out, n_id, n_px


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    a = ap.parse_args()
    path = runners_io.LIVE_CSV
    if not path.exists():
        print("runners.csv not found")
        return 0
    runners = pd.read_csv(path, dtype=str, keep_default_na=False, low_memory=False)
    new, n_id, n_px = fill(runners)
    print(f"horse_id filled on {n_id} rows, early price on {n_px} rows")
    if (n_id or n_px) and not a.dry_run:
        new.to_csv(path, index=False)
    return 0


if __name__ == "__main__":
    sys.exit(main())
