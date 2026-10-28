"""Forward log for the 'lower-rated but forward on the map' idea (28 Oct 2026).

The idea (CLAUDE.md, forward-map entries): a runner a few Proj points below the top rated, but forecast closer to the lead, may win more than its price. Backtests on
the results files (22,055 and 12,575 races) found only a small win-rate lift and no profit; the first weeks of live Proj looked better. This log judges it on races that were
not used to find it: every non-scratched runner in each race that has a Trip map forecast is stored with the Proj, its forecast gap (lengths behind the projected leader at
about 800m), Nett, Spd, and the last fixed price read before the jump, then labelled with the result and the starting price. Any rule (points below, lengths closer, price floor,
state, distance, going) can be applied afterwards by research/forward_log_report.py, so the rule is not fixed here.

data/forward_log/<date>.json.gz = {"rows": {run_id: {...}}}. A row is rewritten on every pass until the race start has passed (so `price` is the last price read before the jump
and `price_first` the first); it is then frozen. Labels (won, finish, sp) are added once the race has resulted. `proj_made` is when that Proj was logged: a Proj made after the
start would be hindsight, report it.

Usage: python forward_log.py snapshot [--from D --days N]   (default today and tomorrow, Melbourne date)
       python forward_log.py labels                         (fill results for logged dates before today)
Inputs: runners.csv (live file), trip_map.json.
"""
import argparse
import datetime as dt
import gzip
import json
import sys
from pathlib import Path
from zoneinfo import ZoneInfo

import pandas as pd

ROOT = Path(__file__).parent
DIR = ROOT / "data" / "forward_log"
USE = ["run_id", "race_id", "date", "venue", "state", "race", "distance", "going", "start_time", "tab_number", "barrier", "horse", "jockey", "trainer",
       "wprp_proj", "wprp_model", "wprp_made", "wpr_nett", "spd_fig", "fixed_win_price", "starting_price_sp", "scratched", "won", "finish_position",
       "placed", "interim_resulted", "resulted"]


def _num(x):
    try:
        v = float(x)
        return None if v != v else v
    except (TypeError, ValueError):
        return None


def _melb_today():
    return dt.datetime.now(ZoneInfo("Australia/Melbourne")).date()


def _read(path):
    try:
        with gzip.open(path, "rt") as fh:
            return json.load(fh).get("rows", {})
    except Exception:
        return {}


def _write(path, rows):
    path.parent.mkdir(parents=True, exist_ok=True)
    with gzip.GzipFile(path, "wb", mtime=0) as gz:
        gz.write(json.dumps({"rows": rows}, separators=(",", ":"), sort_keys=True).encode())


def _runners():
    p = ROOT / "runners.csv"
    d = pd.read_csv(p, usecols=lambda c: c in set(USE), low_memory=False)
    return d


def _trip_map():
    try:
        return json.load(open(ROOT / "trip_map.json")).get("races", {})
    except Exception:
        return {}


def snapshot(dates):
    rn = _runners()
    tm = _trip_map()
    fc = {}   # (race_id, run_id) -> (gap, map kind, error sd)
    for rid, v in tm.items():
        for u in v.get("runners", []):
            fc[(str(rid), str(u.get("rid")))] = (_num(u.get("gap")), v.get("state"), (v.get("err") or {}).get("gap"))
    now = dt.datetime.now(dt.timezone.utc)
    stamp = now.strftime("%Y-%m-%dT%H:%MZ")
    for date in dates:
        d = rn[(rn.date.astype(str).str[:10] == date) & (rn.scratched.fillna(0) != 1)].dropna(subset=["run_id", "race_id", "race"])
        path = DIR / f"{date}.json.gz"
        have = _read(path)
        merged = dict(have)
        n = 0
        for r in d.itertuples(index=False):
            key = str(int(r.run_id))
            f = fc.get((str(int(r.race_id)), key))
            if f is None or f[0] is None:
                continue          # only races with a forecast for this runner
            old = have.get(key)
            st = str(r.start_time)[:16] if isinstance(r.start_time, str) else ""
            started = bool(st) and st.replace("T", " ") <= now.strftime("%Y-%m-%d %H:%M")
            if old is not None and (old.get("won") is not None or old.get("frozen")):
                continue
            if started and old is None:
                continue          # no pre-jump read of this runner: logging it now would put a post-jump price and Proj in the log
            price = _num(r.fixed_win_price)
            row = dict(race_id=int(r.race_id), venue=r.venue, state=r.state, race=int(r.race), date=date, distance=_num(r.distance), going=r.going,
                       start_time=r.start_time, tab=_num(r.tab_number), barrier=_num(r.barrier), horse=r.horse, jockey=r.jockey, trainer=r.trainer,
                       proj=_num(r.wprp_proj), model=r.wprp_model if isinstance(r.wprp_model, str) else None, proj_made=r.wprp_made if isinstance(r.wprp_made, str) else None,
                       nett=_num(r.wpr_nett), spd=_num(r.spd_fig), fgap=f[0], map_kind=f[1], map_err=f[2], price=price,
                       price_first=(old or {}).get("price_first") if (old or {}).get("price_first") is not None else price,
                       price_time=stamp if price is not None else (old or {}).get("price_time"), logged=stamp)
            if started:
                # the race has started: keep what was read before the jump, do not overwrite with a post-jump price
                if old is not None:
                    row.update(price=old.get("price"), price_time=old.get("price_time"), proj=old.get("proj"), proj_made=old.get("proj_made"), fgap=old.get("fgap"))
                row["frozen"] = True
            merged[key] = row
            n += 1
        for k in list(merged):
            if k not in set(str(int(x)) for x in d.run_id) and not merged[k].get("gone") and merged[k].get("won") is None:
                merged[k] = {**merged[k], "gone": True}
        if merged != have:
            _write(path, merged)
        print(f"{date}: {len(d)} runners in runners.csv, {n} written, {len(merged)} in log")


def labels():
    rn = _runners()
    today = _melb_today().isoformat()
    for path in sorted(DIR.glob("*.json.gz")):
        date = path.name[:10]
        if date >= today:
            continue
        rows = _read(path)
        if not rows or all(r.get("won") is not None or r.get("gone") for r in rows.values()):
            continue
        d = rn[rn.date.astype(str).str[:10] == date].drop_duplicates("run_id").set_index("run_id")
        n = 0
        for k, r in rows.items():
            if r.get("won") is not None or int(k) not in d.index:
                continue
            x = d.loc[int(k)]
            won, pos = _num(x.get("won")), _num(x.get("finish_position"))
            if won is None and pos is None:
                continue
            rows[k] = {**r, "won": won if won is not None else 0.0, "finish": pos, "sp": _num(x.get("starting_price_sp")), "frozen": True}
            n += 1
        if n:
            _write(path, rows)
        print(f"{date}: {n} labels")


def main(argv):
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["snapshot", "labels"])
    ap.add_argument("--from", dest="start")
    ap.add_argument("--days", type=int, default=2)
    a = ap.parse_args(argv)
    if a.cmd == "labels":
        return labels()
    s = dt.date.fromisoformat(a.start) if a.start else _melb_today()
    return snapshot([(s + dt.timedelta(i)).isoformat() for i in range(a.days)])


if __name__ == "__main__":
    main(sys.argv[1:])
