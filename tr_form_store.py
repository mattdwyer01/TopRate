"""Permanent store of every past run TopRate's runner pages list (14 Oct 2026).

toprate_runner_fetch.py keeps each day's runner pages for only 7 days, but a page carries the horse's whole run list (about 19 runs, up to 100+):
TopRate's own `wpr` for the run, finish, margin, settled position, 200m to 800m positions and margins, sectionals, race shape, opening/starting/top
price, weight carried, going, class, jockey, trainer, gear changes, days since last run, steward and video comments. This module upserts those runs
into data/tr_form/<YYYY-MM>.json.gz (month of the RUN date), one record per (horse, date, run), so the history accumulates instead of rolling off.

A run is final once run, so a stored record is replaced by a later copy (TopRate can revise a rating); a shard is rewritten only when its content changed.
Records are TopRate's numbers as given: they are history, safe to join to any later race by (horse_id, date), never to the race the run belongs to
before it ran.

Usage: python tr_form_store.py [data/tr_runners/<date>.json.gz ...]   (no arguments: ingest every file in data/tr_runners)
       python tr_form_store.py --merge SRC_DIR   (merge every shard of another store directory into data/tr_form, run on the newest tip)

frame(horses) turns the store into the run table the dashboard's Recent runs / form history is built from (TopRate's numbers only).
"""
import gzip
import json
import sys
from pathlib import Path

DIR = Path(__file__).parent / "data" / "tr_form"
RUNNERS = Path(__file__).parent / "data" / "tr_runners"


def _read(path):
    try:
        with gzip.open(path, "rt") as fh:
            return json.load(fh).get("runs", {})
    except Exception:
        return {}


def _write(path, runs):
    path.parent.mkdir(parents=True, exist_ok=True)
    with gzip.GzipFile(path, "wb", mtime=0) as gz:
        gz.write(json.dumps({"runs": runs}, separators=(",", ":"), sort_keys=True, default=str).encode())


def upsert(records, store_dir=DIR):
    """records: runner-page records ({horse_id, horse, form: [...]}). Returns (runs seen, runs added or changed, shards written)."""
    by_shard = {}
    seen = 0
    for rec in records:
        hid = rec.get("horse_id")
        if hid is None:
            continue
        for run in rec.get("form") or []:
            if not isinstance(run, dict) or not run.get("date"):
                continue
            seen += 1
            key = f"{hid}|{run['date']}|{run.get('runId') or run.get('raceId') or run.get('raceNumber')}"
            by_shard.setdefault(str(run["date"])[:7], {})[key] = {"horse_id": hid, "horse": rec.get("horse"), **run}
    changed = written = 0
    for month, new in by_shard.items():
        path = store_dir / f"{month}.json.gz"
        have = _read(path)
        merged = dict(have)
        n = 0
        for k, v in new.items():
            if merged.get(k) != v:
                merged[k] = v
                n += 1
        if n:
            _write(path, merged)
            changed += n
            written += 1
    return seen, changed, written


def main(argv):
    if argv[:1] == ["--merge"]:
        c, w = merge_dir(argv[1])
        print(f"merged {argv[1]}: {c} runs added or changed, {w} shards written")
        return [0, c, w]
    files = [Path(a) for a in argv] or sorted(RUNNERS.glob("*.json.gz"))
    total = [0, 0, 0]
    for f in files:
        try:
            with gzip.open(f, "rt") as fh:
                rows = json.load(fh).get("rows", {})
        except Exception as e:
            print(f"{f}: unreadable ({type(e).__name__})")
            continue
        s, c, w = upsert(rows.values())
        print(f"{f.name}: {s} runs seen, {c} added or changed, {w} shards written")
        total = [total[0] + s, total[1] + c, total[2] + w]
    return total


def merge_dir(src_dir, store_dir=DIR):
    """Merge every shard in src_dir into the store (a run in both: src wins). Used by the backfill workflow on the newest tip so concurrent writers are kept."""
    changed = written = 0
    for src in sorted(Path(src_dir).glob("*.json.gz")):
        new = _read(src)
        path = store_dir / src.name
        merged = _read(path)
        n = 0
        for k, v in new.items():
            if merged.get(k) != v:
                merged[k] = v
                n += 1
        if n or not path.exists():
            _write(path, merged)
            written += 1
        changed += n
    return changed, written


def frame(horses=None, store_dir=DIR):
    """All stored runs as a DataFrame in the column names toprate_daily's form-history code reads (horse, date, wpr, track, distance, going, positionFinish,
    barrier, marginFinish, positionSettled, position800m, position400m, race_class, jockey, field_size, weightCarried, priceStarting, raceNumber, raceShape*,
    comments_video/steward). `horses`: optional set of lowercased horse names to keep. wpr is TopRate's rating at the weight of the horse's upcoming race."""
    import pandas as pd
    rows = []
    for f in sorted(store_dir.glob("*.json.gz")):
        for r in _read(f).values():
            h = str(r.get("horse") or "").strip().lower()
            if horses is not None and h not in horses:
                continue
            sr = r.get("sectionalRating") or {}
            rows.append({
                "sect_early": sr.get("individualEarlySpeed"), "sect_mid": sr.get("individual800mTo400mSpeed"),
                "sect_l600": sr.get("individualLast600mSpeed"), "sect_l200": sr.get("individualLast200mSpeed"),
                # names the settling and race-speed models were trained on (TopRate's own columns)
                "sect_i_early": sr.get("individualEarlySpeed"), "sect_ld_early": sr.get("leaderEarlySpeed"),
                "sect_i_to800": sr.get("individualTo800mSpeed"), "sect_i_to600": sr.get("individualTo600mSpeed"),
                "margin800m": r.get("margin800m"), "margin600m": r.get("margin600m"), "position600m": r.get("position600m"),
                "horse": r.get("horse"), "horse_lc": h, "horse_id": r.get("horse_id"), "date": r.get("date"), "wpr": r.get("wpr"),
                "track": r.get("track") or r.get("venue"), "distance": r.get("distance"), "going": r.get("going"),
                "positionFinish": r.get("positionFinish"), "barrier": r.get("barrier"), "marginFinish": r.get("marginFinish"),
                "positionSettled": r.get("positionSettled"), "position800m": r.get("position800m"), "position400m": r.get("position400m"),
                "race_class": r.get("class"), "jockey": r.get("jockey"), "field_size": r.get("starters"), "weightCarried": r.get("weightCarried"),
                "priceStarting": r.get("priceStarting"), "raceNumber": r.get("raceNumber"),
                "raceShapeEarly": r.get("raceShapeEarly"), "raceShapeMid": r.get("raceShapeMid"), "raceShapeLate": r.get("raceShapeLate"),
                "comments_video": r.get("commentsVideo"), "comments_steward": r.get("commentsSteward"),
                "isBarrierTrial": 1 if (r.get("isBarrierTrial") or r.get("isJumpout")) else 0,
            })
    return pd.DataFrame(rows)


if __name__ == "__main__":
    main(sys.argv[1:])
