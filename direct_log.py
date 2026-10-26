"""Complete-field pre-race ATW feature log (26 Oct 2026).

Every declared runner of a race gets one row holding the runner-page history it had BEFORE the race (TopRate's ratings as given, weight adjusted to the
horse's next start, so ATW only) plus the race context. Live fields are complete (a runner page exists for every declared runner), so these rows can
train a field-relative direct finishing-position model that the thin past page store cannot (see CLAUDE.md, direct finishing-position entries).

data/direct_log/<date>.json.gz = {"rows": {run_id: {...}}}. A row is written while its race is still to run and frozen once the race start has passed
or a label is filled. fill_labels() adds finish/won/placed from runners.csv once the race has resulted. Backfilled rows (src='backfill') rebuild the
history from data/tr_form with date < race date, so they hold Final ratings, whereas live rows may hold Preliminary ones: keep src when training.

Usage: python direct_log.py snapshot [--from D --days N]   (default today and the next 2 days, as the runner fetch does)
       python direct_log.py labels                         (fill labels for logged dates up to yesterday)
       python direct_log.py backfill --from D --to D
"""
import argparse
import datetime as dt
import gzip
import json
import sys
from pathlib import Path

import pandas as pd

import runners_io

ROOT = Path(__file__).parent
DIR = ROOT / "data" / "direct_log"
NHIST = 12
RUN_KEYS = ("date", "wpr", "marginFinish", "positionFinish", "starters", "distance", "going", "weightCarried", "class", "barrier", "priceStarting",
            "priceOpening", "jockey", "track", "daysSinceLastRun")


def _hist_index():
    """horse_id -> list of compact runs (rated, non-trial, non-jumpout), oldest first, from data/tr_form."""
    idx = {}
    for f in sorted((ROOT / "data" / "tr_form").glob("*.json.gz")):
        with gzip.open(f, "rt") as fh:
            runs = json.load(fh).get("runs", {})
        for r in runs.values():
            if r.get("isBarrierTrial") or r.get("isJumpout") or r.get("wpr") is None:
                continue
            c = {k: r.get(k) for k in RUN_KEYS}
            c["wpr"] = r["wpr"]
            idx.setdefault(str(r["horse_id"]), {})[r["date"]] = c
    return {h: [v[d] for d in sorted(v)] for h, v in idx.items()}


def _num(x):
    try:
        v = float(x)
        return None if v != v else v
    except (TypeError, ValueError):
        return None


def build_rows(rn, date, hist, src):
    """rn: runners.csv rows of one date (non-scratched). Returns {run_id: row}."""
    out = {}
    for r in rn.itertuples(index=False):
        hid = str(int(r.horse_id)) if _num(r.horse_id) is not None else None
        past = [x for x in hist.get(hid, []) if x["date"] < date][-NHIST:] if hid else []
        out[str(int(r.run_id))] = dict(
            horse_id=hid, race_id=int(r.race_id), venue=r.venue, state=r.state, race=int(r.race), date=date, distance=_num(r.distance),
            going=r.going, race_class=r.race_class, grading=r.track_grading, prize=_num(r.prize_money), start_time=r.start_time,
            tab=_num(r.tab_number), barrier=_num(r.barrier), weight=_num(getattr(r, "weight_carried", None)), jockey=r.jockey, trainer=r.trainer,
            price=_num(r.fixed_win_price), nett=_num(r.wpr_nett), proj=_num(getattr(r, "wprp_proj", None)), hist=past, src=src,
            logged=dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%MZ"))
    return out


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


def _day_rows(runners, date):
    d = runners[(runners.date.astype(str).str[:10] == date) & (runners.scratched.fillna(0) != 1)].copy()
    return d.dropna(subset=["run_id", "race_id", "race"])


def snapshot(dates, src="live", freeze_past=True):
    runners = runners_io.read_runners()
    hist = _hist_index()
    now = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M")
    for date in dates:
        new = build_rows(_day_rows(runners, date), date, hist, src)
        path = DIR / f"{date}.json.gz"
        have = _read(path)
        merged = dict(have)
        n = 0
        for k, v in new.items():
            old = have.get(k)
            if old is not None:
                frozen = old.get("won") is not None or (freeze_past and old.get("start_time") and str(old["start_time"])[:16] <= now)
                if frozen:
                    continue
            merged[k] = v
            n += 1
        # a runner scratched or dropped after logging leaves the row but it is flagged
        for k in list(merged):
            if k not in new and not merged[k].get("gone") and merged[k].get("won") is None:
                merged[k] = {**merged[k], "gone": True}
        if merged != have:
            _write(path, merged)
        print(f"{date}: {len(new)} runners, {n} written")


def fill_labels():
    runners = runners_io.read_runners()
    today = dt.date.today().isoformat()
    for path in sorted(DIR.glob("*.json.gz")):
        date = path.name[:10]
        if date >= today:
            continue
        rows = _read(path)
        if not rows or all(r.get("won") is not None or r.get("gone") for r in rows.values()):
            continue
        d = runners[runners.date.astype(str).str[:10] == date].drop_duplicates("run_id").set_index("run_id")
        n = 0
        for k, r in rows.items():
            if r.get("won") is not None or int(k) not in d.index:
                continue
            x = d.loc[int(k)]
            won, pos = _num(x.get("won")), _num(x.get("finish_position"))
            if won is None and pos is None:
                continue
            rows[k] = {**r, "won": won, "finish": pos, "placed": _num(x.get("placed"))}
            n += 1
        if n:
            _write(path, rows)
        print(f"{date}: {n} labels")


def main(argv):
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["snapshot", "labels", "backfill"])
    ap.add_argument("--from", dest="start")
    ap.add_argument("--to")
    ap.add_argument("--days", type=int, default=3)
    a = ap.parse_args(argv)
    if a.cmd == "labels":
        return fill_labels()
    if a.cmd == "snapshot":
        s = dt.date.fromisoformat(a.start) if a.start else dt.date.today()
        return snapshot([(s + dt.timedelta(i)).isoformat() for i in range(a.days)])
    s, e = dt.date.fromisoformat(a.start), dt.date.fromisoformat(a.to)
    ds = [(s + dt.timedelta(i)).isoformat() for i in range((e - s).days + 1)]
    snapshot(ds, src="backfill", freeze_past=False)
    fill_labels()


if __name__ == "__main__":
    main(sys.argv[1:])
