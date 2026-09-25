"""
tab_fields.py -- carried weights (and barriers) from TAB race cards, written into toprate_runners.csv.

Why: toprate.au stopped supplying weights (race results files from 12 Sep 2026; the runners file's
weight_carried column and toprate_data.json's wt were never filled), so every model reading a weight gets
nothing. TAB's per-race detail (the same RACE_DETAIL call the poller already makes for prices) carries each
runner's handicap weight for every Australian race.

What: tab_results_poller.run_once() calls maybe_fetch() and apply_logged() every cycle.
  - maybe_fetch: twice a day (a marker file per slot: 04:30 and 10:30 Melbourne time, or the first cycle after,
    earliest pending slot first) it fetches the race detail for every AU thoroughbred race today and tomorrow
    (04:30) or today (10:30, late rider changes), within an 8-minute budget, and appends every read to
    $FIELDS_LOG_DIR/YYYY-MM-DD.csv (default ~/racing-data/tab_fields, outside the runner checkout like
    tab_price_log; also shipped to the racing-model archive)
  - apply_logged: writes the latest logged weight_carried into the runners dataframe (TAB wins: it is the only
    weight source), matched on (date, venue, race, tab_number) like apply_prices. It runs every cycle and only
    counts changed rows, so a read whose commit failed to push is written again by the next cycle
Carried weight = TAB handicapWeight minus claimAmount when positive (TAB sends -1 for no claim). The first runner's raw
keys are printed once per slot so the field names can be checked in the workflow log.

Best-effort throughout: any error is printed and swallowed, the price / results poll is never affected.
"""
import csv
import json
import os
import re
import time
from datetime import date, datetime, timedelta
from pathlib import Path
from zoneinfo import ZoneInfo

import pandas as pd

LOG_DIR = Path(os.environ.get("FIELDS_LOG_DIR", Path.home() / "racing-data" / "tab_fields"))
SLOTS = ((4, 30), (10, 30))           # Melbourne local time; each runs once per day
FIELDS = ["captured_utc", "date", "venue", "race_no", "tab_number", "runner_name", "barrier",
          "handicap_weight", "claim", "weight_carried", "rider", "scratched"]
MEL = ZoneInfo("Australia/Melbourne")


def _num(v):
    try:
        f = float(v)
        return f if f == f else None
    except (TypeError, ValueError):
        return None


def _claim(run):
    """Apprentice claim in kg. TAB's claimAmount is -1 when there is no claim (seen in the first live run,
    24 Sep 2026), so only a positive value counts; else '(a3)' style text in the rider name; else 0."""
    f = _num(run.get("claimAmount"))
    if f is not None and f > 0:
        return f
    m = re.search(r"\(a(\d+(?:\.\d+)?)\)", str(run.get("riderDriverName") or ""))
    return float(m.group(1)) if m else 0.0


def runner_fields(run):
    weight = _num(run.get("handicapWeight"))
    if weight is None:
        weight = _num(run.get("weight"))
    claim = _claim(run)
    fo = run.get("fixedOdds") or {}
    return dict(
        runner_name=run.get("runnerName"), barrier=run.get("barrierNumber"), handicap_weight=weight,
        claim=claim, weight_carried=(weight - claim) if weight else None,
        rider=run.get("riderDriverName"),
        scratched=fo.get("bettingStatus") in ("LateScratched", "Scratched") or bool(run.get("scratched")),
    )


BUDGET_S = 480                        # stop fetching after 8 minutes (the poller job's timeout is 15)


def fetch(poller, dates):
    """Race detail for every AU thoroughbred race on `dates` -> list of dicts (FIELDS without captured_utc)."""
    out = []
    shown = False
    t0 = time.time()
    for d in dates:
        for jurisdiction in getattr(poller, "TAB_JURISDICTIONS", poller.AU_STATES):
            try:
                payload = poller.get(poller.MEETINGS.format(date=d), {"jurisdiction": jurisdiction}, timeout=20)
            except Exception as e:
                print(f"  tab_fields: {d} {jurisdiction} meetings failed: {type(e).__name__}")
                continue
            for m in payload.get("meetings", []):
                if m.get("raceType") != poller.RACE_TYPE or m.get("location") not in poller.AU_STATES:
                    continue
                venue = str(m.get("meetingName", "")).strip()
                mnem = m.get("venueMnemonic")
                for rc in m.get("races", []):
                    race_no = rc.get("raceNumber")
                    if not mnem or race_no is None:
                        continue
                    if time.time() - t0 > BUDGET_S:
                        print(f"  tab_fields: time budget reached, stopping at {venue} R{race_no}")
                        return out
                    try:
                        det = poller.get(poller.RACE_DETAIL.format(date=d, venue_mnemonic=mnem, race_no=race_no),
                                         {"jurisdiction": jurisdiction}, timeout=20)
                    except Exception as e:
                        print(f"  tab_fields: {venue} R{race_no} failed: {type(e).__name__}")
                        continue
                    for run in det.get("runners", []):
                        if not shown:
                            print("  tab_fields: TAB runner keys: " + json.dumps(
                                {k: v for k, v in run.items() if not isinstance(v, (dict, list))}, default=str)[:1500])
                            shown = True
                        if run.get("runnerNumber") is None:
                            continue
                        out.append(dict(date=d, venue=venue, race_no=race_no, tab_number=run.get("runnerNumber"),
                                        **runner_fields(run)))
                    time.sleep(0.15)
    return out


def apply(poller, runners_df, fields):
    """Write weight_carried for every matched runner (TAB is the only weight source now, so it wins and a
    later read corrects an earlier one); returns (df, n_written). Only rows whose value changes count."""
    if "weight_carried" not in runners_df.columns:
        runners_df["weight_carried"] = pd.NA
    f = pd.DataFrame(fields)
    if f.empty:
        return runners_df, 0
    f = f[f["weight_carried"].notna()].copy()
    f["venue_u"] = f["venue"].astype(str).map(lambda v: poller.VENUE_ALIASES.get(v.upper(), v).upper())
    f["race"] = pd.to_numeric(f["race_no"], errors="coerce")
    f["tab"] = pd.to_numeric(f["tab_number"], errors="coerce")
    f["wc_new"] = pd.to_numeric(f["weight_carried"], errors="coerce")
    f = f.drop_duplicates(["date", "venue_u", "race", "tab"], keep="last")
    key = pd.DataFrame({"date": runners_df["date"].astype(str),
                        "venue_u": runners_df["venue"].astype(str).str.upper(),
                        "race": pd.to_numeric(runners_df["race"], errors="coerce"),
                        "tab": pd.to_numeric(runners_df["tab_number"], errors="coerce")}, index=runners_df.index)
    m = key.reset_index().merge(f[["date", "venue_u", "race", "tab", "wc_new"]], on=["date", "venue_u", "race", "tab"],
                                how="inner").set_index("index")
    wc = pd.to_numeric(runners_df.loc[m.index, "weight_carried"], errors="coerce")
    m = m[wc.isna() | (wc != m["wc_new"])]
    if len(m):
        runners_df.loc[m.index, "weight_carried"] = m["wc_new"].to_numpy()
    return runners_df, len(m)


def read_log(days=2):
    """Every read logged today and on the previous `days` - 1 days (the morning pass reads tomorrow too), in
    capture order, for race dates from yesterday on."""
    today = datetime.now(MEL).date()
    parts = []
    for k in range(days - 1, -1, -1):
        p = LOG_DIR / f"{(today - timedelta(days=k)).isoformat()}.csv"
        if p.exists():
            try:
                parts.append(pd.read_csv(p, dtype={"date": str, "venue": str}))
            except Exception as e:
                print(f"  tab_fields: could not read {p.name}: {type(e).__name__}")
    if not parts:
        return []
    d = pd.concat(parts, ignore_index=True).sort_values("captured_utc", kind="mergesort")
    d = d[d["date"] >= (today - timedelta(days=1)).isoformat()]
    return d.to_dict("records")


def apply_logged(poller, runners_df):
    """Every cycle: re-apply the logged weights (a no-op once they are in). A fetch whose commit was lost (push
    failed after the slot was marked done, 25 Sep 2026) is repaired by the next cycle."""
    try:
        df, n = apply(poller, runners_df, read_log())
        if n:
            print(f"  tab_fields: wrote weight_carried for {n} runners")
        return df, n
    except Exception as e:
        print(f"  tab_fields apply failed (non-fatal): {type(e).__name__}: {str(e)[:120]}")
        return runners_df, 0


def _log(fields):
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    now = datetime.utcnow().isoformat(timespec="seconds")
    path = LOG_DIR / f"{date.today().isoformat()}.csv"
    new = not path.exists()
    with path.open("a", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=FIELDS, extrasaction="ignore")
        if new:
            w.writeheader()
        for f in fields:
            w.writerow({**f, "captured_utc": now})


def due_slot(now=None):
    """The marker of the earliest slot due and not yet run today, or None. Earliest first, so when the poller
    first wakes after 10:30 the morning pass (today and tomorrow) still runs, then 10:30 on the next cycle."""
    now = now or datetime.now(MEL)
    for h, m in SLOTS:
        if (now.hour, now.minute) >= (h, m):
            marker = LOG_DIR / f".done_{now.date().isoformat()}_{h:02d}{m:02d}"
            if not marker.exists():
                return marker
    return None


def maybe_fetch(poller):
    """Called every poller cycle. When a slot is due, reads TAB race cards and appends them to the log (the
    weights reach toprate_runners.csv through apply_logged). Returns the number of runners read."""
    try:
        marker = due_slot()
        if marker is None:
            return 0
        LOG_DIR.mkdir(parents=True, exist_ok=True)
        marker.touch()          # before fetching: a killed run skips this slot instead of retrying every cycle
        today = datetime.now(MEL).date()
        morning = marker.name.endswith(f"{SLOTS[0][0]:02d}{SLOTS[0][1]:02d}")
        dates = [today.isoformat()] + ([(today + timedelta(days=1)).isoformat()] if morning else [])
        t0 = time.time()
        fields = fetch(poller, dates)
        _log(fields)
        with_w = sum(f.get("weight_carried") is not None for f in fields)
        claims = pd.Series([f.get("claim") for f in fields]).value_counts().head(8).to_dict()
        print(f"  tab_fields: {', '.join(dates)}: {len(fields)} runners read ({with_w} with a weight) in "
              f"{time.time() - t0:.0f}s; claims (kg: runners) {claims}")
        return len(fields)
    except Exception as e:
        print(f"  tab_fields failed (non-fatal): {type(e).__name__}: {str(e)[:120]}")
        return 0
