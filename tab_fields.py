"""
tab_fields.py -- carried weights (and barriers) from TAB race cards, written into toprate_runners.csv.

Why: toprate.au stopped supplying weights (race results files from 12 Sep 2026; the runners file's
weight_carried column and toprate_data.json's wt were never filled), so every model reading a weight gets
nothing. TAB's per-race detail (the same RACE_DETAIL call the poller already makes for prices) carries each
runner's handicap weight for every Australian race.

What: tab_results_poller.run_once() calls maybe_run() every cycle. Twice a day (first cycle after 04:30 and
after 10:30 Melbourne time; a marker file per slot) it fetches the race detail for every AU thoroughbred race
today and tomorrow (04:30) or today (10:30, late rider changes), within an 8-minute budget, then:
  - writes weight_carried in the runners dataframe (TAB wins: it is the only weight source), matched on
    (date, venue, race, tab_number) exactly like apply_prices
  - appends every read to $FIELDS_LOG_DIR/YYYY-MM-DD.csv (default ~/racing-data/tab_fields, outside the
    runner checkout like tab_price_log) for the racing-model archive job
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
        for jurisdiction in poller.AU_STATES:
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
    later read corrects an earlier one); returns (df, n_written)."""
    if "weight_carried" not in runners_df.columns:
        runners_df["weight_carried"] = pd.NA
    venue_u = runners_df["venue"].astype(str).str.upper()
    race = pd.to_numeric(runners_df["race"], errors="coerce")
    tab = pd.to_numeric(runners_df["tab_number"], errors="coerce")
    wc = pd.to_numeric(runners_df["weight_carried"], errors="coerce")
    n = 0
    for f in fields:
        if f.get("weight_carried") is None:
            continue
        pv = poller.VENUE_ALIASES.get(f["venue"].upper(), f["venue"]).upper()
        mask = (runners_df["date"] == f["date"]) & (venue_u == pv) & (race == f["race_no"]) & (tab == f["tab_number"])
        idx = runners_df.index[mask & (wc.isna() | (wc != f["weight_carried"]))]
        if len(idx):
            runners_df.loc[idx, "weight_carried"] = f["weight_carried"]
            n += len(idx)
    return runners_df, n


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
    """The slot marker to run now, or None (each slot runs once per Melbourne day, at or after its time)."""
    now = now or datetime.now(MEL)
    for h, m in reversed(SLOTS):
        if (now.hour, now.minute) >= (h, m):
            marker = LOG_DIR / f".done_{now.date().isoformat()}_{h:02d}{m:02d}"
            return None if marker.exists() else marker
    return None


def maybe_run(poller, runners_loader):
    """Called every poller cycle. Returns (runners_df, n_filled) when it ran and filled something, else None."""
    try:
        marker = due_slot()
        if marker is None:
            return None
        LOG_DIR.mkdir(parents=True, exist_ok=True)
        marker.touch()          # before fetching: a killed run skips this slot instead of retrying every cycle
        today = datetime.now(MEL).date()
        morning = marker.name.endswith(f"{SLOTS[0][0]:02d}{SLOTS[0][1]:02d}")
        dates = [today.isoformat()] + ([(today + timedelta(days=1)).isoformat()] if morning else [])
        # one-off: the first live run (24 Sep 2026) read claimAmount -1 as a 1kg claim; re-read that day
        repair = LOG_DIR / ".repaired_claim_2026-09-24"
        if not repair.exists():
            dates = ["2026-09-24"] + dates
            repair.touch()
        t0 = time.time()
        fields = fetch(poller, dates)
        _log(fields)
        with_w = sum(f.get("weight_carried") is not None for f in fields)
        claims = pd.Series([f.get("claim") for f in fields]).value_counts().head(8).to_dict()
        print(f"  tab_fields: {len(fields)} runners read ({with_w} with a weight) in {time.time() - t0:.0f}s; "
              f"claims (kg: runners) {claims}")
        if not with_w:
            return None
        df, n = apply(poller, runners_loader(), fields)
        print(f"  tab_fields: wrote weight_carried for {n} runners")
        return (df, n) if n else None
    except Exception as e:
        print(f"  tab_fields failed (non-fatal): {type(e).__name__}: {str(e)[:120]}")
        return None
