"""Hong Kong results history from HKJC's results pages (28 Oct 2026).

  python hk_results.py --since 2016-09-01 --until 2026-10-27 [--workers 4] [--max-minutes 300]

Walks every date, tries Sha Tin then Happy Valley race 1 (https://racing.hkjc.com/en-us/local/information/localresults, which redirects to the
archive pages for older dates), and for a date with a meeting reads every race. Writes race_results_hk.csv.gz (one row per runner per race):
race_id (92YYYYMMDDRR, below TopRate's 7 trillion ids but clear of them), date, race_no, track, course, distance, going, race_class, race_name,
prize_hkd, horse, hk_code, hk_num (saddle cloth), jockey, trainer, weightCarried (kg), weight_lbs, horse_weight_lbs, barrier, field_size,
positionFinish (blank when the horse did not finish, with `status` holding the code), marginFinish (lengths behind the winner; a winner's own
value is NEGATIVE, the winning margin, as in the Australian files), priceStarting (final win odds), run_pos (the running-position calls),
time_s, winners_time, wpr blank (HKJC publishes no rating; ratings come from the runner pages in data/tr_form).
Resumable: data/hk_results_state.json records every date already checked (a date with no meeting is only recorded once it is 4+ days old).
Nothing reads this file yet."""
import argparse
import concurrent.futures as cf
import datetime as dt
import html
import json
import re
import sys
import time
import urllib.request
from pathlib import Path

import numpy as np
import pandas as pd

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "race_results_hk.csv.gz"
STATE = ROOT / "data" / "hk_results_state.json"
UA = {"User-Agent": "Mozilla/5.0"}
URL = "https://racing.hkjc.com/en-us/local/information/localresults?racedate={d}&Racecourse={c}&RaceNo={n}"
COURSES = {"ST": "Sha Tin", "HV": "Happy Valley"}
FR = {"N": 0.25, "SH": 0.1, "HD": 0.2, "SN": 0.05, "NOSE": 0.05, "NS": 0.05}
GOING = r"(GOOD TO FIRM|GOOD TO YIELDING|YIELDING TO SOFT|WET FAST|WET SLOW|GOOD|FIRM|YIELDING|SOFT|HEAVY|FAST|SLOW)"
LBS_KG = 0.45359237


def get(d, c, n):
    u = URL.format(d=d, c=c, n=n)
    err = None
    for k in range(3):
        try:
            return urllib.request.urlopen(urllib.request.Request(u, headers=UA), timeout=45).read().decode("utf8", "ignore")
        except Exception as e:  # noqa: BLE001
            err = e
            time.sleep(1.5 * (k + 1))
    raise RuntimeError(f"{d} {c} R{n}: {err}")


def lbw(s):
    s = s.strip().upper()
    if s in ("---", "-", "") or s.startswith("DH"):
        return 0.0
    tot = 0.0
    for part in s.replace("-", " ").split():
        if part in FR:
            tot += FR[part]
        elif "/" in part:
            a, b = part.split("/")
            tot += int(a) / int(b)
        else:
            try:
                tot += float(part)
            except ValueError:
                return None
    return tot


def secs(t):
    m = re.match(r"^(\d+):(\d+\.\d+)$", t.strip())
    if m:
        return int(m.group(1)) * 60 + float(m.group(2))
    try:
        return float(t)
    except ValueError:
        return None


def num(x):
    try:
        return float(str(x).replace(",", ""))
    except ValueError:
        return None


def parse(t, n):
    """(runner rows, race header dict) for one results page, or ([], {}) when the date has no such race."""
    t = re.sub(r"<script.*?</script>|<style.*?</style>", "", t, flags=re.S)
    rows = []
    for r in re.findall(r"<tr[^>]*>(.*?)</tr>", t, flags=re.S):
        cells = [re.sub(r"\s+", " ", html.unescape(re.sub(r"<[^>]+>", " ", c))).strip() for c in re.findall(r"<t[dh][^>]*>(.*?)</t[dh]>", r, flags=re.S)]
        if len(cells) >= 12 and cells[1].isdigit() and re.search(r"\([A-Z]\d{3}\)", cells[2]):
            rows.append(cells)
    if not rows:
        return [], {}
    tx = re.sub(r"\s+", " ", html.unescape(re.sub(r"<[^>]+>", " ", t)))
    m = re.search(rf"RACE {n} \(\d+\) (.*?) - (\d{{3,4}})M.*?Going : {GOING} (.*?) Course : (.*?) HK\$ ([\d,]+)", tx)
    head = {}
    if m:
        head = dict(race_class=m.group(1).strip(), distance=int(m.group(2)), going=m.group(3).title(), race_name=m.group(4).strip(),
                    course=m.group(5).strip(), prize_hkd=num(m.group(6)))
    return rows, head


def race_rows(d, c, n, cells, head):
    out = []
    win_time = None
    for x in cells:
        if re.match(r"^1(\s*DH)?$", x[0]):
            win_time = secs(x[10])
            break
    second = next((lbw(x[8]) for x in cells if re.match(r"^2(\s*DH)?$", x[0])), None)
    n_run = len(cells)
    ymd = d.replace("/", "")
    for x in cells:
        pm = re.match(r"^(\d+)(\s*DH)?$", x[0])
        pos = int(pm.group(1)) if pm else None
        mar = lbw(x[8])
        if pos == 1:
            mar = -(second if second is not None else 0.0) if not pm.group(2) else 0.0
        name = re.sub(r"\s*\([A-Z]\d{3}\)\s*$", "", x[2]).strip()
        code = re.search(r"\(([A-Z]\d{3})\)", x[2]).group(1)
        lbs = num(x[5])
        out.append(dict(
            race_id=int(f"92{ymd}{n:02d}"), date=d.replace("/", "-"), race_no=n, track=COURSES[c], course=head.get("course"), distance=head.get("distance"),
            going=head.get("going"), race_class=head.get("race_class"), race_name=head.get("race_name"), prize_hkd=head.get("prize_hkd"),
            horse=name, hk_code=code, hk_num=int(x[1]), jockey=x[3], trainer=x[4],
            weightCarried=round(lbs * LBS_KG, 1) if lbs else None, weight_lbs=lbs, horse_weight_lbs=num(x[6]),
            barrier=int(x[7]) if x[7].isdigit() else None, field_size=n_run, positionFinish=pos, status=None if pm else x[0],
            marginFinish=mar, priceStarting=num(x[11]), run_pos=x[9], time_s=secs(x[10]), winners_time=win_time, wpr=None,
            isBarrierTrial=False, is_jumpout=False))
    return out


def meeting(d):
    """All runner rows of the meeting on date d (yyyy/mm/dd), or [] when there is none."""
    for c in COURSES:
        t = get(d, c, 1)
        cells, head = parse(t, 1)
        if not cells:
            continue
        rows = race_rows(d, c, 1, cells, head)
        for n in range(2, 16):
            cells, head = parse(get(d, c, n), n)
            if not cells:
                break
            rows += race_rows(d, c, n, cells, head)
        return rows
    return []


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--since", default="2016-09-01")
    ap.add_argument("--until", default=(dt.date.today() - dt.timedelta(days=1)).isoformat())
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--max-minutes", type=float, default=0)
    ap.add_argument("--recheck", action="store_true", help="ignore the state file and read every date again")
    a = ap.parse_args()
    state = json.loads(STATE.read_text()) if STATE.exists() and not a.recheck else {}
    d0, d1 = dt.date.fromisoformat(a.since), dt.date.fromisoformat(a.until)
    todo = [(d0 + dt.timedelta(days=i)).strftime("%Y/%m/%d") for i in range((d1 - d0).days + 1)]
    todo = [d for d in todo if d.replace("/", "-") not in state]
    print(f"{len(todo)} dates to check ({a.since} to {a.until})", flush=True)
    t0, new, found = time.time(), [], 0
    stop = False

    def work(d):
        if stop:
            return d, None
        return d, meeting(d)

    done = 0
    with cf.ThreadPoolExecutor(a.workers) as ex:
        futs = [ex.submit(work, d) for d in todo]
        for f in cf.as_completed(futs):
            try:
                d, rows = f.result()
            except Exception as e:  # noqa: BLE001
                print("  error:", e, flush=True)
                continue
            if rows is None:
                continue
            key = d.replace("/", "-")
            old_enough = (dt.date.today() - dt.date.fromisoformat(key)).days >= 4
            if rows:
                new += rows
                found += 1
                state[key] = rows[0]["track"]
            elif old_enough:
                state[key] = None
            done += 1
            if done % 100 == 0:
                print(f"  {done}/{len(todo)} dates, {found} meetings, {len(new)} runners, {time.time() - t0:.0f}s", flush=True)
                STATE.parent.mkdir(exist_ok=True)
                STATE.write_text(json.dumps(state, sort_keys=True))
            if a.max_minutes and time.time() - t0 > a.max_minutes * 60 and not stop:
                stop = True
                print("  time budget reached, stopping after the dates in flight", flush=True)
    STATE.parent.mkdir(exist_ok=True)
    STATE.write_text(json.dumps(state, sort_keys=True))
    if new:
        df = pd.DataFrame(new)
        if OUT.exists():
            df = pd.concat([pd.read_csv(OUT, low_memory=False), df], ignore_index=True)
        df = df.drop_duplicates(["race_id", "hk_num"], keep="last").sort_values(["date", "race_no", "hk_num"])
        df.to_csv(OUT, index=False, compression="gzip")
        print(f"wrote {len(df):,} rows, {df.race_id.nunique():,} races, {df.date.nunique()} meetings, {df.date.min()} to {df.date.max()}")
    else:
        print("nothing new")


if __name__ == "__main__":
    sys.exit(main())
