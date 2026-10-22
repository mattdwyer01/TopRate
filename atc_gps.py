"""Australian Turf Club (NSW metro) Swiss Timing sectional PDFs, processed by Triple S Data.

One PDF = one meeting (`{DDMM}{TRACK}.pdf`) or one race (`{DDMM}{TRACK}-{race}.pdf`); same template. No rail distance,
but per horse: barrier, distance travelled vs the winner (DT-W, m), first 400m, last 600m, top speed, and per 200m
section the time remaining to the finish, the section split and the position at the start of the section.

    python atc_gps.py download --since 2022-01-01 [--until 2022-12-31] [--tracks RAND RHIL CANT WARW]
    python atc_gps.py parse [--out work/atc_new]    # every saved PDF -> atc_gps_{runs,sections}.parquet
    python atc_gps.py merge [--new work/atc_new]    # merge into data/gps/atc_gps_{runs,sections}_{year}.parquet

Column Lxxx = xxx metres to run. Its value is the time from that post to the finish ("remaining"), its bracket the
position at that post, its split the time of the section from that post to the next one. The first column is the start
(remaining = race time, no position). Elapsed time at a post = race time - remaining.
"""
from __future__ import annotations

import argparse
import datetime as dt
import logging
import re
import sys
import time
from pathlib import Path

import pandas as pd
import pdfplumber

logging.getLogger("pdfminer").setLevel(logging.ERROR)

ROOT = Path(__file__).resolve().parent
PDF_DIR = ROOT / "work/atc_pdf"
OUT_DIR = ROOT / "work/atc_new"
GPS_DIR = ROOT / "data/gps"
KEYS = {"atc_gps_runs": ["meet_code", "race_no", "tab_no"], "atc_gps_sections": ["meet_code", "race_no", "tab_no", "from_m"]}
BASE = "https://feed.australianturfclub.com.au/sectionals/swiss-timing/{y}/{dm}{t}{sfx}.pdf"
TRACKS = ["RAND", "RHIL", "CANT", "WARW"]   # Sydney metro: Randwick, Rosehill (RHIL, found by probing), Canterbury, Warwick Farm (WARW, no meeting found yet: code unverified)
UA = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/140.0 Safari/537.36"}

T = r"\d+:\d{2}\.\d{2}"
NA = r"(?:-:--\.--|NA)"
ROW1 = re.compile(rf"^(\d+=?|DNF|DNT) (\d+) (.+?) ({T}|{NA}|DNF) ({T}|{NA}) ([\d.]+|NA) \((\d+\s*-\s*\d+)\) (.*)$")
ROW2 = re.compile(rf"^\((\d+)\)\s?(.+?)(?: (\S+) \(([+-]?\d+)\))? ({T}|{NA}) (\d+\s*-\s*\d+|NA) \(({T}|{NA})\) (.*)$")
REM = re.compile(rf"({T}|{NA})(?: \[(\d+)\])?")
SPLIT = re.compile(rf"\(({T}|{NA}|\d+:\d{{2}}\.\d{{2}})\)")


def _t(s: str | None) -> float | None:
    """'1:21.29' / '0:34.57' -> seconds; None for NA."""
    if not s or not re.fullmatch(T, s):
        return None
    m, x = s.split(":")
    return int(m) * 60 + float(x)


def _margin(s: str | None) -> float | None:
    if not s:
        return None
    m = re.fullmatch(r"([\d.]+)L", s)
    return float(m.group(1)) if m else None   # SHD / HD / NK etc. stay in margin_txt


def _header(text: str) -> dict:
    L = [l.strip() for l in text.splitlines() if l.strip()]
    venue = re.sub(r"\s*-\s*$", "", L[0])
    m = re.match(r"Race (\d+): (.*) - (\d+)m$", L[1])
    race_no, name, dist = int(m.group(1)), m.group(2).strip(), int(m.group(3))
    md = re.match(r"(\d{1,2} \w+ \d{4}) - (\d{1,2}:\d{2}[AP]M)", L[2])
    date = dt.datetime.strptime(md.group(1), "%d %B %Y").date()
    m = re.search(r"Track Rating: (.*?), Weather: (.*?), Rail Position: (.*)$", L[3])
    going, weather, rail = (x.strip() for x in m.groups()) if m else (None, None, None)
    scr = re.search(r"^Scratched: (.*)$", text, re.M)
    cols = [int(x) for x in re.findall(r"\bL(\d+)\b", next(l for l in L if l.startswith("Rank TAB#")))]
    ft = next(l for l in L if l.startswith("Field Times"))
    field_t = [_t(x) for x in re.findall(T, ft)]
    return dict(venue=venue, race_no=race_no, race_name=name, distance=dist, race_date=date, start_time=md.group(2),
                going=going, weather=weather, rail=rail, scratched=scr.group(1).strip() if scr else "",
                cols=cols, field_remaining_s=field_t)


def _parse_page(text: str, h: dict) -> list[dict]:
    lines = text.splitlines()
    out = []
    for i, l in enumerate(lines):
        m1 = ROW1.match(l.strip())
        if not m1 or i + 1 >= len(lines):
            continue
        m2 = ROW2.match(lines[i + 1].strip())
        if not m2:
            raise ValueError(f"race {h['race_no']}: unparsed second row after {l!r}: {lines[i + 1]!r}")
        rank, tab, horse, time_s, first400, top, topsec, rest = m1.groups()
        bar, jockey, margin, dtw, last600, fastest, fastest_t, splits_txt = m2.groups()
        rem = REM.findall(rest)
        splits = SPLIT.findall(splits_txt)
        n = len(h["cols"])
        if len(rem) != n or len(splits) != n:
            raise ValueError(f"race {h['race_no']} tab {tab}: {len(rem)} remaining / {len(splits)} splits for {n} columns")
        out.append(dict(
            race_no=h["race_no"], finish=int(rank.rstrip("=")) if rank.rstrip("=").isdigit() else None, finish_txt=rank, tab_no=int(tab),
            horse=horse.strip(), barrier=int(bar), jockey=jockey.strip(), time_s=_t(time_s),
            margin_l=0.0 if rank == "1" else _margin(margin), margin_txt=margin, dist_vs_winner_m=int(dtw) if dtw else 0,
            first400_s=_t(first400), last600_s=_t(last600), top_speed_kmh=float(top) if top != "NA" else None,
            top_speed_section=topsec, fastest_section=fastest if fastest != "NA" else None, fastest_section_s=_t(fastest_t),
            _sections=[dict(to_go_m=k, remaining_s=_t(r), pos=int(p) if p else None, split_s=_t(s))
                       for k, (r, p), s in zip(h["cols"], rem, splits)],
        ))
    return out


def parse_pdf(src: str | Path | bytes, track: str | None = None) -> tuple[pd.DataFrame, pd.DataFrame]:
    """-> (runs, sections). Long fields continue on a second page: rows are merged by (race, tab)."""
    import io
    f = io.BytesIO(src) if isinstance(src, (bytes, bytearray)) else src
    races: dict[int, dict] = {}
    with pdfplumber.open(f) as pdf:
        for page in pdf.pages:
            text = page.extract_text() or ""
            if "TAB#" not in text or not re.search(r"^Race \d+:", text, re.M):
                continue
            h = _header(text)
            r = races.setdefault(h["race_no"], dict(h=h, rows={}))
            for row in _parse_page(text, h):
                if row["tab_no"] in r["rows"]:
                    r["rows"][row["tab_no"]]["_sections"] += row["_sections"]
                else:
                    r["rows"][row["tab_no"]] = row
    runs, secs = [], []
    for no in sorted(races):
        h, rows = races[no]["h"], races[no]["rows"]
        code = track or re.sub(r"\W", "", h["venue"])[:4].upper()
        meet = f"{h['race_date']:%Y%m%d}_{code}"
        win = next((r for r in rows.values() if r["finish"] == 1), None)
        for r in rows.values():
            sec = r.pop("_sections")
            r.update(meet_code=meet, track=code, venue=h["venue"], race_date=h["race_date"], race_name=h["race_name"],
                     distance=h["distance"], going=h["going"], weather=h["weather"], rail=h["rail"], start_time=h["start_time"],
                     source="atc_swiss_timing")
            runs.append(r)
            for s in sorted(sec, key=lambda s: -s["to_go_m"]):
                secs.append(dict(meet_code=meet, race_date=h["race_date"], race_no=no, tab_no=r["tab_no"], horse=r["horse"], **s))
    runs, secs = pd.DataFrame(runs), pd.DataFrame(secs)
    if runs.empty:
        return runs, secs
    secs["from_m"] = (secs["race_no"].map({n: races[n]["h"]["distance"] for n in races}) - secs["to_go_m"]).clip(lower=0)
    secs["to_m"] = secs.groupby(["race_no", "tab_no"])["from_m"].shift(-1)
    secs["to_m"] = secs["to_m"].fillna(secs["race_no"].map({n: races[n]["h"]["distance"] for n in races}))
    secs = secs.merge(runs[["race_no", "tab_no", "time_s"]], on=["race_no", "tab_no"], how="left")
    secs["elapsed_s"] = secs["time_s"] - secs["remaining_s"]   # time from the start to this post
    secs["speed_kmh"] = (secs["to_m"] - secs["from_m"]) / secs["split_s"] * 3.6
    secs = secs.drop(columns="time_s")
    return runs, secs


def check(runs: pd.DataFrame, secs: pd.DataFrame) -> list[str]:
    """Internal consistency: remaining_k - split_k = remaining_(k+1); first remaining = race time; one winner per race."""
    bad = []
    for (race, tab), g in secs.sort_values("to_go_m", ascending=False).groupby(["race_no", "tab_no"]):
        rem, sp = g["remaining_s"].to_numpy(), g["split_s"].to_numpy()
        for j in range(len(g) - 1):
            if pd.notna(rem[j]) and pd.notna(sp[j]) and pd.notna(rem[j + 1]) and abs(rem[j] - sp[j] - rem[j + 1]) > 0.025:
                bad.append(f"race {race} tab {tab}: remaining/split mismatch at {g['to_go_m'].iloc[j]}")
        if pd.notna(rem[-1]) and pd.notna(sp[-1]) and abs(rem[-1] - sp[-1]) > 0.025:
            bad.append(f"race {race} tab {tab}: last remaining != last split")
        t = runs.loc[(runs.race_no == race) & (runs.tab_no == tab), "time_s"].iloc[0]
        if pd.notna(t) and pd.notna(rem[0]) and abs(t - rem[0]) > 0.011:
            bad.append(f"race {race} tab {tab}: first remaining {rem[0]} != race time {t}")
    for race, g in runs.groupby("race_no"):
        if (g["finish"] == 1).sum() != 1:
            bad.append(f"race {race}: {(g['finish'] == 1).sum()} winners (ranks seen: {' '.join(g['finish_txt'].astype(str))})")
    return bad


# ---------------------------------------------------------------- download

def _candidates(since: dt.date, until: dt.date, tracks: list[str]):
    d = until
    while d >= since:
        for t in tracks:
            yield d, t
        d -= dt.timedelta(days=1)


def download(since: str, until: str | None = None, tracks: list[str] | None = None, delay: float = 0.5) -> None:
    """Try every date x track: meeting PDF first, then per-race PDFs (race 1, 2, ... until a miss). Skips what is saved."""
    import requests
    s = requests.Session()
    s.headers.update(UA)
    PDF_DIR.mkdir(parents=True, exist_ok=True)
    d0, d1 = dt.date.fromisoformat(since), dt.date.fromisoformat(until) if until else dt.date.today()
    miss_log = PDF_DIR / "_no_meeting.txt"
    known_miss = set(miss_log.read_text().split()) if miss_log.exists() else set()
    got = errors = 0
    for d, t in _candidates(d0, d1, tracks or TRACKS):
        stem = f"{d:%Y%m%d}_{t}"
        if stem in known_miss or any(PDF_DIR.glob(f"{stem}*.pdf")):
            continue
        base = dict(y=d.year, dm=f"{d:%d%m}", t=t)
        try:
            r = s.get(BASE.format(**base, sfx=""), timeout=30)
            time.sleep(delay)
            if r.status_code == 200 and r.content[:4] == b"%PDF":
                (PDF_DIR / f"{stem}.pdf").write_bytes(r.content)
                got += 1
                print("saved", stem)
                continue
            if r.status_code not in (403, 404):
                print(f"{stem}: HTTP {r.status_code}")
                errors += 1
                continue
            r = s.get(BASE.format(**base, sfx="-1"), timeout=30)   # fall back to per-race files
            time.sleep(delay)
            if r.status_code != 200 or r.content[:4] != b"%PDF":
                if d < dt.date.today() - dt.timedelta(days=3):   # old dates with nothing are final; recent ones may not be up yet
                    known_miss.add(stem)
                continue
            (PDF_DIR / f"{stem}-1.pdf").write_bytes(r.content)
            n = 2
            while True:
                rr = s.get(BASE.format(**base, sfx=f"-{n}"), timeout=30)
                time.sleep(delay)
                if rr.status_code != 200 or rr.content[:4] != b"%PDF":
                    break
                (PDF_DIR / f"{stem}-{n}.pdf").write_bytes(rr.content)
                n += 1
            got += 1
            print(f"saved {stem}: {n - 1} races")
        except requests.RequestException as e:
            errors += 1
            print(f"{stem}: {type(e).__name__}")
            if errors >= 10 and not got:
                sys.exit("feed unreachable (10 errors, nothing saved): check network access / run from the Vultr AU runner")
    miss_log.write_text("\n".join(sorted(known_miss)) + "\n")
    print(f"{got} meetings saved, {errors} errors")


# ---------------------------------------------------------------- parse

def _peek(f: Path, n: int = 8) -> str:
    """First lines of the first page, to see what a PDF the parser could not read looks like."""
    try:
        with pdfplumber.open(f) as pdf:
            return " | ".join(((pdf.pages[0].extract_text() or "").splitlines()[:n])) or f"(no text, {len(pdf.pages)} pages)"
    except Exception as e:
        return f"({type(e).__name__}: {e})"


def parse_all(out: Path = OUT_DIR) -> None:
    files = sorted(PDF_DIR.glob("*.pdf"))
    runs, secs, problems = [], [], []
    by_meet: dict[str, list[Path]] = {}
    for f in files:
        by_meet.setdefault(f.stem.split("-")[0], []).append(f)
    for stem, fs in by_meet.items():
        track = stem.split("_")[1]
        for f in fs:
            try:
                r, s = parse_pdf(f, track)
            except Exception as e:   # one bad PDF must not stop the batch
                problems.append(f"{f.name}: {type(e).__name__}: {e}")
                continue
            if r.empty:
                problems.append(f"{f.name}: no runs, first lines: {_peek(f)}")
                continue
            bad = check(r, s)
            problems += [f"{f.name}: {b}" for b in bad]
            runs.append(r)
            secs.append(s)
    out.mkdir(parents=True, exist_ok=True)
    if runs:
        pd.concat(runs, ignore_index=True).to_parquet(out / "atc_gps_runs.parquet", index=False)
        pd.concat(secs, ignore_index=True).to_parquet(out / "atc_gps_sections.parquet", index=False)
    print(f"{len(files)} PDFs, {sum(len(r) for r in runs):,} runs, {sum(len(s) for s in secs):,} sections, {len(problems)} problems")
    for p in problems[:50]:
        print(" ", p)
    if problems:
        (out / "atc_parse_problems.txt").write_text("\n".join(problems) + "\n")


# ---------------------------------------------------------------- merge into data/gps

def _merge_one(name: str, new: pd.DataFrame) -> list[str]:
    """Merge new rows into data/gps/{name}_{year}.parquet (year of race_date). Only years whose rows change are rewritten."""
    keys = KEYS[name]
    GPS_DIR.mkdir(parents=True, exist_ok=True)
    year = pd.to_datetime(new["race_date"]).dt.year
    wrote = []
    for yr, part in new.groupby(year):
        f = GPS_DIR / f"{name}_{int(yr)}.parquet"
        old = pd.read_parquet(f) if f.exists() else pd.DataFrame()
        df = pd.concat([x for x in (old, part) if len(x)], ignore_index=True)
        k = df[keys].astype("string")   # keys as strings: dtypes differ between files
        df = df[~k.duplicated(keep="last")].sort_values(["race_date", *keys], kind="stable").reset_index(drop=True)
        if len(old) == len(df) and old.astype(str).equals(df.astype(str)):
            continue
        df.to_parquet(f, index=False)
        wrote.append(f"{f.name} ({len(df):,} rows, {len(df) - len(old):+,})")
    return wrote


def merge(new_dir: Path = OUT_DIR) -> None:
    for name in KEYS:
        f = new_dir / f"{name}.parquet"
        if not f.exists():
            print(f"{name}: nothing to merge")
            continue
        new = pd.read_parquet(f)
        print(f"{name}: {len(new):,} parsed rows; wrote {', '.join(_merge_one(name, new)) or 'nothing'}")


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    d = sub.add_parser("download")
    d.add_argument("--since", required=True)
    d.add_argument("--until")
    d.add_argument("--tracks", nargs="+")
    d.add_argument("--delay", type=float, default=0.5)
    p = sub.add_parser("parse")
    p.add_argument("--out", default=str(OUT_DIR))
    p.add_argument("--file")
    m = sub.add_parser("merge")
    m.add_argument("--new", default=str(OUT_DIR))
    a = ap.parse_args()
    if a.cmd == "download":
        download(a.since, a.until, a.tracks, a.delay)
    elif a.cmd == "merge":
        merge(Path(a.new))
    elif a.file:
        r, s = parse_pdf(a.file)
        print(r.shape, s.shape, check(r, s))
    else:
        parse_all(Path(a.out))
