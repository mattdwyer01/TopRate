"""Racing Victoria / Triple S GPS sectional PDFs (VIC and SA): distance from the rail by section, per runner.

racing.com's GPS feed (what gps_daily.yml reads into data/gps/rc_gps_*.parquet) keeps ONE average distance from the rail per runner. The
PDF report published for each race carries it per section (about every 200m), plus speed, stride length and stride rate:

    https://d3qmfyv6ad9vwv.cloudfront.net/{meet_code}_{race_no:02d}.pdf        (meet_code = racing.com meeting id = rc_gps_runs.meet_code)

No login. Pages 1 to 4 are the race summary, then one page per runner with four charts. The charts print a value only at some points
(Distance from Rail always at the start, 1600, 1200, 800, 400 and 200 from home on a 2040m race), so this keeps those labelled points.
Each value is the average distance off the rail over the section that STARTS at from_m (800 = the 800m to 600m section).
Real PDFs exist from 28 Apr 2026 (earlier ids answer with a tiny non-PDF reply).

Writes data/gps/rc_pdf_rail_{year}.parquet: meet_code, race_no, tab_no, horse, finish, from_m, to_m, rail_m (merged on those keys,
like the atc / rc / rq files).

    python rc_pdf_gps.py download --since 2026-10-20 [--until 2026-10-25]
    python rc_pdf_gps.py parse
    python rc_pdf_gps.py merge
    python rc_pdf_gps.py parse --file work/rc_pdf/5195542_08.pdf      # one file, prints the rows and the checks
"""
from __future__ import annotations

import argparse
import glob
import io
import logging
import re
import sys
import time
from pathlib import Path

import pandas as pd
import pdfplumber
import requests

ROOT = Path(__file__).resolve().parent
GPS_DIR = ROOT / "data" / "gps"
WORK = ROOT / "work" / "rc_pdf"
OUT_DIR = ROOT / "work" / "rc_pdf_new"
BASE = "https://d3qmfyv6ad9vwv.cloudfront.net"
KEYS = ["meet_code", "race_no", "tab_no", "from_m"]
LABEL = re.compile(r"^(\d{1,2}(?:\.\d)?)m$")
logging.getLogger("pdfminer").setLevel(logging.ERROR)


def _dedupe(page):
    """Each label is drawn several times on top of itself with small offsets (a halo), so a word comes out as '5555.5mmm'. Keep one copy of
    every character: skip a character if the same one was already kept within 2.5 points."""
    kept: dict = {}

    def keep(o):
        if o.get("object_type") != "char":
            return True
        for x, y in kept.get(o["text"], ()):
            if abs(x - o["x0"]) < 2.5 and abs(y - o["top"]) < 2.5:
                return False
        kept.setdefault(o["text"], []).append((o["x0"], o["top"]))
        return True

    return page.filter(keep)


def _centre(w):
    return (w["x0"] + w["x1"]) / 2


def parse_runner_page(page) -> dict | None:
    """One runner's page: header (finish place, name, TAB) and the Distance from Rail labels by section."""
    pg = _dedupe(page)
    words = pg.extract_words(extra_attrs=["size"])
    heads = [w for w in words if w["text"] == "Distance" and w["size"] > 10]
    if not heads:
        return None
    head = heads[0]
    right = [w for w in words if w["x0"] > page.width * 0.5]
    # tick labels: whole numbers printed under the charts; the Stride Length chart (top right) has all of them, the Rail chart a subset
    ticks = [w for w in right if re.fullmatch(r"\d{3,4}", w["text"]) and w["size"] < 8]
    if not ticks:
        return None
    rows = sorted({round(w["top"]) for w in ticks})
    # group the tick labels into rows (each chart has one row), the first row is the widest chart row
    byrow: dict[int, list] = {}
    for w in ticks:
        key = next((r for r in byrow if abs(r - w["top"]) < 3), round(w["top"]))
        byrow.setdefault(key, []).append(w)
    grid_row = max((r for r in byrow if r < head["top"]), key=lambda r: len(byrow[r]), default=None)
    if grid_row is None:
        return None
    grid = sorted(byrow[grid_row], key=lambda w: w["x0"])
    gx = [_centre(w) for w in grid]
    gv = [int(w["text"]) for w in grid]
    if len(grid) < 4:
        return None
    step = (gx[-1] - gx[0]) / (len(gx) - 1)
    labels = [w for w in right if LABEL.match(w["text"]) and head["top"] < w["top"] < head["top"] + 140]
    out = []
    for w in labels:
        i = round((_centre(w) - gx[0]) / step)
        if not 0 <= i < len(gv) or abs(_centre(w) - gx[i]) > step * 0.35:
            continue
        out.append((gv[i], float(LABEL.match(w["text"]).group(1))))
    # header: the finish place sits in a box at the left (about 18pt), the horse name is the 34pt text
    rank = next((w["text"] for w in words if w["top"] < 250 and w["x0"] < 75 and 15 <= w["size"] <= 22 and re.fullmatch(r"\d{1,2}", w["text"])), None)
    name = " ".join(w["text"] for w in sorted([w for w in words if w["size"] >= 30 and w["top"] < 250], key=lambda w: w["x0"]))
    race_word = next((words[i + 1]["text"] for i, w in enumerate(words) if w["text"] == "RACE" and i + 1 < len(words) and w["top"] < 150), None)
    tab = None
    for i, w in enumerate(words):
        if w["text"] == "TAB" and i + 1 < len(words) and re.fullmatch(r"\d{1,2}", words[i + 1]["text"]):
            tab = int(words[i + 1]["text"])
            break
    if tab is None or not out:
        return None
    return dict(tab_no=tab, horse=name, finish=int(rank) if rank else None, race=int(race_word) if race_word and race_word.isdigit() else None,
                points=sorted(set(out), reverse=True), grid=gv)


def parse_old_page(page) -> dict | None:
    """Older report layout (Apr to Jul 2026): one table per runner page with a column for every section. It has no TAB number, so the caller
    matches the horse name and finish place to the runner."""
    words = page.extract_words()
    txt = " ".join(w["text"] for w in words)
    m = re.search(r"Horse/Jockey Name (.+?)/", page.extract_text() or "")
    if not m:
        return None
    rank = re.search(r"Finish Rank (\d+)", txt)
    race = re.search(r"Race (\d+):", txt)
    hdr = [w for w in words if re.fullmatch(r"Overall|L\d{3,4}", w["text"]) and w["top"] < 260]
    if len(hdr) < 3:
        return None
    htop = min(w["top"] for w in hdr)
    hdr = [w for w in hdr if abs(w["top"] - htop) < 3]
    # the Rail row: starts with the label 'Avg. Dist. to Rail [m]'
    lab = next((w for w in words if w["text"] == "Rail" and w["x0"] < 200 and w["top"] > htop), None)
    if lab is None:
        return None
    vals = [w for w in words if abs(w["top"] - lab["top"]) < 3 and w["x0"] > lab["x1"] + 5 and re.fullmatch(r"-?\d+(?:\.\d)?", w["text"])]
    pts = []
    for v in vals:
        h = min(hdr, key=lambda w: abs(_centre(w) - _centre(v)))
        if abs(_centre(h) - _centre(v)) > 25 or h["text"] == "Overall":
            continue
        pts.append((int(h["text"][1:]), float(v["text"])))
    if not pts:
        return None
    return dict(tab_no=None, horse=m.group(1).strip(), finish=int(rank.group(1)) if rank else None, race=int(race.group(1)) if race else None,
                points=sorted(set(pts), reverse=True))


def parse_pdf(src, meet_code: str, race_no: int) -> pd.DataFrame:
    rows = []
    with pdfplumber.open(io.BytesIO(src) if isinstance(src, (bytes, bytearray)) else src) as pdf:
        for page in pdf.pages:
            r = parse_runner_page(page) or parse_old_page(page)
            if not r:
                continue
            if r["race"] is not None and r["race"] != int(race_no):
                raise ValueError(f"page says race {r['race']}, expected {race_no}")
            for v, m in r["points"]:
                rows.append(dict(meet_code=str(meet_code), race_no=int(race_no), tab_no=r["tab_no"], horse=r["horse"], finish=r["finish"],
                                 from_m=v, to_m=max(v - 200, 0), rail_m=m))
    return pd.DataFrame(rows)


def check(df: pd.DataFrame) -> list[str]:
    msgs = []
    if df.empty:
        return ["no rows"]
    if (df.rail_m > 40).any() or (df.rail_m < 0).any():
        msgs.append("rail_m outside 0 to 40")
    d = df.groupby("tab_no").size()
    if d.min() < 3:
        msgs.append(f"a runner has {d.min()} labelled points")
    if df.tab_no.notna().all() and df.duplicated(["tab_no", "from_m"]).any():
        msgs.append("duplicate tab/section")
    return msgs


# ---------------------------------------------------------------- download / parse / merge
def _meetings(since: str, until: str | None) -> pd.DataFrame:
    fs = sorted(glob.glob(str(GPS_DIR / "rc_gps_runs_*.parquet")))
    r = pd.concat([pd.read_parquet(f, columns=["meet_code", "race_no", "start_utc"]) for f in fs])
    r["d"] = pd.to_datetime(r.start_utc).dt.tz_convert("Australia/Melbourne").dt.date.astype(str)
    r = r[(r.d >= since) & (r.d <= (until or "9999"))]
    return r.drop_duplicates(["meet_code", "race_no"])[["meet_code", "race_no", "d"]].sort_values(["d", "meet_code", "race_no"])


def _fetch(args):
    sess, code, race = args
    f = WORK / f"{code}_{race:02d}.pdf"
    if f.exists() and f.stat().st_size > 5000:
        return "have"
    try:
        resp = sess.get(f"{BASE}/{code}_{race:02d}.pdf", timeout=40)
    except requests.RequestException:
        return "error"
    if resp.ok and resp.content[:4] == b"%PDF" and len(resp.content) > 5000:
        f.write_bytes(resp.content)
        return "got"
    return "none"


def download(since: str, until: str | None = None, workers: int = 8) -> None:
    from concurrent.futures import ThreadPoolExecutor

    WORK.mkdir(parents=True, exist_ok=True)
    m = _meetings(since, until)
    s = requests.Session()
    s.headers["User-Agent"] = "Mozilla/5.0 TopRate research"
    jobs = [(s, str(r.meet_code), int(r.race_no)) for r in m.itertuples()]
    with ThreadPoolExecutor(workers) as ex:
        res = list(ex.map(_fetch, jobs))
    c = {k: res.count(k) for k in ("got", "have", "none", "error")}
    print(f"{len(m)} races listed: {c['got']} downloaded, {c['have']} already here, {c['none']} with no PDF, {c['error']} fetch errors")


def _norm(x) -> str:
    return re.sub(r"[^A-Z0-9]", "", str(x).upper())


def resolve_tabs(df: pd.DataFrame) -> pd.DataFrame:
    """The older layout has no TAB number: take it from racing.com's runner list (same meeting and race) by horse name, else finish place."""
    if df.empty or df.tab_no.notna().all():
        return df
    fs = sorted(glob.glob(str(GPS_DIR / "rc_gps_runs_*.parquet")))
    r = pd.concat([pd.read_parquet(f, columns=["meet_code", "race_no", "horse", "tab_no", "finish"]) for f in fs])
    r["meet_code"] = r.meet_code.astype(str)
    r["hn"] = r.horse.map(_norm)
    by_name = {(m, int(n), h): int(t) for m, n, h, t in zip(r.meet_code, r.race_no, r.hn, r.tab_no) if pd.notna(t)}
    by_fin = {(m, int(n), int(f)): int(t) for m, n, f, t in zip(r.meet_code, r.race_no, r.finish, r.tab_no) if pd.notna(t) and pd.notna(f) and f > 0}
    out = df.copy()
    miss = out.tab_no.isna()
    got = [by_name.get((m, int(n), _norm(h))) or (by_fin.get((m, int(n), int(f))) if pd.notna(f) else None)
           for m, n, h, f in zip(out.meet_code[miss], out.race_no[miss], out.horse[miss], out.finish[miss])]
    out.loc[miss, "tab_no"] = pd.Series(got, index=out.index[miss], dtype="float")
    n_bad = int(out.tab_no.isna().sum())
    if n_bad:
        print(f"{n_bad} rows without a TAB number were dropped")
    out = out[out.tab_no.notna()].copy()
    out["tab_no"] = out.tab_no.astype(int)
    return out


def _parse_file(f: Path):
    mc, rn = f.stem.split("_")
    try:
        df = parse_pdf(str(f), mc, int(rn))
        return f.name, df, None
    except Exception as e:  # noqa: BLE001
        return f.name, None, repr(e)


CACHE = ROOT / "work" / "rc_pdf_parsed"


def parse_all(out: Path = OUT_DIR, workers: int = 4) -> None:
    """Parses every downloaded PDF. Each result is cached in work/rc_pdf_parsed/ as it arrives, so a run that is cut short (a restarted
    runner or session) carries on where it stopped; delete that folder to re-parse everything."""
    from concurrent.futures import ProcessPoolExecutor

    out.mkdir(parents=True, exist_ok=True)
    CACHE.mkdir(parents=True, exist_ok=True)
    problems = []
    files = sorted(WORK.glob("*.pdf"))
    todo = [f for f in files if not (CACHE / f"{f.stem}.parquet").exists()]
    print(f"{len(files)} PDFs, {len(files) - len(todo)} already parsed, {len(todo)} to do", flush=True)
    done = 0
    with ProcessPoolExecutor(workers) as ex:
        for name, df, err in ex.map(_parse_file, todo, chunksize=2):
            if err:
                problems.append(f"{name}: {err}")
            else:
                (df if df is not None else pd.DataFrame()).to_parquet(CACHE / f"{Path(name).stem}.parquet", index=False)
            done += 1
            if done % 100 == 0:
                print(f"  {done}/{len(todo)}", flush=True)
    parts = []
    for f in files:
        c = CACHE / f"{f.stem}.parquet"
        if not c.exists():
            continue
        df = pd.read_parquet(c)
        msgs = check(df)
        if msgs:
            problems.append(f"{f.name}: {'; '.join(msgs)}")
        if not df.empty:
            parts.append(df)
    allr = resolve_tabs(pd.concat(parts, ignore_index=True)) if parts else pd.DataFrame()
    allr.to_parquet(out / "rc_pdf_rail.parquet", index=False)
    print(f"parsed {len(parts)} races, {len(allr):,} rows; {len(problems)} with problems")
    if problems:
        (out / "rc_pdf_problems.txt").write_text("\n".join(problems))


def _year_of(meet_code: str, dates: dict) -> str:
    return dates.get(meet_code, "unknown")


def merge(new_dir: Path = OUT_DIR) -> None:
    f = new_dir / "rc_pdf_rail.parquet"
    if not f.exists():
        print("nothing to merge")
        return
    new = pd.read_parquet(f)
    if new.empty:
        print("nothing to merge")
        return
    fs = sorted(glob.glob(str(GPS_DIR / "rc_gps_runs_*.parquet")))
    dm = pd.concat([pd.read_parquet(x, columns=["meet_code", "start_utc"]) for x in fs]).drop_duplicates("meet_code")
    dm["year"] = pd.to_datetime(dm.start_utc).dt.year.astype(str)
    new = new.merge(dm[["meet_code", "year"]], on="meet_code", how="left")
    new["year"] = new.year.fillna(str(pd.Timestamp.now().year))
    GPS_DIR.mkdir(parents=True, exist_ok=True)
    wrote = []
    for year, z in new.groupby("year"):
        z = z.drop(columns="year")
        p = GPS_DIR / f"rc_pdf_rail_{year}.parquet"
        if p.exists():
            old = pd.read_parquet(p)
            races = z[["meet_code", "race_no"]].drop_duplicates()
            old = old.merge(races.assign(_x=1), on=["meet_code", "race_no"], how="left")
            old = old[old._x.isna()].drop(columns="_x")   # a re-read race replaces its earlier rows
            z = pd.concat([old, z], ignore_index=True)
        z = z.drop_duplicates(KEYS, keep="last").sort_values(KEYS)
        if p.exists() and pd.read_parquet(p).equals(z.reset_index(drop=True)):
            continue
        z.to_parquet(p, index=False)
        wrote.append(p.name)
    print("wrote", ", ".join(wrote) or "nothing (no change)")


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    d = sub.add_parser("download")
    d.add_argument("--since", required=True)
    d.add_argument("--until")
    p = sub.add_parser("parse")
    p.add_argument("--file")
    p.add_argument("--out", default=str(OUT_DIR))
    m = sub.add_parser("merge")
    m.add_argument("--new", default=str(OUT_DIR))
    a = ap.parse_args()
    if a.cmd == "download":
        download(a.since, a.until)
    elif a.cmd == "merge":
        merge(Path(a.new))
    elif a.file:
        mc, rn = Path(a.file).stem.split("_")
        df = resolve_tabs(parse_pdf(a.file, mc, int(rn)))
        print(df.to_string(index=False))
        print("checks:", check(df) or "ok")
    else:
        parse_all(Path(a.out))
