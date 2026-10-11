"""
atc_ingest.py -- Australian Turf Club (Randwick, Rosehill, Canterbury, Warwick Farm) results and sectionals into data/gps/ (Oct 2026).

Plain HTTP, no browser. Per meeting code:
  GET /meeting/<code>                              results page: per race a heading, a margin/last-600/track/rail block and a results table
  GET /meeting/sectionals/<code>?meetingId=<code>  sectionals fragment: per race a horse table and a cumulative-time table
Meeting codes are opaque; recent ones come from /latest-racing/N (unquoted href=meeting/<code>, or trials/<code> which are skipped).

Writes (append, one row per runner / per split), same layout as the other sources so one loader can read all of them:
  data/gps/atc_gps_runs_<year>.parquet      source, race_date, meeting_code, course, race_no, race_distance, going, rail_text, race_time_s,
                                            horse, tab_no, barrier, weight, jockey, sp, finish, margin_l, time_s
  data/gps/atc_gps_sections_<year>.parquet  meeting_code, race_no, tab_no, horse, from_m, to_m, pos, split_s
Run on the AU runner (the sandbox cannot reach the host). Usage:
  python atc_ingest.py --index 6            # discover codes on /latest-racing/0..5, ingest the ones not yet stored
  python atc_ingest.py --code oY3R5qzn --date 2026-10-03 --course Randwick
  python atc_ingest.py --selftest           # parser check on the built-in fixture (works anywhere)
"""
import argparse
import html
import re
import sys
from datetime import date, datetime
from pathlib import Path

BASE = "https://racing.australianturfclub.com.au"
OUT = Path(__file__).parent / "data" / "gps"
RAW = Path(__file__).parent / "tab_raw"

# beaten-margin words to lengths
WORD = {"nse": 0.05, "shd": 0.1, "sh hd": 0.1, "short head": 0.1, "hd": 0.2, "head": 0.2, "nk": 0.3, "neck": 0.3, "lg": 1.0}


def fetch(url):
    try:
        from curl_cffi import requests as cr
        return cr.get(url, impersonate="chrome", timeout=30, headers={"Accept": "*/*"})
    except ImportError:
        import requests
        return requests.get(url, timeout=30, headers={"User-Agent": "Mozilla/5.0"})


def text(frag):
    return re.sub(r"\s+", " ", html.unescape(re.sub(r"<[^>]+>", " ", frag or ""))).strip()


def secs(s):
    """'1:22.25' or '00:13.48' or '13.48' -> seconds."""
    m = re.match(r"^\s*(?:(\d+):)?(\d+(?:\.\d+)?)\s*$", s or "")
    return None if not m else (int(m.group(1)) * 60 if m.group(1) else 0) + float(m.group(2))


def margin_len(s):
    """'3 1/4 len', '1/2', 'nk', 'hd', 'sh hd', '2.5' -> lengths (None if unreadable)."""
    t = (s or "").lower().replace("len", "").replace("lgs", "").replace("-", " ").strip()
    if not t:
        return None
    if t in WORD:
        return WORD[t]
    tot, ok = 0.0, False
    for part in t.split():
        if re.fullmatch(r"\d+/\d+", part):
            a, b = part.split("/")
            tot += int(a) / int(b); ok = True
        elif re.fullmatch(r"\d+(?:\.\d+)?", part):
            tot += float(part); ok = True
        elif part in WORD:
            tot += WORD[part]; ok = True
        else:
            return None
    return tot if ok else None


def panels(body):
    """{race_no: html} split on the race panel markers."""
    parts = re.split(r'<div class="racing-meet-race-panel"[^>]*?data-race-number="(\d+)"[^>]*>', body)
    return {int(parts[i]): parts[i + 1] for i in range(1, len(parts) - 1, 2)}


def weather_blocks(pan):
    """label -> value for the small 'weather-block' tiles (Margin, Last 600, Track, Rail, Penetrometer, Time ...)."""
    out = {}
    for blk in re.split(r'<div class="weather-block">', pan)[1:]:
        lab = re.search(r'<p class="(?:weather|track)-label">(.*?)</p>', blk, re.S)
        val = re.search(r'<p class="(?:other-desc|weather-desc|track-desc|margin-one)">(.*?)</p>', blk, re.S)
        if lab and val:
            out[text(lab.group(1))] = text(val.group(1))
    return out


def parse_results(body, race_date, course, code):
    runs = []
    for rno, pan in panels(body).items():
        spans = [text(x) for x in re.findall(r"<span>(.*?)</span>", pan.split('<table')[0], re.S)]
        dist = next((int(m.group(1)) for s in spans for m in [re.fullmatch(r"(\d{3,4})m", s)] if m), None)
        wb = weather_blocks(pan)
        race_time = secs(wb.get("Time"))
        tbl = re.search(r'<table id="race-results-table">(.*?)</table>', pan, re.S)
        if not tbl:
            continue
        for tr in re.findall(r"<tr>(.*?)</tr>", tbl.group(1).split("<tbody>")[-1], re.S):
            cell = {c: text(v) for c, v in re.findall(r'<td class="([a-z]+)"[^>]*>(.*?)</td>', tr, re.S)}
            if "horse" not in cell:
                continue
            pos = re.search(r"\d+", cell.get("placing", ""))
            tab = re.search(r"\d+", cell.get("tab", ""))
            if not pos:      # scratched / non-runner rows carry no placing
                continue
            m = margin_len(cell.get("margin"))
            # the margin column is taken as already cumulative to the winner (MAE vs the time-derived margin is printed at ingest)
            mw = 0.0 if (pos and int(pos.group(0)) == 1) else m
            runs.append(dict(source="atc", race_date=race_date, meeting_code=code, course=course, race_no=rno, race_distance=dist,
                             going=wb.get("Track"), rail_text=wb.get("Rail"), race_time_s=race_time,
                             horse=re.sub(r"\s*\([A-Z]{2,3}\)\s*$", "", cell["horse"]).strip(), tab_no=int(tab.group(0)) if tab else None,
                             barrier=_f(cell.get("barrier")), weight=_f(cell.get("weight")), jockey=cell.get("jockey"),
                             sp=_f(cell.get("sp")), finish=int(pos.group(0)) if pos else None, margin_l=mw, margin_raw=cell.get("margin"), margin_t=None, time_s=None))
    return runs


def _f(s):
    m = re.search(r"\d+(?:\.\d+)?", s or "")
    return float(m.group(0)) if m else None


def parse_sectionals(body, code):
    """{(race_no, tab_no): dict(horse, finish, time_s, sections=[(from_m, to_m, pos, split_s)])}"""
    out = {}
    for rno, pan in panels(body).items():
        tabs = re.findall(r"<table[^>]*>(.*?)</table>", pan, re.S)
        if len(tabs) < 2:
            continue
        horses = []
        for tr in re.findall(r"<tr>(.*?)</tr>", tabs[0].split("<tbody>")[-1], re.S):
            nm = re.search(r'sect-placing-name">(.*?)</div>', tr, re.S)
            tb = re.search(r'sect-tab-number">\s*\((\d+)\)', tr, re.S)
            if nm and tb:
                t = text(nm.group(1))
                mm = re.match(r"(\d+)\.\s*(.*)", t)
                horses.append((int(tb.group(1)), re.sub(r"\s*\([A-Z]{2,3}\)\s*$", "", (mm.group(2) if mm else t)).strip(), int(mm.group(1)) if mm else None))
        head = re.findall(r'<th class="sect-times">(.*?)</th>', tabs[1], re.S)
        marks = [text(h) for h in head]
        rows = re.findall(r"<tr>(.*?)</tr>", tabs[1].split("<tbody>")[-1], re.S)
        # race distance is not in the fragment; take the first mark that is numeric as the first split's end
        for (tab, nm, fin), tr in zip(horses, rows):
            cells = re.findall(r'<td class="sect-times">(.*?)</td>', tr, re.S)
            secs_, prev_mark, last_cum = [], None, None
            for mk, c in zip(marks, cells):
                divs = [text(d) for d in re.findall(r'<div class="sect-time-rank">(.*?)</div>', c, re.S)]
                if len(divs) < 2:
                    continue
                cum = secs(re.sub(r"\[.*?\]", "", divs[0]))
                rk = re.search(r"\[(\d+)\]", divs[0])
                split = secs(divs[1])
                to_m = int(mk) if mk.isdigit() else 0
                secs_.append((prev_mark, to_m, int(rk.group(1)) if rk else None, split))
                prev_mark = to_m
                last_cum = cum if cum is not None else last_cum
            out[(rno, tab)] = dict(horse=nm, finish=fin, time_s=last_cum, sections=secs_)
    return out


def merge(runs, sect, code):
    secrows = []
    for r in runs:
        s = sect.get((r["race_no"], r["tab_no"]))
        if not s:
            continue
        r["time_s"] = s["time_s"]
        for fm, to, pos, split in s["sections"]:
            secrows.append(dict(meeting_code=code, race_no=r["race_no"], tab_no=r["tab_no"], horse=r["horse"],
                                from_m=fm if fm is not None else r["race_distance"], to_m=to, pos=pos, split_s=split))
    # margin from times when the results page margin was unreadable (0.163 s per length, the WA calibration)
    byrace = {}
    for r in runs:
        byrace.setdefault(r["race_no"], []).append(r)
    for rs in byrace.values():
        t0 = min((x["time_s"] for x in rs if x["time_s"]), default=None)
        for x in rs:
            if x["time_s"] and t0:
                x["margin_t"] = round((x["time_s"] - t0) / 0.163, 2)
            if x["margin_l"] is None:
                x["margin_l"] = x["margin_t"]
    return runs, secrows


def index(pages):
    """[(code, date, label)] of recent race meetings from /latest-racing/N."""
    seen, out = set(), []
    for n in range(pages):
        r = fetch(f"{BASE}/latest-racing/{n}")
        if r.status_code != 200:
            break
        for m in re.finditer(r'<a href=meeting/([A-Za-z0-9]{6,10})[^>]*title="([^"]*)"(.*?)</a>', r.text, re.S):
            code, title, inner = m.groups()
            if code in seen:
                continue
            seen.add(code)
            d = re.search(r'latest-race-date">\s*([A-Za-z]{3}) (\d{1,2}) ([A-Za-z]{3})', inner)
            loc = re.search(r'latest-race-location">(.*?)<', inner, re.S)
            dt = None
            if d:
                for y in (date.today().year, date.today().year - 1):
                    try:
                        c = datetime.strptime(f"{d.group(2)} {d.group(3)} {y}", "%d %b %Y").date()
                        if c.strftime("%a") == d.group(1) and c <= date.today():
                            dt = c; break
                    except ValueError:
                        pass
            out.append((code, dt, text(loc.group(1)) if loc else ""))
    return out


def ingest(code, race_date, course, save_raw=False):
    r1 = fetch(f"{BASE}/meeting/{code}")
    r2 = fetch(f"{BASE}/meeting/sectionals/{code}?meetingId={code}")
    if r1.status_code != 200:
        print(f"  {code}: results HTTP {r1.status_code}"); return 0
    if save_raw:
        RAW.mkdir(exist_ok=True)
        (RAW / f"atc_{code}_results.html").write_text(r1.text)
        (RAW / f"atc_{code}_sectionals.html").write_text(r2.text or "")
    runs = parse_results(r1.text, race_date, course, code)
    sect = parse_sectionals(r2.text or "", code) if r2.status_code == 200 else {}
    runs, secrows = merge(runs, sect, code)
    if not runs:
        print(f"  {code}: no runners parsed"); return 0
    import pandas as pd
    yr = str(race_date)[:4]
    OUT.mkdir(parents=True, exist_ok=True)
    for name, rows, key in (("runs", runs, ["meeting_code", "race_no", "tab_no"]), ("sections", secrows, ["meeting_code", "race_no", "tab_no", "from_m", "to_m"])):
        f = OUT / f"atc_gps_{name}_{yr}.parquet"
        new = pd.DataFrame(rows)
        old = pd.read_parquet(f) if f.exists() else None
        allr = pd.concat([old, new], ignore_index=True) if old is not None else new
        allr.drop_duplicates(key, keep="last").to_parquet(f, index=False)
    races = {r["race_no"] for r in runs}
    for rno in sorted(races):
        rr = [r for r in runs if r["race_no"] == rno]
        miss = [(r["finish"], r["tab_no"], r["margin_raw"]) for r in rr if not r["time_s"]]
        if miss and sect:
            print(f"    R{rno}: {len(rr)} results rows, {sum(1 for k in sect if k[0] == rno)} sectional rows, no time for {miss[:4]}")
    d = [abs(r["margin_l"] - r["margin_t"]) for r in runs if r["margin_l"] is not None and r["margin_t"] is not None]
    if d:
        print(f"    margin text vs time-derived: n {len(d)} MAE {sum(d) / len(d):.2f} lengths (text read as margin to the winner)")
    print(f"  {code} {race_date} {course}: {len(races)} races, {len(runs)} runners, {len(secrows)} splits, with times {sum(1 for r in runs if r['time_s'])}")
    return len(runs)


FIXTURE_RESULTS = ('<div class="racing-meet-race-panel" data-race-number="1"><div class="race-name-time"><div class="race-name"> PLATE </div>'
    '<div class="race-time"> <span>2.20 PM</span> <span>1400m</span> <span>3YO</span></div></div>'
    '<div class="weather-block"><p class="weather-label">Margin </p><p class="margin-one">3 1/4 len </p><p class="margin-two">x 3</p></div>'
    '<div class="weather-block"><p class="weather-label">Track </p><p class="track-desc">Soft 6</p></div>'
    '<div class="weather-block"><p class="weather-label">Rail </p><p class="other-desc">True</p></div>'
    '<div class="weather-block"><p class="weather-label">Time </p><p class="other-desc">1:22.25</p></div>'
    '<table id="race-results-table"><thead><tr><th class="placing">Pos</th></tr></thead><tbody>'
    '<tr><td class="placing"><div class="placing-num">1</div></td><td class="sp"> 1.45 </td><td class="tab">2</td><td class="horse">Love Story</td><td class="barrier">3</td><td class="weight">57.0</td><td class="oa">0</td><td class="jockey">A Hyeronimus</td><td class="margin">3 1/4 len</td></tr>'
    '<tr><td class="placing"><div class="placing-num">2</div></td><td class="sp"> 9.00 </td><td class="tab">4</td><td class="horse">Iminastate (NZ)</td><td class="barrier">5</td><td class="weight">57.0</td><td class="oa">0</td><td class="jockey">C Schofield</td><td class="margin">3 1/4 len</td></tr>'
    '<tr><td class="placing"><div class="placing-num">3</div></td><td class="sp"> 15.00 </td><td class="tab">10</td><td class="horse">Memorise</td><td class="barrier">1</td><td class="weight">55.5</td><td class="oa">0</td><td class="jockey">T Clark</td><td class="margin">1/2</td></tr>'
    '</tbody></table></div>')
FIXTURE_SECT = ('<div class="racing-meet-race-panel" data-race-number="1"><table><thead><tr><th class="horse">Horse</th></tr></thead><tbody>'
    '<tr><td class="horse"><div class="sect-horse-name"><div class="sect-placing-name"> 1. Love Story </div><div class="sect-tab-number"> (2) </div></div><div class="sect-jockey"> A H </div></td></tr>'
    '<tr><td class="horse"><div class="sect-horse-name"><div class="sect-placing-name"> 2. Iminastate (NZ) </div><div class="sect-tab-number"> (4) </div></div><div class="sect-jockey"> C S </div></td></tr>'
    '</tbody></table><table id="race-sectionals-table"><thead><tr><th class="sect-times">1200</th><th class="sect-times">1000</th><th class="sect-times">Finish</th></tr></thead><tbody>'
    '<tr><td class="sect-times"><div class="sect-time-rank"> 00:13.48 [1] </div><div class="sect-time-rank"> 13.48 </div></td><td class="sect-times"><div class="sect-time-rank"> 00:24.35 [1] </div><div class="sect-time-rank"> 10.87 </div></td><td class="sect-times"><div class="sect-time-rank"> 01:22.25 [1] </div><div class="sect-time-rank"> 11.40 </div></td></tr>'
    '<tr><td class="sect-times"><div class="sect-time-rank"> 00:13.60 [2] </div><div class="sect-time-rank"> 13.60 </div></td><td class="sect-times"><div class="sect-time-rank"> 00:24.50 [2] </div><div class="sect-time-rank"> 10.90 </div></td><td class="sect-times"><div class="sect-time-rank"> 01:22.80 [2] </div><div class="sect-time-rank"> 11.50 </div></td></tr>'
    '</tbody></table><table></table></div>')


def selftest():
    runs = parse_results(FIXTURE_RESULTS, "2026-10-03", "Randwick", "fix")
    sect = parse_sectionals(FIXTURE_SECT, "fix")
    runs, secrows = merge(runs, sect, "fix")
    assert len(runs) == 3 and runs[0]["race_distance"] == 1400 and runs[0]["going"] == "Soft 6" and runs[0]["race_time_s"] == 82.25, runs[0]
    assert [r["margin_l"] for r in runs[:3]] == [0.0, 3.25, 0.5], [r["margin_l"] for r in runs]
    assert runs[1]["horse"] == "Iminastate" and runs[1]["time_s"] == 82.8 and runs[2]["time_s"] is None
    assert len(secrows) == 6 and secrows[0]["from_m"] == 1400 and secrows[0]["to_m"] == 1200 and secrows[1]["from_m"] == 1200
    assert margin_len("sh hd") == 0.1 and margin_len("1 1/2 len") == 1.5 and margin_len("x") is None
    print("selftest ok")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--index", type=int, default=0, help="pages of /latest-racing to scan")
    ap.add_argument("--code"); ap.add_argument("--date"); ap.add_argument("--course", default="")
    ap.add_argument("--raw", action="store_true", help="also save the raw pages under tab_raw/")
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--n", type=int, default=0); ap.add_argument("--any-status", action="store_true")  # tab_probe.yml compatibility
    a = ap.parse_args()
    if a.selftest:
        return selftest()
    if not a.code and not a.index and a.n:   # tab_probe.yml passes --n only: treat it as pages to scan
        a.index, a.raw = a.n, True
    if a.code:
        ingest(a.code, a.date or str(date.today()), a.course, a.raw)
    if a.index:
        have = set()
        import pandas as pd
        for f in OUT.glob("atc_gps_runs_*.parquet"):
            have |= set(pd.read_parquet(f, columns=["meeting_code"]).meeting_code)
        found = index(a.index)
        print(f"index: {len(found)} meetings found, {sum(1 for c, _, _ in found if c in have)} already stored")
        for code, dt, loc in found:
            if code not in have and dt:
                ingest(code, str(dt), loc, a.raw)


if __name__ == "__main__":
    sys.exit(main())
