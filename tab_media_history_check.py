"""Read-only: learn Sky venue codes from today's TAB meeting list (all jurisdictions), then try the
CONSTRUCTED replay URL for past dates to see how long Sky keeps files. Run from the AU runner."""
import re, requests
from datetime import date, timedelta
import tab_results_poller as tp

def probe(url):
    try:
        r = requests.get(url, headers={"Range": "bytes=0-255"}, timeout=15, stream=True)
        s = r.status_code; r.close(); return s
    except Exception:
        return "ERR"

codes = {}
for j in ("VIC", "NSW", "QLD", "SA", "WA", "TAS", "NT", "ACT"):
    try:
        data = tp.get(tp.MEETINGS.format(date=date.today().isoformat()), {"jurisdiction": j})
    except Exception as e:
        print(j, "ERR", e); continue
    for m in data.get("meetings", []):
        for r in m.get("races", []):
            u = (r.get("skyRacing") or {}).get("video")
            mm = u and re.search(r"/\d{8}([A-Z]+)\d{2}_V\.mp4", u)
            if mm: codes[mm.group(1)] = m.get("meetingName")
print(f"{len(codes)} codes today:", codes)

for back in (1, 2, 3, 7, 14, 30, 60, 90, 180, 365, 730):
    d = date.today() - timedelta(days=back)
    hits = tried = 0; ex = None
    for code in codes:
        for rn in (1, 2):
            url = f"https://mediatabs.skyracing.com.au/Race_Replay/{d:%Y}/{d:%m}/{d:%Y%m%d}{code}{rn:02d}_V.mp4"
            tried += 1
            if probe(url) in (200, 206):
                hits += 1; ex = ex or url
    print(f"-{back}d {d}: tried={tried} hits={hits} e.g. {ex}")
