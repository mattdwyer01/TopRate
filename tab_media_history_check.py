"""Read-only: do TAB meeting lists for PAST dates still carry skyRacing.video, and do the files still serve?
Also prints venue -> Sky code (from the URL) so past runs can be mapped. Run from the AU runner."""
import re, requests
from datetime import date, timedelta
import tab_results_poller as tp

def head(url):
    try:
        r = requests.get(url, headers={"Range": "bytes=0-255"}, timeout=20, stream=True)
        out = (r.status_code, r.headers.get("content-length"), r.headers.get("content-range"))
        r.close(); return out
    except Exception as e:
        return ("ERR", type(e).__name__)

codes = {}
for back in (1, 3, 7, 14, 30, 60, 90, 180, 365, 730, 1200):
    d = (date.today() - timedelta(days=back)).isoformat()
    try:
        data = tp.get(tp.MEETINGS.format(date=d), {"jurisdiction": "VIC"})
    except Exception as e:
        print(f"{d} (-{back}d) meetings ERR {type(e).__name__} {e}"); continue
    n = v = 0; sample = None
    for m in data.get("meetings", []):
        for r in m.get("races", []):
            n += 1
            u = (r.get("skyRacing") or {}).get("video")
            if u:
                v += 1
                mm = re.search(r"/(\d{8})([A-Z]+)(\d{2})_V\.mp4", u)
                if mm: codes[m.get("meetingName")] = mm.group(2)
                sample = sample or u
    print(f"{d} (-{back}d) races={n} with_video_url={v} file_check={head(sample) if sample else None}")
print("\nvenue -> sky code:")
for k, c in sorted(codes.items()): print(f"  {k}: {c}")
