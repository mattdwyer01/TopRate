"""Read-only: HEAD/Range-GET the Sky Racing replay URLs found in TAB's meeting list and report
status, content-type, size, CORS headers. Run from the AU runner. Writes nothing."""
import tab_results_poller as tp
from datetime import datetime
import zoneinfo

def main():
    from datetime import date
    d = date.today().isoformat()
    data = tp.get(tp.MEETINGS.format(date=d), {"jurisdiction": "VIC"})
    urls, chan, n_races = [], {}, 0
    for m in data.get("meetings", []):
        for r in m.get("races", []):
            n_races += 1
            sr = r.get("skyRacing") or {}
            chan[r.get("broadcastChannel")] = chan.get(r.get("broadcastChannel"), 0) + 1
            if sr.get("video"):
                urls.append((m.get("meetingName"), r.get("raceNumber"), r.get("raceStatus"), r.get("raceStartTime"), sr["video"], sr.get("audio")))
    print(f"races={n_races} with_video={len(urls)} channels={chan}")
    st = {}
    for u in urls:
        st[u[2]] = st.get(u[2], 0) + 1
    print("video by raceStatus:", st)
    import requests
    pick = [u for u in urls if u[2] in tp.FINAL_STATUSES][:3] + urls[:1]
    for mn, rn, status, start, v, a in pick:
        print(f"\n{mn} R{rn} status={status} start={start}\n  {v}")
        for url in (v, a):
            if not url:
                continue
            for hdrs in ({}, {"Origin": "https://mattdwyer01.github.io", "Range": "bytes=0-1023"}):
                try:
                    r = requests.get(url, headers=hdrs, timeout=20, stream=True)
                    keep = {k: r.headers.get(k) for k in ("content-type", "content-length", "content-range", "accept-ranges", "access-control-allow-origin", "x-frame-options", "cache-control")}
                    print(f"  GET {'(origin+range)' if hdrs else '(plain)'} -> {r.status_code} {keep}")
                    r.close()
                except Exception as e:
                    print("  ERR", type(e).__name__, e)
    # sample of the skyRacing/media dict shape for one race
    for m in data.get("meetings", [])[:50]:
        for r in m.get("races", []):
            if r.get("skyRacing"):
                print("\nsample skyRacing:", r["skyRacing"], "| channel:", r.get("broadcastChannel"), r.get("broadcastChannels"))
                return
main()
