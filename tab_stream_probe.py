"""Read-only: does TAB's per-race detail (or the meeting/race _links) carry any live-stream, video or
broadcast field? Fetches one open race and one just-run race with the same call the poller's dividends
code uses (jurisdiction param, venueMnemonic), then lists every media-like key/value plus all _links.
Writes nothing. Run from the AU runner."""
import json, re
from datetime import date
import tab_results_poller as tp

RX = re.compile(r"video|replay|stream|media|sky|vimeo|brightcove|youtube|m3u8|mp4|hls|embed|player|live|vision|broadcast|channel|watch|cdn|rtmp|dash", re.I)

def walk(o, path, hits, depth=0):
    if isinstance(o, dict):
        for k, v in o.items():
            p = f"{path}.{k}" if path else k
            if RX.search(str(k)) or (isinstance(v, str) and RX.search(v) and len(v) < 300):
                hits.append((p, v if not isinstance(v, (dict, list)) else f"<{type(v).__name__} len {len(v)}>"))
            walk(v, p, hits, depth + 1)
    elif isinstance(o, list):
        for i, v in enumerate(o[:60]):
            walk(v, f"{path}[{i}]", hits, depth + 1)

def keys(o, path="", out=None, depth=0):
    out = [] if out is None else out
    if isinstance(o, dict) and depth < 3:
        for k, v in o.items():
            out.append(f"{path}.{k}" if path else k)
            keys(v, f"{path}.{k}" if path else k, out, depth + 1)
    elif isinstance(o, list) and o and depth < 3:
        keys(o[0], path + "[0]", out, depth + 1)
    return out

def report(label, payload):
    print(f"\n=== {label} ===", flush=True)
    ks = keys(payload)
    print(f"{len(ks)} key paths (depth<=3). top-level:", sorted(payload.keys()) if isinstance(payload, dict) else type(payload).__name__, flush=True)
    hits = []; walk(payload, "", hits)
    seen = set()
    for p, v in hits:
        k = (re.sub(r"\[\d+\]", "[]", p), str(v)[:80])
        if k in seen: continue
        seen.add(k); print(f"  MEDIA-LIKE {p} = {v}", flush=True)
    if not hits: print("  nothing media/stream-like", flush=True)
    for lk in ("_links", "links"):
        if isinstance(payload, dict) and payload.get(lk):
            print(f"  {lk}:", json.dumps(payload[lk])[:800], flush=True)

today = date.today().isoformat()
picked = {}
for j in ("VIC", "NSW", "QLD", "SA", "WA", "TAS", "NT", "ACT"):
    try:
        data = tp.get(tp.MEETINGS.format(date=today), {"jurisdiction": j})
    except Exception as e:
        print(j, "ERR", e); continue
    for m in data.get("meetings", []):
        if m.get("raceType") != "R" or m.get("location") not in tp.AU_STATES: continue
        mn = m.get("venueMnemonic")
        if m.get("_links") and "meeting_links" not in picked:
            picked["meeting_links"] = (m.get("meetingName"), m["_links"])
        for r in m.get("races", []):
            st = r.get("raceStatus")
            kind = "open" if st in ("Open", "Normal") else ("resulted" if st == "Paying" else None)
            if kind and kind not in picked and mn:
                picked[kind] = (j, m.get("meetingName"), mn, r.get("raceNumber"), st, r)
print("meeting _links sample:", json.dumps(picked.get("meeting_links"))[:600], flush=True)
for kind in ("open", "resulted"):
    if kind not in picked:
        print(f"no {kind} race found today"); continue
    j, name, mn, rn, st, stub = picked[kind]
    print(f"\n#### {kind}: {name} R{rn} status={st}", flush=True)
    report(f"race STUB from meeting list ({kind})", stub)
    try:
        detail = tp.get(tp.RACE_DETAIL.format(date=today, venue_mnemonic=mn, race_no=rn), {"jurisdiction": j})
        report(f"race DETAIL ({kind})", detail)
    except Exception as e:
        print(f"detail fetch failed: {type(e).__name__} {e}", flush=True)
