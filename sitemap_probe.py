"""Read-only: public sitemap/robots of skyracing.com.au. Lists page URLs only (no stream addresses are in a sitemap).
Plain unauthenticated GETs from the AU runner."""
import re
from curl_cffi import requests as cr

BASE = "https://www.skyracing.com.au"
LIVEISH = re.compile(r"watch|live|radio|channel|vision|tv|stream|replay|sky1|sky2|central|schedule|listen", re.I)

def get(u):
    try:
        r = cr.get(u, impersonate="chrome", timeout=25, allow_redirects=True)
        print(f"GET {u} -> {r.status_code} {r.headers.get('content-type')} len={len(r.text)}", flush=True)
        return r if r.status_code == 200 else None
    except Exception as e:
        print(f"GET {u} ERR {type(e).__name__} {str(e)[:80]}", flush=True); return None

maps = []
r = get(BASE + "/robots.txt")
if r:
    print("--- robots.txt ---"); print(r.text[:1500], flush=True)
    maps += re.findall(r"(?im)^sitemap:\s*(\S+)", r.text)
for u in (BASE + "/sitemap.xml", BASE + "/sitemap_index.xml", BASE + "/sitemap-0.xml"):
    if u not in maps: maps.append(u)

urls, seen = [], set()
queue = list(maps)
while queue and len(seen) < 25:
    m = queue.pop(0)
    if m in seen: continue
    seen.add(m)
    r = get(m)
    if not r: continue
    locs = re.findall(r"<loc>\s*([^<\s]+)\s*</loc>", r.text)
    subs = [l for l in locs if l.endswith(".xml") or "sitemap" in l.lower()]
    queue += [s for s in subs if s not in seen]
    urls += [l for l in locs if l not in subs]
urls = list(dict.fromkeys(urls))
print(f"\nTOTAL page urls: {len(urls)}", flush=True)
hits = [u for u in urls if LIVEISH.search(u)]
print(f"live-ish page urls: {len(hits)}", flush=True)
for u in hits[:120]:
    print("  ", u, flush=True)
paths = sorted({"/" + "/".join(re.sub(r'^https?://[^/]+/', '', u).split("/")[:1]) for u in urls})
print("\ntop-level sections:", paths[:60], flush=True)
