"""Read-only: where does https://i.mjh.nz/.r/sky-racing-1.m3u8 point and what does it serve? Follows redirects by hand,
prints status, host, path (query strings stripped, they can carry tokens), content-type and CORS headers, then the playlist's
own (comment/tag) lines and segment HOSTS only. Downloads the playlist text only, never video segments."""
import re
from urllib.parse import urljoin, urlparse
from curl_cffi import requests as cr

def clean(u):
    p = urlparse(u); return f"{p.scheme}://{p.netloc}{p.path}" + ("?<query stripped>" if p.query else "")

url = "https://i.mjh.nz/.r/sky-racing-1.m3u8"
for hop in range(8):
    r = cr.get(url, impersonate="chrome", timeout=25, allow_redirects=False)
    h = {k.lower(): v for k, v in r.headers.items()}
    print(f"\nHOP {hop}: {clean(url)}\n  status={r.status_code} type={h.get('content-type')} len={len(r.content)}", flush=True)
    print(f"  CORS allow-origin={h.get('access-control-allow-origin')} server={h.get('server')} cache={h.get('cache-control')}", flush=True)
    if r.status_code in (301, 302, 303, 307, 308) and h.get("location"):
        url = urljoin(url, h["location"]); continue
    text = r.text if len(r.content) < 200000 else ""
    lines = text.splitlines()
    print(f"  playlist lines={len(lines)} first tags:", flush=True)
    for ln in lines[:25]:
        if ln.startswith("#") or not ln.strip():
            print("   ", ln[:140], flush=True)
        else:
            print("    <uri>", clean(urljoin(url, ln.strip())), flush=True)
    hosts = sorted({urlparse(urljoin(url, ln.strip())).netloc for ln in lines if ln.strip() and not ln.startswith("#")})
    print("  uri hosts:", hosts, flush=True)
    print("  encryption/drm tags:", [ln[:100] for ln in lines if re.search(r"EXT-X-KEY|EXT-X-SESSION-KEY|DRM|WIDEVINE|FAIRPLAY", ln, re.I)][:5], flush=True)
    break
