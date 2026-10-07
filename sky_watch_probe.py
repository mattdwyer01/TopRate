"""Read-only: what does https://www.skyracing.com.au/watch/live send (framing headers, redirects) and how is its
player built (stream/player hints in the HTML and scripts)? Plain unauthenticated GETs from the AU runner. No login."""
import re
from urllib.parse import urljoin
from curl_cffi import requests as cr

HINT = re.compile(r"m3u8|\.mpd|hls|dash|brightcove|jwplayer|videojs|video\.js|shaka|bitmovin|theoplayer|akamai|cloudfront|fastly|token|auth|login|stream|playback|licen[sc]e|drm|widevine|fairplay|cdn|api[./]", re.I)
SEEDS = ["https://www.skyracing.com.au/watch/live", "https://www.skyracing.com.au/watch", "https://www.skyracing.com.au/watch/live?channel=sky1"]

def show(r, label):
    h = {k.lower(): v for k, v in r.headers.items()}
    fa = re.search(r"frame-ancestors[^;]*", h.get("content-security-policy", ""), re.I)
    print(f"\n--- {label}\n  status={r.status_code} final={r.url}", flush=True)
    print(f"  redirect-history={[str(x.url) for x in getattr(r, 'history', [])] if hasattr(r, 'history') else 'n/a'}", flush=True)
    print(f"  x-frame-options={h.get('x-frame-options')} csp-frame-ancestors={fa.group(0) if fa else None}", flush=True)
    print(f"  set-cookie names={[c.split('=')[0] for c in r.headers.get_list('set-cookie')] if hasattr(r.headers, 'get_list') else h.get('set-cookie','')[:120]}", flush=True)
    print(f"  server={h.get('server')} type={h.get('content-type')} len={len(r.text)}", flush=True)

for u in SEEDS:
    try:
        r = cr.get(u, impersonate="chrome", timeout=25, allow_redirects=True)
    except Exception as e:
        print(f"\n--- {u}\n  ERR {type(e).__name__} {str(e)[:100]}", flush=True); continue
    show(r, u)
    html = r.text
    t = re.search(r"<title[^>]*>(.*?)</title>", html, re.I | re.S)
    print("  title:", t.group(1).strip()[:100] if t else None, flush=True)
    scripts = [urljoin(str(r.url), s) for s in re.findall(r'<script[^>]+src=["\']([^"\']+)["\']', html, re.I)]
    print("  script srcs:", scripts[:20], flush=True)
    inline = re.findall(r"<script(?![^>]*src)[^>]*>(.*?)</script>", html, re.I | re.S)
    hits = []
    for blob in [html] + inline:
        for m in HINT.finditer(blob):
            s = max(0, m.start() - 50); hits.append(blob[s:m.end() + 90].replace("\n", " "))
    seen = set()
    for h_ in hits:
        k = h_[40:90]
        if k in seen: continue
        seen.add(k)
        if len(seen) <= 25: print("  HINT:", h_[:200], flush=True)
    iframes = re.findall(r"<iframe[^>]+>", html, re.I)
    print("  iframes:", iframes[:5], flush=True)
