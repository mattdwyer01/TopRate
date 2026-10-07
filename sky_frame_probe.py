"""Read-only: can Sky Racing / TAB live-vision pages be embedded in an <iframe> on another site?
Plain GETs of public pages from the AU runner. For each page prints status, final URL, title and the
headers that decide framing (X-Frame-Options, Content-Security-Policy frame-ancestors), plus links that
look like live vision. Sends no credentials, writes nothing."""
import re
from urllib.parse import urljoin, urlparse
from curl_cffi import requests as cr

SEEDS = [
    "https://www.skyracing.com.au/",
    "https://www.skyracing.com.au/live",
    "https://www.skyracing.com.au/live-vision",
    "https://www.tab.com.au/",
    "https://www.tab.com.au/racing",
    "https://www.tab.com.au/racing/live-vision",
    "https://www.tab.com.au/live-vision",
]
HREF = re.compile(r'(?:href|src)=["\']([^"\']+)["\']', re.I)
LIVEISH = re.compile(r"live|vision|stream|watch|embed|player|video|broadcast", re.I)

def fetch(url):
    try:
        r = cr.get(url, impersonate="chrome", timeout=25, allow_redirects=True)
    except Exception as e:
        print(f"\n--- {url}\n  ERR {type(e).__name__}: {str(e)[:120]}", flush=True)
        return None
    h = {k.lower(): v for k, v in r.headers.items()}
    csp = h.get("content-security-policy", "")
    fa = re.search(r"frame-ancestors[^;]*", csp, re.I)
    title = re.search(r"<title[^>]*>(.*?)</title>", r.text[:200000], re.I | re.S)
    print(f"\n--- {url}\n  status={r.status_code} final={r.url}", flush=True)
    print(f"  title={title.group(1).strip()[:90] if title else None}", flush=True)
    print(f"  x-frame-options={h.get('x-frame-options')}  csp-frame-ancestors={fa.group(0) if fa else None}", flush=True)
    print(f"  server={h.get('server')} content-type={h.get('content-type')}", flush=True)
    return r

found = {}
for u in SEEDS:
    r = fetch(u)
    if r is None or r.status_code != 200 or "html" not in (r.headers.get("content-type") or ""):
        continue
    host = urlparse(str(r.url)).netloc
    links = []
    for href in HREF.findall(r.text[:600000]):
        full = urljoin(str(r.url), href)
        if LIVEISH.search(full) and not re.search(r"\.(css|js|png|jpg|svg|ico|woff2?)(\?|$)", full):
            links.append(full)
    uniq = list(dict.fromkeys(links))
    print(f"  {len(uniq)} live-ish links; first 15:", flush=True)
    for l in uniq[:15]:
        print("    ", l[:160], flush=True)
        if urlparse(l).netloc == host:
            found[l] = 1

print("\n==== follow-up: same-host live-ish pages ====", flush=True)
for l in list(found)[:8]:
    fetch(l)
