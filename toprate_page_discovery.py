"""
toprate_page_discovery.py
--------------------------
Generic read-only diagnostic for ANY toprate.au SvelteKit __data.json
page, not just /runners/{id} (see toprate_field_discovery.py for that
one). Unlike that script, this one does NOT assume the root data key
(e.g. "runnerDetail") - it dumps whatever top-level key each data-bearing
node actually has, then recurses into it, so a page with an unknown
schema (meeting history, track history, etc.) can still be inspected
without guessing the shape in advance.

USAGE
  python toprate_page_discovery.py <path>

  <path> is anything after https://toprate.au/, e.g.:
    meetings/144507/history

  The x-sveltekit-invalidated query param and __data.json suffix are
  added automatically if not already present.

  Uses the same auth as toprate_json_capture.py (toprate_daily.login()).
  Prints only field NAMES and VALUES from the page payload, nothing
  from the auth layer itself - never pass a raw cookie/token to this
  script, it doesn't need one.

NO EM DASHES policy: hyphens only in this file.
"""

import re
import sys

import toprate_json_capture as tjc

_INTERESTING = re.compile(
    r"age|sex|sire|dam\b|pedigree|breed|colour|color|coat|country|"
    r"foal|born|gelding|gelded|nation|origin|rail|bias|shape|direction|"
    r"straight|surface|wfa|weightforage|scale|clockwise",
    re.IGNORECASE,
)


def _build_url(path):
    """Deliberately does NOT default-add x-sveltekit-invalidated like
    toprate_json_capture.py's runner fetch does. That param tells the
    server which layout segments the CLIENT already has cached from a
    prior page load ('0' = reuse cache, skip refetch), which is only
    true for a real browser mid-navigation. A cold one-shot script has
    no prior state, so forcing '0001' can make the server skip parent
    layout nodes entirely (e.g. a meeting's rail/going, which live in
    the /meetings/{id} layout, not the /history leaf) - exactly what
    happened on the first run of this script against a real page.
    Omitting the param outright asks for everything fresh. Pass it
    explicitly in <path> yourself (as a query string) to override."""
    path = path.strip().lstrip("/")
    if not path.startswith("http"):
        path = f"{tjc.WEB_BASE}/{path}"
    if "__data.json" not in path:
        path = path.rstrip("/") + "/__data.json"
    return path


def _fetch(url):
    for attempt in range(1, tjc.MAX_RETRIES + 1):
        headers, cookies = tjc._auth_bits()
        resp = tjc.requests.get(url, headers=headers, cookies=cookies,
                                 verify=tjc.VERIFY_SSL, timeout=tjc.TIMEOUT,
                                 allow_redirects=False)
        if resp.status_code in (301, 302, 303, 307, 308, 401):
            import toprate_daily as td
            td._SESSION_OBJ = None
            print(f"  attempt {attempt}: auth rejected, re-authenticating...")
            continue
        if resp.status_code != 200:
            print(f"  attempt {attempt}: HTTP {resp.status_code}")
            continue
        payload = resp.json()
        if isinstance(payload, dict) and payload.get("type") == "redirect":
            loc = payload.get("location") or ""
            redir = loc if loc.startswith("http") else f"{tjc.WEB_BASE}{loc}"
            if "__data.json" not in redir:
                redir = redir.rstrip("/") + "/__data.json"
            resp = tjc.requests.get(redir, headers=headers, cookies=cookies,
                                     verify=tjc.VERIFY_SSL, timeout=tjc.TIMEOUT,
                                     allow_redirects=False)
            payload = resp.json()
        if tjc._is_login_bounce(payload):
            import toprate_daily as td
            td._SESSION_OBJ = None
            print(f"  attempt {attempt}: login bounce, re-authenticating...")
            continue
        return payload
    return None


def _describe(v):
    if isinstance(v, (str, int, float, bool)) or v is None:
        return repr(v)
    if isinstance(v, list):
        return f"<list, {len(v)} items>"
    if isinstance(v, dict):
        return f"<dict, keys={list(v.keys())[:12]}>"
    return f"<{type(v).__name__}>"


def _walk(label, obj, deref, depth, seen, max_depth):
    resolved = deref(obj)
    if id(resolved) in seen or depth > max_depth:
        return
    seen.add(id(resolved))
    if isinstance(resolved, dict):
        for k, v in resolved.items():
            rv = deref(v)
            flag = "  <-- LOOK AT THIS" if _INTERESTING.search(str(k)) else ""
            print(f"  {label}.{k:28s} = {_describe(rv)}{flag}")
            if isinstance(rv, (dict, list)):
                _walk(f"{label}.{k}", v, deref, depth + 1, seen, max_depth)
    elif isinstance(resolved, list):
        for i, v in enumerate(resolved[:3]):
            _walk(f"{label}[{i}]", v, deref, depth + 1, seen, max_depth)


if __name__ == "__main__":
    if len(sys.argv) < 2:
        sys.exit("Usage: python toprate_page_discovery.py <path>\n"
                  "  e.g. python toprate_page_discovery.py meetings/144507/history")
    url = _build_url(sys.argv[1])
    print(f"Fetching {url} ...\n")
    payload = _fetch(url)
    if payload is None:
        sys.exit("Result: hard failure, see message above.")

    nodes = payload.get("nodes") if isinstance(payload, dict) else None
    if not isinstance(nodes, list):
        print("Payload has no 'nodes' list. Top-level keys:")
        print(f"  {list(payload.keys()) if isinstance(payload, dict) else type(payload)}")
        sys.exit(0)

    print(f"{len(nodes)} node(s) in the response.\n")
    for i, n in enumerate(nodes):
        if not (isinstance(n, dict) and isinstance(n.get("data"), list)):
            print(f"node[{i}]: not a data node ({type(n).__name__})")
            continue
        data = n["data"]
        root = data[0] if data else None
        if not isinstance(root, dict):
            print(f"node[{i}] data[0] is not a dict: {type(root).__name__}")
            continue

        def deref(p, _data=data):
            return _data[p] if isinstance(p, int) else p

        print("=" * 70)
        print(f"node[{i}] ROOT KEYS: {list(root.keys())}")
        print("=" * 70)
        seen = set()
        for k, v in root.items():
            rv = deref(v)
            flag = "  <-- LOOK AT THIS" if _INTERESTING.search(str(k)) else ""
            print(f"  {k:30s} = {_describe(rv)}{flag}")
        print()
        print(f"-- recursive scan of node[{i}] (depth 3) --")
        for k, v in root.items():
            rv = deref(v)
            if isinstance(rv, (dict, list)):
                # depth 0 here (not 1): the root-level container itself has
                # not been visited by _walk yet, only printed above, so it
                # must not be pre-marked seen or _walk bails immediately.
                _walk(k, v, deref, 0, seen, max_depth=6)
        print()
