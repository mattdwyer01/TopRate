"""
toprate_field_discovery.py
---------------------------
Read-only diagnostic: dumps every field TopRate's runner __data.json
payload actually carries, not just the subset toprate_json_capture.py
currently extracts (SECT_COLS + EXTRA_COLS + CORE_COLS).

WHY
  Before hunting for new toprate.au URLs/endpoints for age, sex, sire/dam,
  and gelding status, check whether the endpoint we ALREADY hit
  (/runners/{run_id}/__data.json) already carries them. TopRate's own UI
  shows breeding, foaled date, and an age/sex column on the runner page,
  so there is a good chance this same payload already has it under a key
  the current extractor just never looks at.

  Walks the deref'd runnerDetail structure a few levels deep (top level,
  plus one level into any nested dict/list) and prints every key found,
  flagging ones that look relevant to the gap list from a keyword match.
  Makes no assumption about the shape - if the interesting fields turn
  out to be nested (e.g. under a "horse" or "breeding" sub-object) this
  will still surface them.

USAGE
  python toprate_field_discovery.py <run_id>

  Uses the same auth as toprate_json_capture.py (toprate_daily.login()),
  so it needs to run wherever that login already works. Prints only
  field NAMES and VALUES from the runner payload, nothing from the auth
  layer itself.

NO EM DASHES policy: hyphens only in this file.
"""

import re
import sys

import toprate_json_capture as tjc

_INTERESTING = re.compile(
    r"age|sex|sire|dam\b|pedigree|breed|colour|color|coat|country|"
    r"foal|born|gelding|gelded|nation|origin",
    re.IGNORECASE,
)


def _fetch_raw(run_id):
    """Fetch one runner page and return (rd, deref) with NO field
    filtering, unlike tjc.fetch_runner which only returns the already
    -extracted subset. Reuses tjc's auth, URL pattern, and parse/redirect
    /login-bounce handling by calling the same low-level pieces."""
    url = (f"{tjc.WEB_BASE}/runners/{run_id}/__data.json"
           f"?x-sveltekit-invalidated=0001")
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
        parsed = tjc._parse_data_json(payload)
        if parsed == "EMPTY":
            return "EMPTY", None
        if parsed is None:
            print("  could not parse runnerDetail out of the payload")
            return None, None
        return parsed  # (rd, deref)
    return None, None


def _describe(v):
    if isinstance(v, (str, int, float, bool)) or v is None:
        return repr(v)
    if isinstance(v, list):
        return f"<list, {len(v)} items>"
    if isinstance(v, dict):
        return f"<dict, keys={list(v.keys())[:12]}>"
    return f"<{type(v).__name__}>"


def _walk(label, obj, deref, depth, seen):
    """Print every key at this level; recurse one level into nested
    dicts/lists so fields nested under e.g. rd['horse'] or rd['breeding']
    still surface. `seen` guards against re-descending into the same
    pointer twice (the payload is a shared, de-duplicated node array)."""
    resolved = deref(obj)
    if id(resolved) in seen or depth > 2:
        return
    seen.add(id(resolved))

    if isinstance(resolved, dict):
        for k, v in resolved.items():
            rv = deref(v)
            flag = "  <-- LOOK AT THIS" if _INTERESTING.search(str(k)) else ""
            print(f"  {label}.{k:28s} = {_describe(rv)}{flag}")
            if isinstance(rv, (dict, list)):
                _walk(f"{label}.{k}", v, deref, depth + 1, seen)
    elif isinstance(resolved, list):
        for i, v in enumerate(resolved[:3]):  # first few entries only
            _walk(f"{label}[{i}]", v, deref, depth + 1, seen)


if __name__ == "__main__":
    if len(sys.argv) < 2:
        sys.exit("Usage: python toprate_field_discovery.py <run_id>")
    rid = sys.argv[1]
    print(f"Fetching runner page {rid} for a full field dump...\n")
    rd, deref = _fetch_raw(rid)
    if rd == "EMPTY":
        sys.exit("Result: EMPTY - runnerDetail null (runner not served, "
                  "try a different/current run_id).")
    if rd is None:
        sys.exit("Result: hard failure, see message above.")

    print("=" * 70)
    print("TOP-LEVEL runnerDetail keys (fields matching the gap-list "
          "keywords are flagged):")
    print("=" * 70)
    seen = set()
    for k, v in rd.items():
        rv = deref(v)
        flag = "  <-- LOOK AT THIS" if _INTERESTING.search(str(k)) else ""
        print(f"  rd.{k:28s} = {_describe(rv)}{flag}")
    print()

    form = deref(rd.get("form"))
    if isinstance(form, list) and form:
        print("=" * 70)
        print("First FORM ENTRY keys (per-run fields, same treatment):")
        print("=" * 70)
        fe = deref(form[0])
        if isinstance(fe, dict):
            for k, v in fe.items():
                rv = deref(v)
                flag = "  <-- LOOK AT THIS" if _INTERESTING.search(str(k)) else ""
                print(f"  form[0].{k:24s} = {_describe(rv)}{flag}")
        print()

    print("=" * 70)
    print("Recursive scan of any nested dict/list values (depth 2), "
          "looking specifically for age/sex/sire/dam/gelding/breeding "
          "fields that might live under a sub-object rather than flat "
          "on runnerDetail:")
    print("=" * 70)
    for k, v in rd.items():
        rv = deref(v)
        if isinstance(rv, (dict, list)):
            _walk(f"rd.{k}", v, deref, 1, seen)
