"""
probe_new_toprate_fields.py - one-off diagnostic, NOT wired into the daily
pipeline.

WHY
  toprate.au shipped an upgrade (23 June 2026) adding an Official Handicap
  Rating (OHR) column and a new "Form Factor" model (Rank + Score, computed
  WITHOUT market price - a genuinely independent pre-race signal) to the
  runner page, plus a Nominations & Weights early-form view. This pipeline
  predates that upgrade and has never looked for these fields.

  toprate_json_capture.py already fetches the full runnerDetail object per
  runner (the __data.json endpoint) but only extracts a fixed, known list
  of keys (SECT_MAP + EXTRA_COLS) - anything TopRate added since is fetched
  over the wire and then silently discarded. This script fetches ONE
  runner and prints EVERY key it actually finds, so we can see by
  inspection whether ohr / formFactor* are already present (and under
  what name), or whether they need a different endpoint entirely.

USAGE (run locally, where TOPRATE_EMAIL/TOPRATE_PASSWORD are set)
  python probe_new_toprate_fields.py --run-id <a current run_id>

  Pick a run_id from a recent row of toprate_runners.csv, e.g.:
    python -c "import pandas as pd; d=pd.read_csv('toprate_runners.csv', dtype=str); print(d.tail(1)['run_id'].iloc[0])"

WHAT IT PRINTS
  - Every top-level key on runnerDetail, with a short repr of its value.
  - Every key on the first entry of runnerDetail['form'] (one past run),
    same treatment.
  - A highlighted "candidate matches" section: any key whose name suggests
    ohr / handicap / form factor / nomination, wherever found.

Read-only. Makes exactly one (or a couple, on redirect-follow) GET request
against the __data.json route already used by the daily pipeline - no
different from a normal page load. Does not write to any CSV or the
dashboard.

NO EM DASHES policy: hyphens only in this file.
"""
import argparse
import json
import sys

import toprate_json_capture as cap


_CANDIDATE_TERMS = ("ohr", "handicap", "formfactor", "form_factor", "pfm",
                    "official", "nomination", "weight")


def _walk(obj, deref, path, out, depth=0, max_depth=4):
    """Depth-limited walk of a deref'd structure, collecting (path, value)
    pairs for scalar/short values. Keeps output readable on a big object."""
    if depth > max_depth:
        return
    val = deref(obj)
    if isinstance(val, dict):
        for k, v in val.items():
            _walk(v, deref, f"{path}.{k}", out, depth + 1, max_depth)
    elif isinstance(val, list):
        if len(val) <= 3:
            for i, v in enumerate(val):
                _walk(v, deref, f"{path}[{i}]", out, depth + 1, max_depth)
        else:
            out.append((path, f"<list of {len(val)}>"))
    else:
        out.append((path, val))


def _probe_list_field(key, val, deref, max_scan=40):
    """_walk() only descends into lists of length <=3 (to keep general
    output readable) - a per-runner list like raceFields has one entry per
    horse, so it was NEVER actually looked inside, and any OHR/Form Factor
    living there would silently show up as "(none found)". This dumps
    EVERY key of the first entry (so you can see the shape), then scans up
    to max_scan entries for candidate-term matches specifically."""
    lst = deref(val)
    if not isinstance(lst, list) or not lst:
        return
    print(f"\n{'=' * 70}")
    print(f"{key}: list of {len(lst)} - first entry, all keys")
    print("=" * 70)
    first = deref(lst[0])
    if isinstance(first, dict):
        for k in sorted(first.keys()):
            v = deref(first[k])
            vr = repr(v)
            if len(vr) > 100:
                vr = vr[:97] + "..."
            print(f"  {k:24s} = {vr}")
    else:
        print(f"  (entry is not a dict: {type(first).__name__}) {first!r}"[:300])

    print(f"\n{key}: candidate matches across all {min(len(lst), max_scan)} entries scanned")
    found = []
    for i, item in enumerate(lst[:max_scan]):
        d = deref(item)
        if not isinstance(d, dict):
            continue
        for k, v in d.items():
            if any(t in k.lower() for t in _CANDIDATE_TERMS):
                found.append((i, k, deref(v)))
    if found:
        for i, k, v in found:
            print(f"  [{i}].{k} = {v!r}")
    else:
        print("  (none found)")


def probe_page(page_path):
    """Generic SvelteKit __data.json prober for any page (not just the
    runner page, which requires a 'runnerDetail' root key). page_path is
    the URL path after the domain, e.g. 'races/1757148/assess' - this is
    where OHR is confirmed to be visible (the Assess Screen)."""
    page_path = page_path.strip("/")
    url = f"{cap.WEB_BASE}/{page_path}/__data.json?x-sveltekit-invalidated=0001"
    headers, cookies = cap._auth_bits()
    resp = __import__("requests").get(
        url, headers=headers, cookies=cookies,
        verify=cap.VERIFY_SSL, timeout=cap.TIMEOUT, allow_redirects=False)
    print(f"HTTP {resp.status_code} for {url}")
    if resp.status_code in (301, 302, 303, 307, 308):
        print(f"Redirected to: {resp.headers.get('location')}")
        print("(likely an auth bounce - check TOPRATE_EMAIL/TOPRATE_PASSWORD)")
        return
    payload = resp.json()
    if isinstance(payload, dict) and payload.get("type") == "redirect":
        print(f"App-level redirect to: {payload.get('location')!r}")
        return
    nodes = payload.get("nodes") if isinstance(payload, dict) else None
    if not isinstance(nodes, list):
        print("No 'nodes' list in payload. Top-level keys:",
              list(payload.keys()) if isinstance(payload, dict) else type(payload))
        return

    print(f"\n{'=' * 70}\n{len(nodes)} data node(s)\n{'=' * 70}")
    all_pairs = []
    for i, n in enumerate(nodes):
        if not (isinstance(n, dict) and isinstance(n.get("data"), list)):
            print(f"node[{i}]: no data list (type {type(n).__name__})")
            continue
        data = n["data"]
        if not data:
            print(f"node[{i}]: empty data array")
            continue
        root = data[0]

        def deref(p, _data=data):
            return _data[p] if isinstance(p, int) else p

        if isinstance(root, dict):
            print(f"node[{i}] root keys: {list(root.keys())}")
            _walk(root, deref, f"node[{i}]", all_pairs, max_depth=4)
            # Any top-level value that's a list of more than 3 items (e.g.
            # raceFields, one entry per runner) never got walked above -
            # dump it specifically so per-runner fields like OHR/Form
            # Factor aren't silently missed.
            for k, v in root.items():
                dv = deref(v)
                if isinstance(dv, list) and len(dv) > 3:
                    _probe_list_field(f"node[{i}].{k}", v, deref)
        else:
            print(f"node[{i}] root: {root!r}"[:200])

    print(f"\n{'=' * 70}")
    print(f"CANDIDATE MATCHES (key name contains any of {_CANDIDATE_TERMS})")
    print("=" * 70)
    found = [(p, v) for p, v in all_pairs
             if any(t in p.rsplit(".", 1)[-1].split("[")[0].lower()
                    for t in _CANDIDATE_TERMS)]
    if found:
        for path, val in found:
            print(f"  {path} = {val!r}")
    else:
        print("  (none found)")


def probe(run_id):
    url = (f"{cap.WEB_BASE}/runners/{run_id}/__data.json"
           f"?x-sveltekit-invalidated=0001")
    headers, cookies = cap._auth_bits()
    resp = __import__("requests").get(
        url, headers=headers, cookies=cookies,
        verify=cap.VERIFY_SSL, timeout=cap.TIMEOUT, allow_redirects=False)
    print(f"HTTP {resp.status_code} for {url}")
    if resp.status_code in (301, 302, 303, 307, 308):
        print(f"Redirected to: {resp.headers.get('location')}")
        print("(likely an auth bounce - check TOPRATE_EMAIL/TOPRATE_PASSWORD)")
        return
    payload = resp.json()
    parsed = cap._parse_data_json(payload)
    if parsed in (None, "EMPTY"):
        print(f"Could not parse runnerDetail (parsed={parsed!r}).")
        print("Top-level payload keys:", list(payload.keys())
              if isinstance(payload, dict) else type(payload))
        return
    rd, deref = parsed

    print("\n" + "=" * 70)
    print("runnerDetail top-level keys")
    print("=" * 70)
    for k in sorted(rd.keys()):
        v = deref(rd[k])
        vr = repr(v)
        if len(vr) > 80:
            vr = vr[:77] + "..."
        print(f"  {k:30s} = {vr}")

    form = deref(rd.get("form"))
    if isinstance(form, list):
        print(f"\nform array length (total past runs the API returns): {len(form)}")
        dates_seen = sorted({str(deref(f).get("date")) for f in form
                             if isinstance(deref(f), dict)})
        print(f"dates covered: {dates_seen[0]} .. {dates_seen[-1]}"
              if dates_seen else "no dates found")
        for f in form:
            fd = deref(f)
            if isinstance(fd, dict):
                print(f"  {deref(fd.get('date'))}  {deref(fd.get('track'))}  "
                      f"wpr={deref(fd.get('wpr'))}")
    if isinstance(form, list) and form:
        print("\n" + "=" * 70)
        print("First form-run entry - all keys")
        print("=" * 70)
        first = deref(form[0])
        if isinstance(first, dict):
            for k in sorted(first.keys()):
                v = deref(first[k])
                vr = repr(v)
                if len(vr) > 80:
                    vr = vr[:77] + "..."
                print(f"  {k:30s} = {vr}")
        else:
            print("  (first form entry is not a dict:", type(first).__name__, ")")

    print("\n" + "=" * 70)
    print(f"CANDIDATE MATCHES (key name contains any of {_CANDIDATE_TERMS})")
    print("=" * 70)
    found = []
    pairs = []
    _walk(rd, deref, "runnerDetail", pairs, max_depth=3)
    for path, val in pairs:
        key_part = path.rsplit(".", 1)[-1].split("[")[0].lower()
        if any(t in key_part for t in _CANDIDATE_TERMS):
            found.append((path, val))
    if found:
        for path, val in found:
            print(f"  {path} = {val!r}")
    else:
        print("  (none found within runnerDetail - OHR/Form Factor may live "
              "on a different endpoint, e.g. the race/nominations page "
              "rather than the runner page)")


def _walk_json(obj, path, out, depth=0, max_depth=5):
    """Same idea as _walk() but for plain (non-deref'd) JSON, used for the
    get_race_detail RPC response."""
    if depth > max_depth:
        return
    if isinstance(obj, dict):
        for k, v in obj.items():
            _walk_json(v, f"{path}.{k}", out, depth + 1, max_depth)
    elif isinstance(obj, list):
        if len(obj) <= 3:
            for i, v in enumerate(obj):
                _walk_json(v, f"{path}[{i}]", out, depth + 1, max_depth)
        else:
            out.append((path, f"<list of {len(obj)}>"))
    else:
        out.append((path, obj))


def _dump_item(item, label):
    print(f"\n{label} - full key/value dump")
    if isinstance(item, dict):
        for k in sorted(item.keys()):
            v = item[k]
            vr = repr(v)
            if len(vr) > 100:
                vr = vr[:97] + "..."
            print(f"  {k:22s} = {vr}")
    else:
        print(f"  (not a dict: {type(item).__name__}) {item!r}"[:300])


def probe_race(race_id):
    """Check get_race_detail (Field View), plus get_race_stats/
    get_race_cache/get_race_wpr_chart - already called by the daily
    pipeline for other purposes, so cheap to check here too - for OHR /
    Form Factor, which the announcement describes as shown per-race
    (Field View, WPR Chart, Assess Screen), not per-runner."""
    import toprate_daily as td
    jwt = td.login()

    data = td.api_race_detail(jwt, race_id)
    print(f"\n{'=' * 70}")
    print(f"get_race_detail(rc_id={race_id}) - top-level shape")
    print("=" * 70)
    if isinstance(data, dict):
        print("  top-level keys:", list(data.keys()))
    elif isinstance(data, list):
        print(f"  top-level: list of {len(data)}")
        if data:
            _dump_item(data[0], "item[0]")

    print(f"\n{'=' * 70}")
    print(f"CANDIDATE MATCHES (key name contains any of {_CANDIDATE_TERMS})")
    print("=" * 70)
    pairs = []
    _walk_json(data, "race_detail", pairs, max_depth=5)
    found = [(p, v) for p, v in pairs
             if any(t in p.rsplit(".", 1)[-1].split("[")[0].lower()
                    for t in _CANDIDATE_TERMS)]
    if found:
        for path, val in found:
            print(f"  {path} = {val!r}")
    else:
        print("  (none found)")

    for rpc_name, rpc_fn in (
        ("get_race_stats", td.api_race_stats),
        ("get_race_cache (get_user_cache_race)", td.api_race_cache),
        ("get_race_wpr_chart", td.api_race_wpr),
    ):
        try:
            rdata = rpc_fn(jwt, race_id)
        except Exception as e:
            print(f"\n{rpc_name}: request failed ({e})")
            continue
        print(f"\n{'=' * 70}")
        print(f"{rpc_name}(rc_id={race_id}) - shape + candidate matches")
        print("=" * 70)
        if isinstance(rdata, dict):
            print("  top-level keys:", list(rdata.keys()))
        elif isinstance(rdata, list):
            print(f"  top-level: list of {len(rdata)}")
            if rdata:
                _dump_item(rdata[0], "item[0]")
        rpairs = []
        _walk_json(rdata, rpc_name, rpairs, max_depth=5)
        rfound = [(p, v) for p, v in rpairs
                  if any(t in p.rsplit(".", 1)[-1].split("[")[0].lower()
                         for t in _CANDIDATE_TERMS)]
        if rfound:
            for path, val in rfound:
                print(f"  MATCH: {path} = {val!r}")
        else:
            print("  (no candidate matches)")


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--run-id", help="a real run_id, e.g. from toprate_runners.csv")
    ap.add_argument("--race-id",
                    help="a real race_id - checks get_race_detail (the Field "
                         "View RPC) instead of the runner page")
    ap.add_argument("--page",
                    help="a page path to probe generically via its "
                         "__data.json, e.g. 'races/1757148/assess' (the "
                         "Assess Screen, where OHR is visible)")
    args = ap.parse_args()
    if not args.run_id and not args.race_id and not args.page:
        ap.error("pass --run-id, --race-id, and/or --page")
    if args.run_id:
        probe(args.run_id)
    if args.race_id:
        probe_race(args.race_id)
    if args.page:
        probe_page(args.page)


if __name__ == "__main__":
    main()
