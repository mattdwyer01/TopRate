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


_CANDIDATE_TERMS = ("ohr", "handicap", "formfactor", "form_factor",
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


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--run-id", required=True,
                    help="a real run_id, e.g. from toprate_runners.csv")
    args = ap.parse_args()
    probe(args.run_id)


if __name__ == "__main__":
    main()
