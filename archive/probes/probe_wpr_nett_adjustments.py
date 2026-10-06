"""One-off check: does wpr_nett reflect PURE automated base ratings, or does
it include manually-saved Adj overrides from this TopRate account?

wpr_nett is built (build_wpr_lookup() in toprate_daily.py) from
get_user_cache_race()'s runAdjustments[].defaults.wprBase PLUS whichever
of adjustments.wprAdjustment / defaults.wprAdjustment is present. Base and
the account's own saved Adj get collapsed into one number before we ever
see it - this prints them separately so we can tell whether Adj has ever
actually been used on this account, and for what fraction of runners.

Usage: python probe_wpr_nett_adjustments.py --race-id 1757148

NO EM DASHES policy: hyphens only in this file.
"""
import argparse

import toprate_daily as td


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--race-id", required=True, type=int)
    args = ap.parse_args()

    jwt = td.login()
    cache = td.api_race_cache(jwt, args.race_id) or {}
    entries = cache.get("runAdjustments", [])
    print(f"{len(entries)} runAdjustments entries for race {args.race_id}\n")

    n_nonzero_user_adj = 0
    n_nonzero_default_adj = 0
    for e in entries:
        rid = e.get("runId")
        defaults = e.get("defaults", {}) or {}
        adjs = e.get("adjustments", {}) or {}
        base = defaults.get("wprBase")
        default_adj = defaults.get("wprAdjustment") or 0
        user_adj = adjs.get("wprAdjustment")
        effective_adj = user_adj if user_adj is not None else (default_adj or 0)
        nett = (base + effective_adj) if base is not None else None
        if user_adj not in (None, 0):
            n_nonzero_user_adj += 1
        if default_adj not in (None, 0):
            n_nonzero_default_adj += 1
        print(f"  runId={rid}  base={base}  default_adj={default_adj}  "
              f"user_adj={user_adj!r}  -> nett={nett}")
        # Also show any other keys in defaults/adjustments beyond wprBase/
        # wprAdjustment, in case there is more structure worth knowing about.
        extra_default_keys = [k for k in defaults if k != "wprBase" and k != "wprAdjustment"]
        extra_adj_keys = [k for k in adjs if k != "wprAdjustment"]
        if extra_default_keys:
            print(f"    other defaults keys: {extra_default_keys}")
        if extra_adj_keys:
            print(f"    other adjustments keys: {extra_adj_keys}")

    print(f"\n{n_nonzero_user_adj}/{len(entries)} runners have a non-zero "
          f"SAVED USER adjustment on this account")
    print(f"{n_nonzero_default_adj}/{len(entries)} runners have a non-zero "
          f"automated DEFAULT adjustment (not user-set)")


if __name__ == "__main__":
    main()
