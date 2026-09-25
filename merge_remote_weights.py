"""
merge_remote_weights.py -- keep TAB carried weights that are already on the remote when a data job commits
its own copy of toprate_runners.csv.

    python merge_remote_weights.py origin/main

Why: weight_carried is written only by the TAB poller (tab_fields.py, self-hosted runner). The GitHub-hosted
data jobs (daily.yml, toprate_daily.yml) load the CSV at the start of a long run and commit their whole copy at
the end, which wiped the weights the poller had pushed in the meantime (25 Sep 2026). Run just before staging
(and again after each reset onto the new remote tip): for every run_id whose weight_carried is set on REF, the
local file takes that value. Every other cell is left byte-for-byte as it was (all columns read as text).
Best-effort: any error is printed and the file is left untouched.
"""
import io
import subprocess
import sys

import pandas as pd

CSV = "toprate_runners.csv"


def main(ref):
    try:
        remote = subprocess.run(["git", "show", f"{ref}:{CSV}"], capture_output=True, check=True, timeout=120).stdout
        r = pd.read_csv(io.BytesIO(remote), dtype=str, keep_default_na=False, usecols=["run_id", "weight_carried"])
        r = r[r["weight_carried"].str.strip() != ""].drop_duplicates("run_id", keep="last")
        if r.empty:
            print("merge_remote_weights: no weights on", ref)
            return
        local = pd.read_csv(CSV, dtype=str, keep_default_na=False)
        if "weight_carried" not in local.columns:
            local["weight_carried"] = ""
        new = local["run_id"].map(r.set_index("run_id")["weight_carried"])
        change = new.notna() & (new != local["weight_carried"])
        if not change.any():
            print("merge_remote_weights: local file already has the remote weights")
            return
        local.loc[change, "weight_carried"] = new[change]
        local.to_csv(CSV, index=False)
        print(f"merge_remote_weights: kept {int(change.sum())} weights from {ref}")
    except Exception as e:
        print(f"merge_remote_weights skipped: {type(e).__name__}: {str(e)[:200]}")


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "origin/main")
