"""
wpr_form_history_dedup_cleanup.py - ONE-TIME cleanup for the dedup-key bug
fixed in toprate_daily.py's flush_wpr_form_history() (Sep 2026).

WHY THIS EXISTS
  The file's dedup key used to include formNumber, on the assumption that
  it was a stable "which run number in this horse's career" index. It
  isn't: formNumber is relative to whatever race triggered the capture, so
  the SAME physical (horse, date) run gets a different formNumber on every
  re-scrape - confirmed directly, the same run appeared with formNumber 2,
  3 and 4 across three rows captured on the same scrape_date. With
  formNumber in the key, the dedup this file's docstring always promised
  never actually happened: 448,908 / 613,477 rows (73%) turned out to be
  duplicate captures of the same (horse, date) run, 80% of those groups
  with a genuinely different `wpr` value between copies (not just
  cosmetic differences in the enrichment columns).

  Every own-history ADJ_TERM (own_distance, own_going, own_first_up,
  own_trend, own_long_spell) and the base signals (ewm5, career_avg,
  best3) are computed by averaging over a horse's own row series from
  this file - a horse's older runs being silently double/triple-counted
  (more so the more times it has raced since, since each re-scrape
  re-duplicates its WHOLE history) is a systematic bias, not cosmetic
  bloat. This collapses the existing file down to the correct
  (dedup_key, date) key ONE TIME; toprate_daily.py's own
  flush_wpr_form_history() now maintains that key going forward.

METHOD: identical tie-break logic to flush_wpr_form_history() itself
(enriched rows - those with sect_i_early populated - sort after thin
rows, scrape_date as the tiebreaker among same-enrichment-status rows,
keep='last') so this is a mechanical application of the SAME rule the
live pipeline already uses, not a new policy.

USAGE
  python wpr_form_history_dedup_cleanup.py            # report only, no write
  python wpr_form_history_dedup_cleanup.py --write     # overwrite the CSV

NO EM DASHES policy: hyphens only in this file.
"""
import argparse

import pandas as pd

FORM_CSV = "wpr_form_history.csv.gz"


def run(write=False):
    fh = pd.read_csv(FORM_CSV, low_memory=False, dtype={"run_id": str, "horse_id": str})
    before = len(fh)
    print(f"loaded {before:,} rows")

    dedup_key = fh["horse_id"].astype(str)
    blank = dedup_key.isin(["", "nan", "None"])
    dedup_key = dedup_key.where(~blank, fh["horse"].astype(str))
    fh["_dedup"] = dedup_key

    dup_mask = fh.duplicated(subset=["_dedup", "date"], keep=False)
    n_dup_rows = int(dup_mask.sum())
    n_groups = fh[dup_mask].groupby(["_dedup", "date"]).ngroups
    print(f"rows involved in a (dedup_key, date) collision: {n_dup_rows:,} across {n_groups:,} groups")

    if "sect_i_early" in fh.columns:
        has_sect = fh["sect_i_early"].notna().astype(int)
    else:
        has_sect = 0
    fh["_enriched"] = has_sect
    sort_cols = ["_enriched"]
    if "scrape_date" in fh.columns:
        sort_cols = ["_enriched", "scrape_date"]
    fh = fh.sort_values(sort_cols, kind="stable")
    cleaned = fh.drop_duplicates(subset=["_dedup", "date"], keep="last").reset_index(drop=True)
    cleaned = cleaned.drop(columns=["_dedup", "_enriched"])

    after = len(cleaned)
    print(f"\nrows before: {before:,}")
    print(f"rows after:  {after:,}  (removed {before - after:,}, {(before - after) / before * 100:.1f}%)")

    remaining_dup = cleaned.assign(
        _dedup=cleaned["horse_id"].astype(str).where(
            ~cleaned["horse_id"].astype(str).isin(["", "nan", "None"]), cleaned["horse"].astype(str))
    ).duplicated(subset=["_dedup", "date"]).sum()
    print(f"remaining (dedup_key, date) duplicates after cleanup: {remaining_dup:,} (should be 0)")

    if write:
        cleaned.to_csv(FORM_CSV, index=False)
        print(f"\nwrote {after:,} rows -> {FORM_CSV}")
    else:
        print("\n--report only-- pass --write to overwrite the file")


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--write", action="store_true", help="overwrite wpr_form_history.csv.gz")
    args = ap.parse_args()
    run(write=args.write)
