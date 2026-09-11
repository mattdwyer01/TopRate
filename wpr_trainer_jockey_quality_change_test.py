"""
wpr_trainer_jockey_quality_change_test.py - tests a QUALITY-AWARE
redesign of trainer_change (and the same idea applied fresh to jockey
changes), per explicit user request (Sep 2026, see chat): instead of a
binary "did the trainer change" flag (which the earlier trainer_change_
rebase_test.py found gives a positive bonus for "no change" that isn't
really about trainer identity - see that script's own findings), use
the ACTUAL QUALITY DELTA - new trainer's trailing win% minus the old
trainer's trailing win% at the time of the switch. A move to a better
trainer should predict a bonus; a move to a worse one, a penalty. A
horse that keeps the same trainer gets delta 0 (neutral), not the old
design's unexplained "same trainer = positive" quirk.

LEAK-FREE POINT-IN-TIME LOOKUP: trainer_win_pct_365d/jockey_win_pct_90d
are only ever captured in toprate_runners.csv (today's-races snapshots,
~20% overall historical coverage, concentrated in the recent window -
same limitation trainer_merit/jockey_merit already have, see
_fit_coverage_aware_trn). Built here as a (trainer/jockey, date) ->
win% lookup from EVERY row in toprate_runners.csv (not just one horse -
many horses share a trainer, so the same trainer's win% gets observed
on many different days), then pd.merge_asof'd backward (largest
available date <= the target date, never a later one) to find the OLD
trainer/jockey's win% as of the horse's LAST run under them - strictly
backward-looking, no future information about that trainer's later
form can leak in.

SCOPE: like trainer_merit/jockey_merit, this is only testable within
toprate_runners.csv's own coverage window - the full 10-year set can't
be used (wpr_nett-style problem, see wpr_alpha_reopt_for_ewm7_test.py's
own docstring for the same class of limitation). Uses the SAME H1/H2
covered-subset split trainer_merit/jockey_merit's own validation used
(wpr_adj_term_ablation_and_stability.py).

NO EM DASHES policy: hyphens only in this file.
"""
import pandas as pd
import numpy as np

import wpr_projection as wp

FORM_HISTORY_CSV = "wpr_form_history.csv.gz"
RUNNERS_CSV = "toprate_runners.csv"


def build_quality_lookup(col):
    """(entity_lc, date) -> win% observations from EVERY row of
    toprate_runners.csv, deduped to one row per (entity, date) (same
    value repeats across every horse that entity had running that day -
    keep any one). Returns a DataFrame sorted by entity then date, ready
    for merge_asof."""
    tr = pd.read_csv(RUNNERS_CSV, low_memory=False,
                     usecols=["trainer", "jockey", "date", col])
    entity_col = "trainer" if col == "trainer_win_pct_365d" else "jockey"
    tr = tr.rename(columns={entity_col: "entity"})
    tr["entity_lc"] = tr["entity"].astype(str).str.strip().str.lower()
    tr["date"] = pd.to_datetime(tr["date"], errors="coerce")
    tr = tr.dropna(subset=["date", col, "entity_lc"])
    tr = tr.drop_duplicates(subset=["entity_lc", "date"], keep="first")
    tr = tr.sort_values(["entity_lc", "date"])[["entity_lc", "date", col]]
    return tr.rename(columns={col: "quality"})


def asof_lookup(targets, lookup):
    """targets: DataFrame with entity_lc, date columns (the OLD
    trainer/jockey and the date of the horse's last run under them).
    Returns quality as of the closest available date <= target date,
    per entity - leak-free (never looks past the target date)."""
    targets = targets.reset_index(drop=True)
    targets["_row"] = targets.index
    t = targets.dropna(subset=["entity_lc", "date"]).sort_values(["entity_lc", "date"])
    merged = pd.merge_asof(
        t, lookup, on="date", by="entity_lc", direction="backward",
    )
    out = pd.Series(np.nan, index=targets.index)
    out.loc[merged["_row"]] = merged["quality"].to_numpy()
    return out


def run():
    print("Building training frame (wpr_form_history.csv.gz, same source trainer_merit/jockey_merit use)...")
    D = wp.build_training_frame(FORM_HISTORY_CSV, verbose=True)

    print("\nMerging today's (new) trainer/jockey win% via the existing coverage-aware loader...")
    name_map, tj_lookup = wp._load_trainer_jockey_by_horse_date(FORM_HISTORY_CSV)
    D["horse_name"] = D["horse_id"].map(name_map)
    D["date_str"] = pd.to_datetime(D["date"]).dt.strftime("%Y-%m-%d")
    tj = D.apply(lambda r: tj_lookup.get((r["horse_name"], r["date_str"]), (np.nan, np.nan)), axis=1)
    D["trainer_win_pct_365d"] = [x[0] for x in tj]
    D["jockey_win_pct_90d"] = [x[1] for x in tj]
    print(f"  trainer_win_pct_365d coverage: {D['trainer_win_pct_365d'].notna().mean()*100:.1f}%  "
          f"jockey_win_pct_90d coverage: {D['jockey_win_pct_90d'].notna().mean()*100:.1f}%")

    print("\nComputing prior trainer/jockey (own-history, leak-free) and their last-run date...")
    fh = pd.read_csv(FORM_HISTORY_CSV, usecols=["horse_id", "date", "trainer", "jockey"], low_memory=False)
    fh["date"] = pd.to_datetime(fh["date"], errors="coerce")
    fh = fh.dropna(subset=["date"]).sort_values(["horse_id", "date"])
    fh = fh.drop_duplicates(subset=["horse_id", "date"], keep="last")
    fh["prior_trainer"] = fh.groupby("horse_id")["trainer"].shift(1)
    fh["prior_jockey"] = fh.groupby("horse_id")["jockey"].shift(1)
    fh["prior_date"] = fh.groupby("horse_id")["date"].shift(1)

    D = D.merge(
        fh[["horse_id", "date", "prior_trainer", "prior_jockey", "prior_date"]],
        on=["horse_id", "date"], how="left")

    # D itself may not carry today's trainer/jockey name directly (it is a
    # per-horse feature frame, not the raw form history) - re-merge from fh
    # for TODAY's row too, matching D's own (horse_id, date) key.
    cur = fh[["horse_id", "date", "trainer", "jockey"]].rename(
        columns={"trainer": "cur_trainer_name", "jockey": "cur_jockey_name"})
    D = D.merge(cur, on=["horse_id", "date"], how="left")
    D["trainer_change_raw"] = (
        (D["cur_trainer_name"] != D["prior_trainer"]) & D["prior_trainer"].notna()).astype(float)
    D["jockey_change_raw"] = (
        (D["cur_jockey_name"] != D["prior_jockey"]) & D["prior_jockey"].notna()).astype(float)

    print("\nBuilding leak-free (trainer/jockey, date) -> win% lookups from toprate_runners.csv...")
    trainer_lookup = build_quality_lookup("trainer_win_pct_365d")
    jockey_lookup = build_quality_lookup("jockey_win_pct_90d")
    print(f"  trainer_lookup: {len(trainer_lookup):,} (entity, date) rows, "
          f"{trainer_lookup['entity_lc'].nunique():,} trainers")
    print(f"  jockey_lookup: {len(jockey_lookup):,} (entity, date) rows, "
          f"{jockey_lookup['entity_lc'].nunique():,} jockeys")

    print("\nLooking up OLD trainer/jockey quality as of their last run with this horse (leak-free asof)...")
    old_trainer_targets = pd.DataFrame({
        "entity_lc": D["prior_trainer"].astype(str).str.strip().str.lower(),
        "date": D["prior_date"],
    })
    old_trainer_targets.loc[D["prior_trainer"].isna(), "entity_lc"] = np.nan
    D["old_trainer_quality"] = asof_lookup(old_trainer_targets, trainer_lookup)

    old_jockey_targets = pd.DataFrame({
        "entity_lc": D["prior_jockey"].astype(str).str.strip().str.lower(),
        "date": D["prior_date"],
    })
    old_jockey_targets.loc[D["prior_jockey"].isna(), "entity_lc"] = np.nan
    D["old_jockey_quality"] = asof_lookup(old_jockey_targets, jockey_lookup)

    D["trainer_quality_delta"] = D["trainer_win_pct_365d"] - D["old_trainer_quality"]
    D["jockey_quality_delta"] = D["jockey_win_pct_90d"] - D["old_jockey_quality"]

    print(f"\n  trainer_quality_delta coverage (of trainer_change==1 rows): "
          f"{D.loc[D['trainer_change_raw']==1, 'trainer_quality_delta'].notna().mean()*100:.1f}%")
    print(f"  jockey_quality_delta coverage (of jockey_change==1 rows): "
          f"{D.loc[D['jockey_change_raw']==1, 'jockey_quality_delta'].notna().mean()*100:.1f}%")
    print(f"\n  trainer_quality_delta distribution (changed rows only):")
    print(D.loc[D["trainer_change_raw"]==1, "trainer_quality_delta"].describe())

    D.to_pickle("/tmp/claude-0/-home-user-TopRate/95a262de-71bd-5daf-b05e-b7e3031f09dd/scratchpad/quality_delta_D.pkl")
    print("\nSaved D -> scratchpad/quality_delta_D.pkl for the next step (MAE test).")
    print("Done.")


if __name__ == "__main__":
    run()
