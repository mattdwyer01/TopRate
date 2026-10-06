"""wpr_price_steam_feature_test.py - is price drift/"steam" (how much a
runner's price shortens or drifts between the first seen snapshot and its
final pre-race price) a genuinely new, usable signal? (item 5 of the "how
do we improve strike rate/AUC/Brier further" follow-up, Sep 2026 - the one
CLAUDE.md-sanctioned path beyond tuning existing features is "a
fundamentally new data source"). toprate_price_history.csv already
captures per-run_id price snapshots over time but nothing currently uses
it as a feature - this is the cheapest possible new-data-source test
(zero new collection needed).

Market steam is a well-known real signal in betting markets (informed/
"smart" money shortens a price before the crowd catches on) - if it adds
INCREMENTAL predictive value on top of wprp_proj (not already priced in
by the FINAL market price itself, which WPR is already compared against),
it could genuinely help. Tests two things:
  1. Does steam alone predict "won" better than chance (AUC)?
  2. Does combining wprp_blend_prob with steam (simple two-feature
     logistic regression, walk-forward split) beat wprp_blend_prob alone,
     and does it beat the market's own final price?

Uses toprate_runners.csv directly (real, live-served wprp_proj/wprp_blend_
prob, no build_training_frame() needed) joined to toprate_price_history.csv
by run_id (reliable here - it is toprate_runners.csv's own primary key,
not the corrupted form-history scrape-time stamp - see wpr_projection.py's
build_training_frame docstring for that unrelated bug).

USAGE
  python wpr_price_steam_feature_test.py

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd
from sklearn.linear_model import LogisticRegression
from sklearn.metrics import roc_auc_score

import toprate_daily as td

PRICE_HISTORY_CSV = "toprate_price_history.csv"


def brier(p, y):
    return float(np.mean((p - y) ** 2))


def run():
    print("Loading price history...")
    ph = pd.read_csv(PRICE_HISTORY_CSV, dtype={"run_id": str, "race_id": str})
    ph["snapshot_time"] = pd.to_datetime(ph["snapshot_time"], errors="coerce")
    ph = ph.dropna(subset=["run_id", "snapshot_time", "fixed_win_price"])
    ph = ph[ph["fixed_win_price"] > 1.0]

    print(f"  {len(ph):,} snapshots, {ph['run_id'].nunique():,} runners")
    ph_sorted = ph.sort_values(["run_id", "snapshot_time"])
    first = ph_sorted.groupby("run_id").first()["fixed_win_price"]
    last = ph_sorted.groupby("run_id").last()["fixed_win_price"]
    n_snaps = ph_sorted.groupby("run_id").size()
    steam = pd.DataFrame({"first_price": first, "last_price": last, "n_snapshots": n_snaps})
    steam["steam_pct"] = (steam["first_price"] - steam["last_price"]) / steam["first_price"]
    steam = steam[steam["n_snapshots"] >= 2]  # need at least 2 snapshots for real drift
    print(f"  {len(steam):,} runners with >=2 snapshots (real drift measurable)")

    print("Loading runners...")
    r = td.load_runners()
    r["date"] = pd.to_datetime(r["date"], errors="coerce")
    r["won"] = pd.to_numeric(r["won"], errors="coerce")
    r["resulted"] = pd.to_numeric(r["resulted"], errors="coerce")
    r["scratched"] = pd.to_numeric(r["scratched"], errors="coerce")
    r["wprp_proj"] = pd.to_numeric(r["wprp_proj"], errors="coerce")
    r["wprp_blend_prob"] = pd.to_numeric(r["wprp_blend_prob"], errors="coerce")
    r["_price"] = pd.to_numeric(r["fixed_win_price"], errors="coerce").combine_first(
        pd.to_numeric(r["starting_price_sp"], errors="coerce"))

    scoped = r[(r["resulted"] == 1) & (r["scratched"] != 1) &
               r["won"].notna() & r["wprp_proj"].notna() & r["wprp_blend_prob"].notna() &
               r["_price"].notna() & (r["_price"] > 1.0) & r["date"].notna()].copy()
    field_counts = scoped.groupby("race_id")["race_id"].transform("size")
    scoped = scoped[field_counts >= 4].copy()

    scoped = scoped.merge(steam[["steam_pct", "n_snapshots"]], left_on="run_id", right_index=True, how="inner")
    print(f"Merged: {len(scoped):,} runners with both WPR data and measurable price steam, "
          f"date range {scoped['date'].min().date()} to {scoped['date'].max().date()}")

    scoped["mkt_prob"] = (1.0 / scoped["_price"]) / scoped.groupby("race_id")["_price"].transform(
        lambda s: (1.0 / s).sum())

    print(f"\nsteam_pct summary (positive = price shortened/firmed since first seen):")
    print(scoped["steam_pct"].describe())

    auc_steam_alone = roc_auc_score(scoped["won"], scoped["steam_pct"])
    print(f"\nAUC, steam_pct alone (raw, not race-relative): {auc_steam_alone:.4f}  "
          f"(0.5 = no signal; note this is NOT race-normalised, unlike WPR/market probs)")

    scoped = scoped.sort_values("date")
    cut = scoped["date"].quantile(0.70)
    trn, tst = scoped[scoped["date"] < cut], scoped[scoped["date"] >= cut]
    print(f"\ntrain (< {cut.date()}): {len(trn):,} rows, {trn['race_id'].nunique():,} races")
    print(f"held-out: {len(tst):,} rows, {tst['race_id'].nunique():,} races")

    def eval_features(feat_cols, label):
        X_trn, y_trn = trn[feat_cols].to_numpy(), trn["won"].to_numpy()
        X_tst, y_tst = tst[feat_cols].to_numpy(), tst["won"].to_numpy()
        clf = LogisticRegression()
        clf.fit(X_trn, y_trn)
        p_tst = clf.predict_proba(X_tst)[:, 1]
        auc = roc_auc_score(y_tst, p_tst)
        br = brier(p_tst, y_tst)
        print(f"  {label:<40} held-out AUC={auc:.4f}  Brier={br:.5f}")
        return auc, br

    print(f"\n{'='*70}\nBenchmark comparison (all held-out, same rows)\n{'='*70}")
    auc_mkt = roc_auc_score(tst["won"], tst["mkt_prob"])
    br_mkt = brier(tst["mkt_prob"].to_numpy(), tst["won"].to_numpy())
    print(f"  {'Market implied prob (benchmark)':<40} held-out AUC={auc_mkt:.4f}  Brier={br_mkt:.5f}")
    eval_features(["wprp_blend_prob"], "WPR alone (logistic-recalibrated)")
    eval_features(["steam_pct"], "Steam alone")
    eval_features(["wprp_blend_prob", "steam_pct"], "WPR + steam (does steam add anything?)")
    eval_features(["mkt_prob", "steam_pct"], "Market + steam (does steam beat the market's OWN close price?)")


if __name__ == "__main__":
    run()
