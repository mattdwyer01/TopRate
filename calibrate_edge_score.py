"""
calibrate_edge_score.py - fit the "edge score": a logistic regression
blending WPR projection + speed/form-provider ratings + trailing
jockey/trainer form into a per-race win probability, compared against the
market's own implied probability to find value (edge = model_prob -
market_prob). Writes the fitted coefficients into wpr_models/config.json
under "edge_score" for wpr_projection.compute_edge_scores to use.

WHY
  A rank-1-pick backtest of WPR alone (wpr_nett or wprp_proj) never clears
  the market's own accuracy (AUC ~0.59 on held-out dates) - consistent with
  CLAUDE.md's note that the projection model is at its accuracy ceiling.
  But a blend of wprp_proj + speed_rating + pfm_score + pf_ai_score +
  trailing jockey/trainer win% held out materially better (AUC ~0.72 on
  unseen dates, Aug 2026 audit): trainer/jockey trailing form carries real
  incremental signal WPR isn't capturing on its own.

  Betting the TOP PICK from this blend still doesn't beat the market's own
  strike rate (the market has information we don't - late scratches, drift,
  insider money). What DOES show a genuine held-out edge is backing the
  OVERLAY: runners where this blend's normalized win probability exceeds
  the market's implied probability by a wide enough margin (>=8-10 points
  showed +6% to +17% ROI on ~850-1250 held-out bets in the audit). That is
  what "edge" in compute_edge_scores is for - a bet-SELECTION filter, not
  a replacement top-pick ranking.

  Deliberately excludes jt_combo_win_pct - see toprate_daily.py's SIGNALS
  comment: that field leaks the runner's own race result on low-ride-count
  combos (winPercent reads ~100/~0 exactly matching whether the runner just
  won or lost), so any backtest or model using it is meaningless.

USAGE
  python calibrate_edge_score.py           # report only
  python calibrate_edge_score.py --write   # also update wpr_models/config.json

Re-run this quarterly (or whenever a season's worth of new resulted races
has accumulated) to keep the coefficients current - see CLAUDE.md.

NO EM DASHES policy: hyphens only in this file.
"""
import argparse
import json
from pathlib import Path

import numpy as np
import pandas as pd
from sklearn.linear_model import LogisticRegression
from sklearn.metrics import log_loss, roc_auc_score

RUNNERS_CSV = "toprate_runners.csv"
CONFIG_PATH = Path("wpr_models") / "config.json"
FEATURES = ["wprp_proj", "speed_rating", "pfm_score", "pf_ai_score",
            "trainer_win_pct_365d", "jockey_win_pct_90d"]


def _load_resulted():
    df = pd.read_csv(RUNNERS_CSV, dtype={"run_id": str, "race_id": str},
                     low_memory=False)
    df["resulted"] = pd.to_numeric(df.get("resulted"), errors="coerce")
    df = df[(df["resulted"] == 1) & (df.get("scratched") != 1)].copy()
    df["date"] = pd.to_datetime(df.get("date"), errors="coerce")
    df["won"] = pd.to_numeric(df.get("won"), errors="coerce").fillna(0)
    df["sp"] = pd.to_numeric(df.get("starting_price_sp"), errors="coerce")
    df["sp"] = df["sp"].fillna(pd.to_numeric(df.get("price_top"), errors="coerce"))
    for f in FEATURES:
        df[f] = pd.to_numeric(df.get(f), errors="coerce")
    df = df.dropna(subset=["date", "race_id", "sp"])
    df = df[df["sp"] > 1.0]
    return df


def _matrix(data, medians):
    return data[FEATURES].fillna(pd.Series(medians)).to_numpy(dtype=float)


def _fit(data, medians):
    clf = LogisticRegression(max_iter=1000)
    clf.fit(_matrix(data, medians), data["won"].to_numpy())
    return clf


def _eval(clf, data, medians, label):
    p = clf.predict_proba(_matrix(data, medians))[:, 1]
    auc = roc_auc_score(data["won"], p)
    ll = log_loss(data["won"], p)
    print(f"  {label}: n={len(data):,}  AUC={auc:.4f}  logloss={ll:.4f}")
    return p


def _overlay_report(data, p):
    d = data.copy()
    d["p_model"] = p
    d["p_model_norm"] = d["p_model"] / d.groupby("race_id")["p_model"].transform("sum")
    d["p_mkt"] = 1.0 / d["sp"]
    d["p_mkt_norm"] = d["p_mkt"] / d.groupby("race_id")["p_mkt"].transform("sum")
    d["edge"] = d["p_model_norm"] - d["p_mkt_norm"]
    print("\n  edge-vs-market overlay ROI on this held-out slice:")
    for thr in [0.0, 0.03, 0.05, 0.08, 0.10]:
        sub = d[d["edge"] >= thr]
        if len(sub) == 0:
            continue
        profit = np.where(sub["won"] == 1, sub["sp"] - 1, -1.0)
        print(f"    edge>={thr:.2f}: n={len(sub):5d}  strike={sub['won'].mean()*100:5.1f}%  "
              f"ROI={profit.sum()/len(sub)*100:+6.2f}%")


def calibrate(write=False):
    d = _load_resulted()
    cut = d["date"].quantile(0.70)
    train, test = d[d["date"] < cut].copy(), d[d["date"] >= cut].copy()
    print(f"resulted races: {d['race_id'].nunique():,}  runners: {len(d):,}  "
          f"(train < {cut.date()}: {train['race_id'].nunique():,} races, "
          f"held-out: {test['race_id'].nunique():,} races)")

    train_medians = train[FEATURES].median().to_dict()
    clf = _fit(train, train_medians)
    print("\nheld-out validation (fit on first 70% of dates, tested on last 30%):")
    _eval(clf, train, train_medians, "train")
    p_test = _eval(clf, test, train_medians, "held-out")
    _overlay_report(test, p_test)

    wpr_median = train_medians["wprp_proj"]
    clf_wpr = LogisticRegression(max_iter=1000).fit(
        train[["wprp_proj"]].fillna(wpr_median).to_numpy(dtype=float), train["won"])
    p_wpr = clf_wpr.predict_proba(
        test[["wprp_proj"]].fillna(wpr_median).to_numpy(dtype=float))[:, 1]
    print(f"\n  reference - wprp_proj alone (held-out): "
          f"AUC={roc_auc_score(test['won'], p_wpr):.4f}  "
          f"logloss={log_loss(test['won'], p_wpr):.4f}")

    # Final production model: refit on ALL resulted data now that the
    # held-out numbers above have proven the approach generalizes - more
    # data makes the written coefficients more stable than the 70%-only fit.
    full_medians = d[FEATURES].median().to_dict()
    clf_full = _fit(d, full_medians)

    if write:
        if not CONFIG_PATH.exists():
            print(f"\n{CONFIG_PATH} not found, cannot write.")
            return
        cfg = json.load(open(CONFIG_PATH))
        cfg["edge_score"] = {
            "features": FEATURES,
            "coef": clf_full.coef_[0].tolist(),
            "intercept": float(clf_full.intercept_[0]),
            "medians": full_medians,
            "trained_on_races": int(d["race_id"].nunique()),
            "trained_on_runners": int(len(d)),
            "date_range": [str(d["date"].min().date()), str(d["date"].max().date())],
            "note": ("Logistic regression; deliberately excludes jt_combo_win_pct "
                     "(confirmed leak - see toprate_daily.py SIGNALS comment). "
                     "Held-out AUC/overlay validation is in this script's own "
                     "output/git history, not in this config. Use edge (model_prob "
                     "- market_prob) as a bet-selection filter, not a top-pick "
                     "ranking replacement - see calibrate_edge_score.py docstring."),
        }
        json.dump(cfg, open(CONFIG_PATH, "w"), indent=1)
        print(f"\nwrote edge_score ({len(FEATURES)} features, "
              f"{d['race_id'].nunique():,} races) to {CONFIG_PATH}")


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--write", action="store_true",
                    help="write the fitted edge_score block into wpr_models/config.json")
    args = ap.parse_args()
    calibrate(write=args.write)
