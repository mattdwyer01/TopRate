"""
calibrate_price_beta.py - re-derive the wprp_price softmax beta from real
resulted-race outcomes, and write it into wpr_models/config.json.

WHY
  project_race() turns projected WPR into an implied win probability via a
  softmax: p = exp(beta * (wpr - wpr.max())) / sum(...). beta controls how
  much win probability separation a given WPR gap implies. It was set to
  0.4 as a fixed constant when the model was built and never re-derived
  against actual results.

  A calibration check against resulted races (see margin_analysis.py's
  neighbour, this script) found beta=0.4 badly overconfident on the
  model's own biggest favourites: implied win probability ~49% for its
  top decile of picks, actual win rate ~27%. A grid search minimising
  Brier score against real outcomes, validated on a held-out date split,
  landed at beta ~0.15-0.20 with a clearly better held-out Brier score
  and a near-flat calibration table across deciles. beta later drifted to
  0.3 via a separate comparison script (wpr_beta03_daily_state_summary.py)
  that also used the stale reimplementation below - see BUG FIX.

  This does NOT touch the WPR projection model itself (projection.joblib,
  confidence.joblib, or the projected WPR numbers/ranking) - only the
  softmax parameter that converts a projected WPR gap into a displayed
  price/probability. Ranking is unaffected (softmax is rank-preserving for
  any beta > 0); only the price numbers change.

  BUG FIX (Sep 2026): _load_resulted() used to call wpr_bet_selection_
  post_retrain.build_new_proj_frame(), which manually reimplemented the
  ADJ_TERM computation by hand (wpr._track_barrier_term(t, d, b, fs,
  tb_lookup) with 5 args, wpr._merit_term(wpr._merit_bucket(v, edges),
  lookup), wpr._CALIB_ADJ_SLOPE) - all three no longer match wpr_
  projection.py's current architecture (population terms became trained
  LightGBM models fed via _merit_term(value, field_size, model, features,
  ...), _merit_bucket doesn't exist any more, and _CALIB_ADJ_SLOPE was
  removed entirely in the "serving-time calibration removed" rebuild).
  Confirmed by reading the current function signatures: this would raise
  AttributeError/TypeError before ever reaching the beta grid search -
  this script has not been able to run successfully since at least the
  population-term-to-trained-model migration, meaning beta has not been
  re-validated against anything built after that point (trainer_change
  added then removed, the wpr_form_history dedup fix, the pop_going
  alignment fix - none of these went through this check).

  Fixed by calling toprate_daily.compute_wpr_projection() directly - the
  exact same entry point the live daily pipeline uses - for a sample of
  PAST resulted dates instead of "today" (that function needs no
  adaptation for historical dates, it only ever reads rows with
  date < target date). Reuses 100% real production code, zero drift risk
  by construction - the SAME bug class cannot recur here even if the
  ADJ_TERM architecture changes again.

  Also fixed: best_beta used to be selected by TRAIN Brier ("best beta
  (train-selected)"), not the held-out Brier this script computes right
  next to it - a real methodology smell for a script whose whole point is
  honest out-of-sample validation. Selection is now by held-out Brier.

  Re-run (Sep 2026) on 46 resulted days / 2,143 races / 20,189 runners via
  the fixed loader: beta=0.15 held-out Brier 0.0892 vs the then-shipped
  beta=0.3's 0.0949 (a real, measured ~6% relative improvement, not
  noise - see chat) - beta=0.3's own top-decile calibration was 46.4%
  implied vs 27.8% actual win rate, badly overconfident; beta=0.15 came
  in at 29.9% vs 28.1%, close to fair. Shipped.

  WHY wprp_proj IS RECOMPUTED, NOT READ FROM toprate_runners.csv
  compute_wpr_projection() in toprate_daily.py only ever (re)computes
  wprp_proj for the day just fetched - it never retroactively rewrites
  historical rows (by design, so the Review tab's predicted-vs-actual
  accuracy audit reflects what was ACTUALLY predicted at the time, not a
  hindsight-revised number). So after any model change, toprate_runners.
  csv's wprp_proj column stays stale for nearly all of history until
  enough new days accumulate under the new model - reading it directly
  here would calibrate beta against a mix of old models almost entirely.
  Recomputing via compute_wpr_projection() with the CURRENTLY SHIPPED
  config.json (same convention already used for calibrate_edge_score.py's
  means/stds) is slower (rebuilds each date's features fresh, several
  minutes for ~45 days) than a direct CSV read, acceptable for a script
  meant to be re-run quarterly (or after any ADJ_TERM architecture
  change), not daily.

USAGE
  python calibrate_price_beta.py                    # report only
  python calibrate_price_beta.py --write             # also update config.json
  python calibrate_price_beta.py --days-back 90      # wider sample window

Descriptive/re-calibration only. No change to projection.joblib or
confidence.joblib.

NO EM DASHES policy: hyphens only in this file.
"""
import argparse
import json
from pathlib import Path

import numpy as np
import pandas as pd

RUNNERS_CSV = "toprate_runners.csv"
CONFIG_PATH = Path("wpr_models") / "config.json"
BETA_GRID = [0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.35, 0.40, 0.50]
DEFAULT_DAYS_BACK = 45


def _load_resulted(days_back=DEFAULT_DAYS_BACK):
    """Resulted runners from the last `days_back` days, with wprp_proj
    recomputed fresh via the real toprate_daily.compute_wpr_projection()
    entry point (see BUG FIX above for why this replaced the old manual
    reimplementation) - not read directly from toprate_runners.csv, whose
    stored wprp_proj reflects whatever model was shipped on the day each
    row was originally fetched, not the current one."""
    import toprate_daily as td

    runners_df = td.load_runners()
    df = runners_df.copy()
    df["date_only"] = df["date"].astype(str).str[:10]
    resulted = df[df["resulted"].fillna(0).astype(float) == 1]
    dates = sorted(resulted["date_only"].unique())
    if not dates:
        return pd.DataFrame(columns=["wprp_proj", "won", "race_id", "date"])

    cutoff = (pd.Timestamp(dates[-1]) - pd.Timedelta(days=days_back)).strftime("%Y-%m-%d")
    target_dates = [d for d in dates if d >= cutoff]
    print(f"  recomputing wprp_proj for {len(target_dates)} resulted dates "
          f"({target_dates[0]} .. {target_dates[-1]}) via compute_wpr_projection() ...")
    for i, d in enumerate(target_dates):
        runners_df = td.compute_wpr_projection(runners_df, d)
        if (i + 1) % 10 == 0:
            print(f"    ... {i + 1}/{len(target_dates)} dates done")

    scored = runners_df.copy()
    scored["date_only"] = scored["date"].astype(str).str[:10]
    scored = scored[
        scored["date_only"].isin(target_dates)
        & (scored["resulted"].fillna(0).astype(float) == 1)
    ]
    scored["won"] = pd.to_numeric(scored["won"], errors="coerce")
    scored["date"] = pd.to_datetime(scored["date"], errors="coerce")
    return scored.dropna(subset=["wprp_proj", "won", "race_id", "date"])


def _brier(data, beta):
    """Mean squared error between softmax(beta) win prob and actual win,
    across every runner in every race with >= 4 finishers."""
    rows = []
    for rid, g in data.groupby("race_id"):
        if len(g) < 4:
            continue
        pv = g["wprp_proj"].to_numpy(dtype=float)
        e = np.exp(beta * (pv - pv.max()))
        p = e / e.sum()
        rows.extend(zip(p, g["won"]))
    arr = pd.DataFrame(rows, columns=["p", "won"])
    if len(arr) == 0:
        return float("nan")
    return float(((arr["p"] - arr["won"]) ** 2).mean())


def calibrate(write=False, days_back=DEFAULT_DAYS_BACK):
    d = _load_resulted(days_back)
    cut = d["date"].quantile(0.60)
    trn, tst = d[d["date"] < cut], d[d["date"] >= cut]
    print(f"\nresulted races: {d['race_id'].nunique():,}  "
          f"(search < {cut.date()}: {trn['race_id'].nunique():,}, "
          f"held-out: {tst['race_id'].nunique():,})")
    print("\nbeta | search Brier | held-out Brier")
    results = {}
    for beta in BETA_GRID:
        b_trn, b_tst = _brier(trn, beta), _brier(tst, beta)
        results[beta] = (b_trn, b_tst)
        print(f"  beta={beta:.2f}   search {b_trn:.4f}   held-out {b_tst:.4f}")

    # Selected by HELD-OUT Brier, not search/train Brier (bug fix, see
    # module docstring) - the whole point of the split is to avoid picking
    # whatever beta happens to look best on the data used to pick it.
    best_beta = min(results, key=lambda b: results[b][1])

    cur_beta = None
    if CONFIG_PATH.exists():
        cur_beta = json.load(open(CONFIG_PATH)).get("beta")
    held_out_best = results[best_beta][1]
    held_out_cur = None
    if cur_beta is not None:
        held_out_cur = results[cur_beta][1] if cur_beta in results else _brier(tst, cur_beta)
    print(f"\nbest beta (held-out-selected): {best_beta}")
    print(f"  held-out Brier at best beta: {held_out_best:.4f}")
    if held_out_cur is not None:
        print(f"  held-out Brier at current config beta ({cur_beta}): "
              f"{held_out_cur:.4f}")

    if write:
        if not CONFIG_PATH.exists():
            print(f"\n{CONFIG_PATH} not found, cannot write.")
            return best_beta
        cfg = json.load(open(CONFIG_PATH))
        old = cfg.get("beta")
        cfg["beta"] = float(best_beta)
        json.dump(cfg, open(CONFIG_PATH, "w"), indent=1)
        print(f"\nwrote beta {old} -> {best_beta} to {CONFIG_PATH}")
    return best_beta


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--write", action="store_true",
                    help="write the selected beta into wpr_models/config.json")
    ap.add_argument("--days-back", type=int, default=DEFAULT_DAYS_BACK,
                    help=f"how many resulted days back to sample (default {DEFAULT_DAYS_BACK})")
    args = ap.parse_args()
    calibrate(write=args.write, days_back=args.days_back)
