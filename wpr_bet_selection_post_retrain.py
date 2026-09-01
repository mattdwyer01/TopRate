"""
wpr_bet_selection_post_retrain.py - re-checks the edge-score bet-selection
strategies (wpr_bet_selection_dimensions.py / wpr_bet_selection_fixed_price.py)
now that trainer_merit/jockey_merit are baked into WPR itself as ADJ_TERMs
(see wpr_trainer_jockey_adj_strike_eval.py, shipped in PR #147).

WHY THIS SCRIPT EXISTS
  Those earlier scripts read wprp_proj straight out of toprate_runners.csv.
  compute_wpr_projection() in toprate_daily.py only ever recomputes wprp_proj
  for TODAY's races (see its own docstring) - it never retroactively rewrites
  historical rows. So re-running the old scripts right now would still be
  scoring nearly all of history on the OLD wprp_proj (pre trainer/jockey
  ADJ_TERMs) - not a real answer to "how do the strategies look with the new
  model". This script recomputes wprp_proj for every historical resulted row
  using the actual shipped config.json (trainer_merit/jockey_merit included),
  replicating project_race()'s exact math (base with slope+intercept folded
  in via add_base, then capped adjustment sum x _CALIB_ADJ_SLOPE), then
  re-runs the same walk-forward edge-score methodology on top of it.

DOUBLE-COUNTING CHECK
  trainer_win_pct_365d/jockey_win_pct_90d are now baked into wprp_proj AND
  still sit as raw features in the edge score's own z-score blend
  (calibrate_edge_score.FEATURES). Tests both:
    A) edge features unchanged: [new_wprp_proj, trainer_win_pct_365d,
       jockey_win_pct_90d, pfm_score] - the naive re-run, double-counts the
       signal (once inside wprp_proj, once raw).
    B) trainer/jockey dropped from the blend: [new_wprp_proj, pfm_score] -
       avoids double-counting, since that signal now already lives in
       wprp_proj.

USAGE
  python wpr_bet_selection_post_retrain.py

NO EM DASHES policy: hyphens only in this file.
"""
import json

import numpy as np
import pandas as pd

import wpr_projection as wpr
from wpr_own_pace_backtest import add_base, merge_won_by_horse_date
from wpr_trainer_jockey_adj_strike_eval import merge_trainer_jockey_by_horse_date

FORM_CSV = "wpr_form_history.csv.gz"
RUNNERS_CSV = "toprate_runners.csv"
CONFIG_PATH = "wpr_models/config.json"
BURN_IN_WEEKS = 5
MIN_TRAIN = 300
EDGE_THRESHOLDS = [0.08, 0.10, 0.13, 0.15, 0.20]
PRICE_CAPS = [15.0, 26.0]


def merge_price_pfm(D, runners_csv=RUNNERS_CSV):
    tr = pd.read_csv(runners_csv, low_memory=False,
                     usecols=["horse", "date", "fixed_win_price", "starting_price_sp", "pfm_score"])
    tr["date"] = pd.to_datetime(tr["date"], errors="coerce")
    tr = tr.dropna(subset=["date"])
    tr = tr.drop_duplicates(subset=["horse", "date"], keep=False)
    return D.merge(tr, on=["horse", "date"], how="inner")


def build_new_proj_frame():
    """Full historical frame with wprp_proj recomputed using the SHIPPED
    (post-retrain) config.json - the real, final model, not a freshly
    refit one - since the question is "what does the model we just
    shipped say about history", not a fresh walk-forward re-derivation
    of trainer_merit/jockey_merit itself (already done and validated
    separately in wpr_trainer_jockey_adj_strike_eval.py)."""
    cfg = json.load(open(CONFIG_PATH))

    print("Rebuilding training frame...")
    full = wpr.build_training_frame(FORM_CSV, verbose=True, n_jobs=-1)
    full["date"] = pd.to_datetime(full["date"])

    print("Merging result, trainer/jockey win-rate, price and pfm_score "
          "from toprate_runners.csv by (horse, date)...")
    full = merge_won_by_horse_date(full)
    full = merge_trainer_jockey_by_horse_date(full)
    full = merge_price_pfm(full)

    full = add_base(full)
    non_pop_terms = [t for t in wpr.ADJ_TERMS
                     if t not in ("track_barrier", "closing_merit", "trainer_merit", "jockey_merit")]
    full = full.dropna(subset=["target", "_base", "career_avg"] + non_pop_terms +
                        ["barrier", "field_size", "track", "cur_distance"])
    print(f"Scoped rows: {len(full):,}")

    # Apply the SHIPPED population lookups directly (final model, already
    # fitted and validated) - same functions project_race() itself calls.
    tb_lookup = cfg.get("track_barrier_lookup")
    pb_lookup = cfg.get("pace_baseline_lookup")
    tm_edges, tm_lookup = cfg.get("trainer_merit_edges"), cfg.get("trainer_merit_lookup")
    jm_edges, jm_lookup = cfg.get("jockey_merit_edges"), cfg.get("jockey_merit_lookup")

    full["track_barrier"] = [
        wpr._track_barrier_term(t, d, b, fs, tb_lookup)
        for t, d, b, fs in zip(full["track"], full["cur_distance"], full["barrier"], full["field_size"])
    ]
    full["closing_merit"] = [
        wpr._closing_merit_term(cp, pb_lookup) for cp in full["closing_pairs"]
    ]
    full["trainer_merit"] = [
        wpr._merit_term(wpr._merit_bucket(v, tm_edges), tm_lookup) for v in full["trainer_win_pct_365d"]
    ]
    full["jockey_merit"] = [
        wpr._merit_term(wpr._merit_bucket(v, jm_edges), jm_lookup) for v in full["jockey_win_pct_90d"]
    ]

    adj = wpr._cap_adj_sum(full[wpr.ADJ_TERMS].to_numpy()).sum(axis=1) * wpr._CALIB_ADJ_SLOPE
    full["wprp_proj"] = full["_base"].to_numpy() + adj

    sp = pd.to_numeric(full["fixed_win_price"], errors="coerce")
    sp_fallback = pd.to_numeric(full["starting_price_sp"], errors="coerce")
    full["used_sp_fallback"] = sp.isna() & sp_fallback.notna()
    full["sp"] = sp.fillna(sp_fallback)
    full["pfm_score"] = pd.to_numeric(full["pfm_score"], errors="coerce")
    full = full.dropna(subset=["sp"])
    full = full[full["sp"] > 1.0]
    return full.sort_values("date")


def _score(data, mean, std, features):
    z = (data[features] - mean) / std.replace(0, np.nan)
    score = z.mean(axis=1, skipna=True)
    return score.where(data["wprp_proj"].notna(), 0.0)


def walk_forward_bets(d, features, burn_in_weeks=BURN_IN_WEEKS, min_train=MIN_TRAIN):
    weeks = sorted(d["date"].dt.to_period("W").unique())
    test_weeks = weeks[burn_in_weeks:]
    bets = []
    for wk in test_weeks:
        train = d[d["date"].dt.to_period("W") < wk]
        test = d[d["date"].dt.to_period("W") == wk].copy()
        if len(train) < min_train or len(test) == 0:
            continue
        mean, std = train[features].mean(), train[features].std()
        test["score"] = _score(test, mean, std, features)
        test = test.dropna(subset=["score"])
        if len(test) == 0:
            continue
        e = np.exp(test["score"] - test.groupby("race_id")["score"].transform("max"))
        p = e / test.groupby("race_id")["score"].transform(lambda s: np.exp(s - s.max()).sum())
        test["p_mkt_norm"] = (1.0 / test["sp"]) / test.groupby("race_id")["sp"].transform(
            lambda s: (1.0 / s).sum())
        test["edge"] = p - test["p_mkt_norm"]
        bets.append(test[["won", "sp", "edge", "used_sp_fallback"]])
    return pd.concat(bets, ignore_index=True)


def wpr_price_bets(d, beta, burn_in_weeks=BURN_IN_WEEKS):
    """WPR price ALONE as the model side of edge - no blend, no z-score
    fitting at all (nothing to fit: wprp_proj is already the final,
    calibrated model output). Restricted to the same test weeks as the
    blend variants (burn_in_weeks skipped) purely so the comparison is
    apples-to-apples on identical rows, not because this variant needs a
    burn-in period itself."""
    weeks = sorted(d["date"].dt.to_period("W").unique())
    test_weeks = set(weeks[burn_in_weeks:])
    d = d[d["date"].dt.to_period("W").isin(test_weeks)].copy()
    d = d.dropna(subset=["wprp_proj"])
    e = np.exp(beta * (d["wprp_proj"] - d.groupby("race_id")["wprp_proj"].transform("max")))
    p = e / d.groupby("race_id")["wprp_proj"].transform(
        lambda s: np.exp(beta * (s - s.max())).sum())
    d["p_mkt_norm"] = (1.0 / d["sp"]) / d.groupby("race_id")["sp"].transform(lambda s: (1.0 / s).sum())
    d["edge"] = p - d["p_mkt_norm"]
    return d[["won", "sp", "edge", "used_sp_fallback"]]


def report(sub, label):
    if len(sub) < 20:
        print(f"    {label}: n={len(sub)} (too small, skipped)")
        return
    profit = np.where(sub["won"] == 1, sub["sp"] - 1, -1.0)
    se = profit.std(ddof=1) / np.sqrt(len(profit))
    t = profit.mean() / se if se > 0 else float("nan")
    flag = "  ** SIGNIFICANT **" if abs(t) >= 1.96 else ""
    # avg/median price + % favourites (<$3) - a suspiciously strong result
    # that's just "the filter mostly selects short-priced favourites" (real
    # favourite-longshot bias, not model skill) shows up here as a much
    # lower avg price than the unfiltered population.
    print(f"      [avg price ${sub['sp'].mean():.2f}  median ${sub['sp'].median():.2f}  "
          f"<$3: {(sub['sp'] < 3).mean()*100:.1f}%]")
    print(f"    {label}: n={len(sub):5d}  strike={sub['won'].mean()*100:5.2f}%  "
          f"ROI={profit.sum()/len(sub)*100:+6.2f}%  t={t:+.2f}{flag}")


def report_bets(bets, label):
    print(f"\n{'='*70}\nVariant {label}\n{'='*70}")
    fallback_pct = bets["used_sp_fallback"].mean() * 100
    print(f"total scored bets: {len(bets):,}  (fixed_win_price fallback to SP for {fallback_pct:.1f}%)  "
          f"[population avg price ${bets['sp'].mean():.2f}, <$3: {(bets['sp'] < 3).mean()*100:.1f}%]\n")

    print("=== Edge threshold alone ===")
    for thr in EDGE_THRESHOLDS:
        report(bets[bets["edge"] >= thr], f"edge>={thr:.2f}")

    print("\n=== Edge threshold x price cap ===")
    for thr in EDGE_THRESHOLDS:
        base = bets[bets["edge"] >= thr]
        for cap in PRICE_CAPS:
            report(base[base["sp"] <= cap], f"edge>={thr:.2f}, price<={cap:.0f}")


def run_variant(d, features, label):
    report_bets(walk_forward_bets(d, features), f"{label}: edge features = {features}")


def _brier(data, beta):
    """Same metric/shape as calibrate_price_beta.py's own _brier - kept
    separate (not imported) since that script reads wprp_proj straight
    from toprate_runners.csv, which is stale for history (see module
    docstring); this one scores the freshly recomputed wprp_proj."""
    rows = []
    for rid, g in data.groupby("race_id"):
        if len(g) < 4:
            continue
        pv = g["wprp_proj"].to_numpy(dtype=float)
        e = np.exp(beta * (pv - pv.max()))
        p = e / e.sum()
        rows.extend(zip(p, g["won"]))
    arr = pd.DataFrame(rows, columns=["p", "won"])
    return float(((arr["p"] - arr["won"]) ** 2).mean()) if len(arr) else float("nan")


def refit_beta(d):
    """calibrate_price_beta.py's own retrain-log note is explicit: 'beta
    carried forward from existing config: 0.4 (re-run calibrate_price_beta.py
    --write to re-derive it)' - and that script's own history already found
    0.4 'badly overconfident' even on the OLD model (implied ~49% win prob
    on top-decile picks vs ~27% actual, held-out Brier 0.096 vs ~0.090 at
    beta~0.15-0.20). Adding two more ADJ_TERMs widens wprp_proj's spread
    further, so reusing 0.4 unmodified for a WPR-price-alone edge variant
    would be comparing against a KNOWN-overconfident price, not a fair test
    of "is WPR price alone as good as the blend" - grid search + held-out
    Brier, same shape as calibrate_price_beta.py, on the freshly recomputed
    projection instead of stale toprate_runners.csv values."""
    grid = [0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.40]
    cut = d["date"].quantile(0.70)
    trn, tst = d[d["date"] < cut], d[d["date"] >= cut]
    print(f"\nRe-deriving beta on the recomputed wprp_proj (train Brier picks, held-out verifies):")
    print("  beta | train Brier | held-out Brier")
    best_beta, best_brier = None, float("inf")
    for beta in grid:
        b_trn, b_tst = _brier(trn, beta), _brier(tst, beta)
        print(f"    {beta:.2f} | {b_trn:.4f}      | {b_tst:.4f}")
        if b_trn < best_brier:
            best_brier, best_beta = b_trn, beta
    print(f"  train-selected beta: {best_beta}  (held-out Brier at this beta: {_brier(tst, best_beta):.4f})")
    return best_beta


def run():
    d = build_new_proj_frame()
    print(f"\nresulted races: {d['race_id'].nunique():,}  runners: {len(d):,}  "
          f"({d['date'].min().date()} to {d['date'].max().date()})")

    run_variant(d, ["wprp_proj", "trainer_win_pct_365d", "jockey_win_pct_90d", "pfm_score"],
                "A (unchanged features, double-counts trainer/jockey)")
    run_variant(d, ["wprp_proj", "pfm_score"],
                "B (trainer/jockey dropped, avoids double-counting)")

    stale_beta = json.load(open(CONFIG_PATH)).get("beta", 0.4)
    report_bets(wpr_price_bets(d, stale_beta),
                f"C (WPR price alone, STALE beta={stale_beta} - documented overconfident, see refit below)")

    new_beta = refit_beta(d)
    report_bets(wpr_price_bets(d, new_beta), f"D (WPR price alone, refit beta={new_beta})")

    print("\nSame multiple-comparisons caveat as the earlier bet-selection scripts: treat any")
    print("row here as a hypothesis for a future walk-forward period, not a result to ship.")


if __name__ == "__main__":
    run()
