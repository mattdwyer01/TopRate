"""
wpr_race_speed_hyperparam_tune.py - a regularization/capacity search for
race_speed_estimate.py's LightGBM model, motivated directly by
wpr_race_speed_diagnostic_check.py's own finding (Sep 2026, see chat):
a real (if modest) train-vs-holdout correlation gap (+0.3765 train vs
+0.2959 held-out, on the same 24-feature baseline and 2-year-bounded
population that script used) - meaning this is NOT a pure information
ceiling, there is some genuine slack in how the model is fit today.

WHY REGULARIZATION, NOT MORE CAPACITY
  The shipped hyperparameters (max_depth=3, num_leaves=8, n_estimators=200,
  no L1/L2, default min_child_samples=20) are already shallow. A gap
  appearing at this little capacity points at OTHER knobs being too loose
  for a genuinely weak-signal target - too many boosting rounds (each
  round increasingly fits residual noise), too permissive a leaf-size
  floor, or no L1/L2 pull toward zero - rather than "the trees need to be
  bigger." The search below leans that direction (smaller learning rate +
  early stopping instead of a fixed round count, larger min_child_samples,
  L1/L2), with one deliberately larger-capacity config included as a
  falsification check (confirms capacity is not the fix, if it does not
  win) rather than an unexamined assumption.

METHOD (avoids hyperparameter-search leakage into the reported number)
  Same OUTER 70/30 chronological split as every other script tonight, so
  the final 30% test set is IDENTICAL to diagnostic_check.py's own
  held-out set - directly comparable, apples to apples.
  The 70% train side is further split chronologically 80/20 into an
  INNER train/validation pair, used ONLY for hyperparameter selection via
  LightGBM's native early stopping (picks n_estimators per candidate
  automatically, rather than grid-searching it as a separate axis).
  Once a winner is chosen on the inner validation set, it is refit on the
  FULL 70% outer-train and scored ONCE on the untouched 30% outer-test -
  that number is the one that counts, never seen during selection.

NO EM DASHES policy: hyphens only.
"""
import numpy as np
import pandas as pd
import lightgbm as lgb

import race_speed_estimate as rse

CANDIDATES = [
    {"name": "SHIPPED (baseline, for reference)",
     "params": dict(num_leaves=8, max_depth=3, learning_rate=0.05,
                     min_child_samples=20, reg_alpha=0.0, reg_lambda=0.0)},
    {"name": "slower LR + early stop",
     "params": dict(num_leaves=8, max_depth=3, learning_rate=0.02,
                     min_child_samples=20, reg_alpha=0.0, reg_lambda=0.0)},
    {"name": "larger min_child_samples",
     "params": dict(num_leaves=8, max_depth=3, learning_rate=0.05,
                     min_child_samples=80, reg_alpha=0.0, reg_lambda=0.0)},
    {"name": "L1+L2 regularization",
     "params": dict(num_leaves=8, max_depth=3, learning_rate=0.05,
                     min_child_samples=20, reg_alpha=1.0, reg_lambda=1.0)},
    {"name": "combined (slow LR + min_child + L1/L2)",
     "params": dict(num_leaves=8, max_depth=3, learning_rate=0.02,
                     min_child_samples=80, reg_alpha=1.0, reg_lambda=1.0)},
    {"name": "smaller capacity (falsification check: even less)",
     "params": dict(num_leaves=4, max_depth=2, learning_rate=0.05,
                     min_child_samples=20, reg_alpha=0.0, reg_lambda=0.0)},
    {"name": "LARGER capacity (falsification check: more, not less)",
     "params": dict(num_leaves=16, max_depth=4, learning_rate=0.05,
                     min_child_samples=20, reg_alpha=0.0, reg_lambda=0.0)},
]
MAX_ESTIMATORS = 2000
EARLY_STOP_ROUNDS = 50


def load_population(limit=None):
    print("Loading form history...")
    fh_full = rse._load_and_prep_form()
    since = fh_full["date"].max() - pd.Timedelta(days=730)
    fh = fh_full[fh_full["date"] >= since].copy()
    print(f"  bounded to last 2 years ({since.date()} onward): {len(fh):,} rows")

    fh2 = fh.dropna(subset=["track", "raceNumber", "raceShapeEarly"]).copy()
    fh2["race_key"] = (fh2["track"].astype(str) + "|" + fh2["date"].astype(str)
                        + "|" + fh2["raceNumber"].astype(str))
    race_meta = (fh2.groupby("race_key")
                   .agg(date=("date", "first"), rse=("raceShapeEarly", "first"),
                        n=("horse_lc", "count"))
                   .reset_index())
    race_meta = race_meta[race_meta["n"] >= 4].sort_values("date").reset_index(drop=True)
    print(f"  {len(race_meta):,} races with 4+ runners and a known raceShapeEarly")
    if limit:
        race_meta = race_meta.tail(limit).reset_index(drop=True)
        print(f"  --limit applied: using most recent {len(race_meta):,} races (smoke test)")
    return fh, fh2, race_meta


def build_rows(race_df, fh, fh_by_race, pmeans_cache, label):
    rows, ys = [], []
    for day, day_races in race_df.groupby(race_df["date"].dt.normalize()):
        if day not in pmeans_cache:
            pmeans_cache[day] = rse._prior_means(fh, day)
        pmeans = pmeans_cache[day]
        for _, rr in day_races.iterrows():
            runners = fh_by_race.get_group(rr["race_key"])
            rows.append(rse._race_features(runners, pmeans))
            ys.append(rr["rse"])
    print(f"  {label}: {len(rows):,} rows built")
    return pd.DataFrame(rows), np.array(ys, dtype=float)


def run(limit=None):
    fh, fh2, race_meta = load_population(limit=limit)
    fh_by_race = fh2.groupby("race_key")
    pmeans_cache = {}

    outer_cut = race_meta["date"].quantile(0.70)
    outer_train = race_meta[race_meta["date"] < outer_cut]
    outer_test = race_meta[race_meta["date"] >= outer_cut]
    print(f"\nOuter split at {outer_cut.date()}: {len(outer_train):,} train, {len(outer_test):,} test "
          f"(test set identical to diagnostic_check.py's own held-out set)")

    inner_cut = outer_train["date"].quantile(0.80)
    inner_train = outer_train[outer_train["date"] < inner_cut]
    inner_val = outer_train[outer_train["date"] >= inner_cut]
    print(f"Inner split (within outer-train) at {inner_cut.date()}: "
          f"{len(inner_train):,} inner-train, {len(inner_val):,} inner-val (for hyperparam selection only)")

    print("\nBuilding feature rows (inner train / inner val / outer test)...")
    Xtr_inner, ytr_inner = build_rows(inner_train, fh, fh_by_race, pmeans_cache, "inner-train")
    Xval, yval = build_rows(inner_val, fh, fh_by_race, pmeans_cache, "inner-val")
    Xte, yte = build_rows(outer_test, fh, fh_by_race, pmeans_cache, "outer-test (final, untouched)")
    # outer-train is EXACTLY inner-train + inner-val (inner_cut partitions
    # outer_train with no gap/overlap, both chronologically sorted since
    # race_meta itself was sorted at construction) - concatenate the
    # already-built rows instead of rebuilding features for the same
    # races a second time.
    Xtr_outer = pd.concat([Xtr_inner, Xval], ignore_index=True)
    ytr_outer = np.concatenate([ytr_inner, yval])

    med_inner = Xtr_inner.median()
    Xtr_inner_f = Xtr_inner.fillna(med_inner)
    Xval_f = Xval.fillna(med_inner)

    print("\n" + "=" * 78)
    print("STAGE 1: hyperparameter selection on inner train/val (outer-test untouched)")
    print("=" * 78)
    results = []
    for cand in CANDIDATES:
        model = lgb.LGBMRegressor(n_estimators=MAX_ESTIMATORS, random_state=42, verbosity=-1,
                                  **cand["params"])
        model.fit(Xtr_inner_f, ytr_inner, eval_set=[(Xval_f, yval)],
                  eval_metric="l2",
                  callbacks=[lgb.early_stopping(EARLY_STOP_ROUNDS, verbose=False)])
        pred_val = model.predict(Xval_f, num_iteration=model.best_iteration_)
        corr_val = float(np.corrcoef(pred_val, yval)[0, 1])
        results.append((cand["name"], cand["params"], model.best_iteration_, corr_val))
        print(f"  {cand['name']:48s} best_iter={model.best_iteration_:5d}  inner-val corr={corr_val:+.4f}")

    best_name, best_params, best_iter, best_val_corr = max(results, key=lambda r: r[3])
    print(f"\nBest on inner validation: {best_name}  (inner-val corr={best_val_corr:+.4f}, "
          f"best_iter={best_iter})")

    print("\n" + "=" * 78)
    print("STAGE 2: refit winner on FULL outer-train, score ONCE on outer-test (the real number)")
    print("=" * 78)
    med_outer = Xtr_outer.median()
    Xtr_outer_f = Xtr_outer.fillna(med_outer)
    Xte_f = Xte.fillna(med_outer)

    # Refit with early stopping against a small tail slice of outer-train
    # itself (chronological, last 15%) to pick n_estimators for the final
    # fit - outer-test stays completely unseen until the single final
    # prediction below.
    refit_cut = outer_train["date"].quantile(0.85)
    refit_tr_mask = outer_train["date"] < refit_cut
    Xtr_refit = Xtr_outer[refit_tr_mask.values].fillna(med_outer)
    ytr_refit = ytr_outer[refit_tr_mask.values]
    Xval_refit = Xtr_outer[~refit_tr_mask.values].fillna(med_outer)
    yval_refit = ytr_outer[~refit_tr_mask.values]

    final_model = lgb.LGBMRegressor(n_estimators=MAX_ESTIMATORS, random_state=42, verbosity=-1,
                                    **best_params)
    final_model.fit(Xtr_refit, ytr_refit, eval_set=[(Xval_refit, yval_refit)],
                    eval_metric="l2",
                    callbacks=[lgb.early_stopping(EARLY_STOP_ROUNDS, verbose=False)])

    pred_tr = final_model.predict(Xtr_outer_f, num_iteration=final_model.best_iteration_)
    pred_te = final_model.predict(Xte_f, num_iteration=final_model.best_iteration_)
    corr_tr = float(np.corrcoef(pred_tr, ytr_outer)[0, 1])
    corr_te = float(np.corrcoef(pred_te, yte)[0, 1])

    print(f"\nFinal chosen config: {best_name}")
    print(f"  {best_params}, n_estimators={final_model.best_iteration_}")
    print(f"\nTRAIN correlation (full outer-train): {corr_tr:+.4f}")
    print(f"TEST correlation (outer-test, FINAL):  {corr_te:+.4f}")
    print(f"Gap: {corr_tr-corr_te:+.4f}")

    print("\n" + "=" * 78)
    print("COMPARISON")
    print("=" * 78)
    print("Shipped model's own documented held-out corr: +0.2883")
    print("diagnostic_check.py's fresh-fit-with-shipped-hyperparams held-out corr: +0.2959 (gap +0.0805)")
    print(f"This tuned model's held-out corr (SAME outer-test set):                {corr_te:+.4f} (gap {corr_tr-corr_te:+.4f})")
    delta = corr_te - 0.2959
    print(f"\nDelta vs diagnostic_check.py's baseline on the identical test set: {delta:+.4f}")
    if delta > 0.02:
        print("Real improvement - worth carrying these hyperparameters into an actual retrain "
              "(train() in race_speed_estimate.py) before shipping.")
    else:
        print("Not a real improvement - regularization tuning alone does not move the needle "
              "either. The gap diagnostic_check.py found is real but small enough that closing "
              "it does not translate into materially better held-out accuracy.")


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int, default=None, help="use only the N most recent races (smoke test)")
    args = ap.parse_args()
    run(limit=args.limit)
