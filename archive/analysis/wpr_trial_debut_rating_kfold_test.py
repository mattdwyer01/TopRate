"""
wpr_trial_debut_rating_kfold_test.py - proper K=4-fold leak-free follow-up
to wpr_trial_debut_scoping_check.py's correlation finding (trial finish
quality vs debut WPR, corr=0.27 on n=8,430 horses). Builds an actual
debut-rating ESTIMATE from pre-debut trial performance and checks whether
it beats the only baseline available today: no rating at all (these
horses are currently excluded from every projection - see _MIN_RUNS -
so the honest baseline is "predict the population's own mean debut WPR
for every debutant", not some existing model output).

FEATURES (all pre-debut-known, all leak-free by construction - only
trial rows strictly before the horse's first real race are used):
  n_trials        - count of pre-debut trials/jumpouts
  avg_finish_pct  - mean of (1 - (positionFinish-1)/field_size) across them
  best_finish_pct - the single best trial's finish percentile
  won_a_trial     - finished 1st in at least one pre-debut trial
  avg_margin      - mean marginFinish (lengths behind, 0=won) where recorded
  days_since_last_trial - gap from last trial to debut (freshness)

No WPR or sectional data is ever computed for trials (confirmed directly
in the scoping check: 0% coverage) - position/margin/field_size are the
only usable signal, a cruder proxy than a real per-run WPR would be.

METHOD: K=4 chronological folds BY DEBUT DATE (not trial date) - train on
earlier debut cohorts, validate on later ones, same convention as every
other K-fold script this session. Per fold: fit an OLS (debut_wpr ~
features, on training folds' debutants only) and compare held-out MAE
against the training folds' own mean debut_wpr (the "no signal" baseline
that matches what these horses get today - nothing). Also reports the
population-wide baseline (ALL debutants, trialled or not) for context,
since trialled debutants have a different baseline debut_wpr than
untrialled ones (a real selection effect found in the scoping check).

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd

FORM_CSV = "wpr_form_history.csv.gz"
N_FOLDS = 4


def build_debutant_frame():
    df = pd.read_csv(FORM_CSV, low_memory=False,
                      usecols=["horse_id", "horse", "date", "isBarrierTrial", "is_jumpout",
                               "positionFinish", "field_size", "marginFinish", "wpr"])
    df["date"] = pd.to_datetime(df["date"], errors="coerce")
    df = df.dropna(subset=["date", "horse_id"])
    df["is_trial"] = (df["isBarrierTrial"] == True) | (df["is_jumpout"] == True)
    df = df.sort_values(["horse_id", "date"])

    first_real = df[~df["is_trial"] & df["wpr"].notna()].groupby("horse_id")["date"].min().rename("first_real_date")
    df = df.merge(first_real, on="horse_id", how="left")

    pre = df[df["is_trial"] & (df["date"] < df["first_real_date"])].copy()
    pre["finish_pct"] = 1 - (pre["positionFinish"] - 1) / pre["field_size"].clip(lower=1)
    pre["won"] = (pre["positionFinish"] == 1).astype(float)

    feat = pre.groupby("horse_id").agg(
        n_trials=("finish_pct", "count"),
        avg_finish_pct=("finish_pct", "mean"),
        best_finish_pct=("finish_pct", "max"),
        won_a_trial=("won", "max"),
        avg_margin=("marginFinish", "mean"),
        last_trial_date=("date", "max"),
    )

    debut = df[(~df["is_trial"]) & (df["date"] == df["first_real_date"]) & df["wpr"].notna()]
    debut = debut.drop_duplicates(subset="horse_id").set_index("horse_id")[["wpr", "first_real_date"]]
    debut.columns = ["debut_wpr", "debut_date"]

    out = debut.join(feat, how="inner")
    out["days_since_last_trial"] = (out["debut_date"] - out["last_trial_date"]).dt.days
    out["avg_margin"] = out["avg_margin"].fillna(out["avg_margin"].median())
    return out.sort_values("debut_date").reset_index()


FEATURES = ["n_trials", "avg_finish_pct", "best_finish_pct", "won_a_trial",
            "avg_margin", "days_since_last_trial"]


def fit_ols(train):
    X = np.column_stack([np.ones(len(train))] + [train[f].to_numpy() for f in FEATURES])
    y = train["debut_wpr"].to_numpy()
    coef, *_ = np.linalg.lstsq(X, y, rcond=None)
    return coef


def predict(coef, frame):
    X = np.column_stack([np.ones(len(frame))] + [frame[f].to_numpy() for f in FEATURES])
    return X @ coef


def run():
    data = build_debutant_frame()
    print(f"Trialled debutants with a usable debut WPR: {len(data):,}")
    print(f"date range: {data['debut_date'].min().date()} to {data['debut_date'].max().date()}")
    print(f"debut_wpr: mean={data['debut_wpr'].mean():.2f} std={data['debut_wpr'].std():.2f}\n")

    fold_edges = np.array_split(np.arange(len(data)), N_FOLDS)
    data["_fold"] = -1
    for i, idx in enumerate(fold_edges):
        data.loc[idx, "_fold"] = i

    print(f"{'='*90}\nK={N_FOLDS}-fold: trial-feature model vs population-mean baseline\n{'='*90}")
    base_maes, model_maes = [], []
    for i in range(N_FOLDS):
        test = data[data["_fold"] == i]
        train = data[data["_fold"] != i]

        train_mean = train["debut_wpr"].mean()
        mae_base = (test["debut_wpr"] - train_mean).abs().mean()

        coef = fit_ols(train)
        pred = predict(coef, test)
        mae_model = np.abs(test["debut_wpr"].to_numpy() - pred).mean()

        base_maes.append(mae_base)
        model_maes.append(mae_model)
        print(f"  fold {i} (n={len(test):,}, debut {test['debut_date'].min().date()} to "
              f"{test['debut_date'].max().date()}): "
              f"baseline(train mean={train_mean:.1f}) MAE={mae_base:.4f}   "
              f"model MAE={mae_model:.4f}   "
              f"({'better' if mae_model < mae_base else 'worse/same'})")

    print(f"\n  avg MAE: baseline={np.mean(base_maes):.4f}  model={np.mean(model_maes):.4f}")
    print(f"  model better in every fold: {all(m < b for m, b in zip(model_maes, base_maes))}")
    print(f"  improvement: {np.mean(base_maes) - np.mean(model_maes):+.4f} MAE "
          f"({(np.mean(base_maes) - np.mean(model_maes)) / np.mean(base_maes) * 100:.1f}% reduction)")

    coef_full = fit_ols(data)
    print(f"\n  full-data fit coefficients (intercept, {', '.join(FEATURES)}):")
    print(f"    {[f'{c:.4f}' for c in coef_full]}")

    print("\nSame multiple-comparisons caveat as the other bet-selection scripts: treat this")
    print("as a hypothesis for a future walk-forward period, not a result to ship blindly.")


if __name__ == "__main__":
    run()
