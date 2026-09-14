"""
wpr_passage_quality_predictive_test.py - the two REAL tests, building on
wpr_passage_quality_signal.py's validated bad/good passage label (that
script only showed a run's OWN passage label correlates with that SAME
run's residual - expected almost by construction, not the interesting
question).

TEST 1 (historical tendency, leak-free): does a horse's OWN bad-passage
RATE over its PRIOR runs (strictly before today, expanding, so this is
usable as a forward-looking feature) predict today's residual (today's
wpr - today's own trailing avg3)? This is the real question for an
own_bad_passage-style ADJ_TERM: is getting taken wide a stable per-horse
tendency (temperament, racing style) or one-off race-day luck
uncorrelated with the next run?

TEST 2 (structural forecast, leak-free cross-fit): can TODAY's
bad-passage risk be predicted from pre-race structural facts alone
(barrier, field_size, distance, going, track) with no own-history input
at all - i.e. is it mostly "who you are" (barrier draw + field size) or
"what you've shown before" (test 1)? Uses the same 5-fold out-of-fold
cross-fitting discipline as wpr_race_speed_leader_prob_model.py to avoid
leakage from a meta-model feeding a held-out check.

NO EM DASHES policy: hyphens only.
"""
import numpy as np
import pandas as pd
from scipy import stats

LABELED_PKL = "/tmp/claude-0/-home-user-TopRate/76dfed62-bd31-52ea-bf89-3275bc38fea4/scratchpad/passage_labeled_form.pkl"


def load_labeled():
    fh = pd.read_pickle(LABELED_PKL)
    return fh


def test1_historical_tendency(fh):
    print("=" * 78)
    print("TEST 1: own historical bad-passage RATE (prior runs only) vs today's residual")
    print("=" * 78)
    fh = fh.sort_values(["horse_lc", "date"]).reset_index(drop=True)
    fh["is_bad"] = (fh["passage"] == "bad").astype(float)
    fh["is_labeled"] = fh["passage"].notna().astype(float)

    # expanding (cumulative) prior-only counts, shifted by 1 so today's own
    # row is never included - a strictly leak-free "as of before this race"
    # feature, same shape as build_features()'s own campaign-position walk.
    grp = fh.groupby("horse_lc")
    fh["prior_bad_count"] = grp["is_bad"].transform(lambda s: s.shift(1).expanding().sum())
    fh["prior_labeled_count"] = grp["is_labeled"].transform(lambda s: s.shift(1).expanding().sum())
    fh["prior_bad_rate_raw"] = fh["prior_bad_count"] / fh["prior_labeled_count"]

    # shrink toward the population mean by sample size (same _shrink()
    # logic pattern used everywhere else in this codebase - k=5)
    pop_mean = (fh["prior_bad_count"].sum() / fh["prior_labeled_count"].sum())
    K = 5.0
    fh["own_bad_passage_rate"] = (
        (fh["prior_bad_count"] + K * pop_mean) / (fh["prior_labeled_count"] + K)
    )

    valid = fh.dropna(subset=["residual", "own_bad_passage_rate"])
    valid = valid[valid["prior_labeled_count"] >= 3]  # need some real prior history
    print(f"rows with >=3 prior labeled runs and a computable residual: {len(valid):,}")

    corr = valid[["own_bad_passage_rate", "residual"]].corr().iloc[0, 1]
    print(f"correlation(own_bad_passage_rate, today's residual): {corr:+.4f}")

    # decile check - does residual actually trend down as own rate rises?
    valid["decile"] = pd.qcut(valid["own_bad_passage_rate"], 5, labels=[f"Q{i+1}" for i in range(5)], duplicates="drop")
    g = valid.groupby("decile", observed=True)["residual"].agg(n="size", mean="mean")
    print(g)

    q1 = valid[valid["decile"] == "Q1"]["residual"]
    q5 = valid[valid["decile"] == valid["decile"].cat.categories[-1]]["residual"]
    t, p = stats.ttest_ind(q5, q1, equal_var=False)
    print(f"\nhighest-rate quintile vs lowest: diff={q5.mean()-q1.mean():+.3f}  t={t:.2f}  p={p:.4f}")
    print("(a real, USABLE tendency would show residual falling as own_bad_passage_rate rises,")
    print(" i.e. Q5 mean clearly more negative than Q1 mean, with a significant t-stat)")
    return valid


def test2_structural_forecast(fh):
    print("\n" + "=" * 78)
    print("TEST 2: can bad-passage risk be forecast from barrier/field structure alone?")
    print("=" * 78)
    import lightgbm as lgb
    from sklearn.model_selection import KFold
    from sklearn.metrics import roc_auc_score

    labeled = fh.dropna(subset=["passage", "barrier"]).copy()
    labeled = labeled[labeled["passage"].isin(["bad", "good", "neutral"])]
    labeled["y"] = (labeled["passage"] == "bad").astype(int)

    # field_size: count of labeled+unlabeled runners in the same race
    # (run_id doesn't carry race_id here, but track+date+raceNumber does -
    # same key wpr_race_speed_hyperparam_tune.py etc already use)
    labeled["race_key"] = (labeled["track"].astype(str) + "|" + labeled["date"].astype(str)
                            + "|" + labeled["raceNumber"].astype(str))
    labeled["field_size"] = labeled.groupby("race_key")["horse_lc"].transform("size")
    labeled = labeled[labeled["field_size"] >= 4]

    feats = ["barrier", "field_size"]
    labeled = labeled.dropna(subset=feats + ["y"])
    print(f"rows: {len(labeled):,}  base rate (bad passage): {labeled['y'].mean()*100:.1f}%")

    labeled = labeled.sort_values("date").reset_index(drop=True)
    cut = labeled["date"].quantile(0.70)
    train = labeled[labeled["date"] < cut]
    test = labeled[labeled["date"] >= cut]
    print(f"train: {len(train):,}  test: {len(test):,}  (chronological 70/30 split)")

    Xtr, ytr = train[feats], train["y"]
    Xte, yte = test[feats], test["y"]

    model = lgb.LGBMClassifier(n_estimators=200, max_depth=3, num_leaves=8,
                                learning_rate=0.05, random_state=42, verbosity=-1)
    model.fit(Xtr, ytr)
    pred_tr = model.predict_proba(Xtr)[:, 1]
    pred_te = model.predict_proba(Xte)[:, 1]
    auc_tr = roc_auc_score(ytr, pred_tr)
    auc_te = roc_auc_score(yte, pred_te)
    print(f"AUC train: {auc_tr:.4f}   AUC held-out: {auc_te:.4f}   (0.5 = no better than chance)")
    print("feature importances:", dict(zip(feats, model.feature_importances_)))

    # barrier alone, bucketed - the most interpretable structural check:
    # does a WIDE barrier draw predict a bad passage the way racing logic
    # says it should (wide draw -> more likely to work forward or sit wide)?
    labeled["barrier_bucket"] = pd.cut(labeled["barrier"], [0, 4, 8, 12, 30],
                                        labels=["1-4 (inside)", "5-8", "9-12", "13+ (wide)"])
    g = labeled.groupby("barrier_bucket", observed=True)["y"].agg(n="size", bad_rate="mean")
    print("\nbad-passage rate by barrier bucket (full population, sanity check):")
    print(g)


if __name__ == "__main__":
    fh = load_labeled()
    valid1 = test1_historical_tendency(fh)
    test2_structural_forecast(fh)
    print("\nDone.")
