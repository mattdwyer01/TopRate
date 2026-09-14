"""
wpr_passage_risk_vs_residual_test.py - closes the loop test 2 in
wpr_passage_quality_predictive_test.py left open: that script found
barrier+field_size forecast bad-passage risk with real skill (AUC 0.632
held-out, non-overfit). But wpr_race_speed_leader_prob_model.py already
taught this exact codebase tonight that a good AUC on an AUXILIARY task
does not automatically mean the signal helps the REAL target once
aggregated (that script's leader classifier scored AUC 0.745-0.758 but
still failed to improve race-shape prediction). Same discipline applied
here: does the predicted bad-passage RISK (cross-fit, leak-free, same
5-fold out-of-fold pattern) actually correlate with a runner's WPR
residual (today's wpr minus own trailing avg3), which is the thing that
would actually matter for the model?

NO EM DASHES policy: hyphens only.
"""
import numpy as np
import pandas as pd
from sklearn.model_selection import KFold
import lightgbm as lgb
from scipy import stats

LABELED_PKL = "/tmp/claude-0/-home-user-TopRate/76dfed62-bd31-52ea-bf89-3275bc38fea4/scratchpad/passage_labeled_form.pkl"
FEATS = ["barrier", "field_size"]


def build_rows(fh):
    labeled = fh.dropna(subset=["passage", "barrier", "residual"]).copy()
    labeled = labeled[labeled["passage"].isin(["bad", "good", "neutral"])]
    labeled["y"] = (labeled["passage"] == "bad").astype(int)
    labeled["race_key"] = (labeled["track"].astype(str) + "|" + labeled["date"].astype(str)
                            + "|" + labeled["raceNumber"].astype(str))
    labeled["field_size"] = labeled.groupby("race_key")["horse_lc"].transform("size")
    labeled = labeled[labeled["field_size"] >= 4]
    labeled = labeled.dropna(subset=FEATS + ["y", "residual"])
    return labeled.sort_values("date").reset_index(drop=True)


def run():
    fh = pd.read_pickle(LABELED_PKL)
    rows = build_rows(fh)
    print(f"rows: {len(rows):,}")

    cut = rows["date"].quantile(0.70)
    outer_train = rows[rows["date"] < cut].copy()
    outer_test = rows[rows["date"] >= cut].copy()
    print(f"outer-train: {len(outer_train):,}  outer-test: {len(outer_test):,}")

    # 5-fold out-of-fold cross-fit for outer-train (avoids the classifier
    # having seen its own training labels when we later correlate its
    # prediction against the SAME rows' residual)
    kf = KFold(n_splits=5, shuffle=True, random_state=42)
    oof_pred = np.zeros(len(outer_train))
    Xtr_all = outer_train[FEATS].to_numpy()
    ytr_all = outer_train["y"].to_numpy()
    for fold_idx, (tr_idx, val_idx) in enumerate(kf.split(Xtr_all)):
        m = lgb.LGBMClassifier(n_estimators=200, max_depth=3, num_leaves=8,
                                learning_rate=0.05, random_state=42, verbosity=-1)
        m.fit(Xtr_all[tr_idx], ytr_all[tr_idx])
        oof_pred[val_idx] = m.predict_proba(Xtr_all[val_idx])[:, 1]
    outer_train["bad_passage_risk"] = oof_pred
    print("5-fold out-of-fold predictions built for outer-train rows")

    final_model = lgb.LGBMClassifier(n_estimators=200, max_depth=3, num_leaves=8,
                                      learning_rate=0.05, random_state=42, verbosity=-1)
    final_model.fit(Xtr_all, ytr_all)
    outer_test["bad_passage_risk"] = final_model.predict_proba(outer_test[FEATS])[:, 1]
    print("outer-test predictions built from classifier fit on full outer-train")

    print("\n" + "=" * 78)
    print("Does predicted bad-passage-risk correlate with the WPR residual it's meant to flag?")
    print("=" * 78)
    for label, d in [("outer-train (out-of-fold)", outer_train), ("outer-test (held-out)", outer_test)]:
        corr = d[["bad_passage_risk", "residual"]].corr().iloc[0, 1]
        d = d.copy()
        d["risk_bucket"] = pd.qcut(d["bad_passage_risk"], 5, labels=[f"Q{i+1}" for i in range(5)], duplicates="drop")
        g = d.groupby("risk_bucket", observed=True)["residual"].agg(n="size", mean="mean")
        print(f"\n{label}: correlation(bad_passage_risk, residual) = {corr:+.4f}")
        print(g)

    q1 = outer_test[outer_test["bad_passage_risk"] <= outer_test["bad_passage_risk"].quantile(0.2)]["residual"]
    q5 = outer_test[outer_test["bad_passage_risk"] >= outer_test["bad_passage_risk"].quantile(0.8)]["residual"]
    t, p = stats.ttest_ind(q5, q1, equal_var=False)
    print(f"\nheld-out: highest-risk quintile vs lowest: diff={q5.mean()-q1.mean():+.3f}  t={t:.2f}  p={p:.4f}")
    print("(a USABLE signal needs this negative and significant - high predicted risk should")
    print(" mean a worse actual residual)")


if __name__ == "__main__":
    run()
