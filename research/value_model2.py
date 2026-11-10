"""Value model, second pass (10 Nov 2026): more inputs a market may misweigh, added one family at a time.
Same model, split, rule and commission as research/value_model.py (walk-forward 2024 / 2025 / 2026).
  bias   draw and on-pace lean of the EARLIER races at the same meeting, crossed with the runner's draw and style
  horse  the horse's own record against the price: overall, at this track, on wet ground, at this distance band; running style
  gear   blinkers on or first time, any gear change, apprentice claim, jockey upgrade or downgrade from last start
  trial  barrier trials and jump-outs since the last run
  pace   how many likely leaders are in the field, lone leader, the runner's style rank
  PYTHONPATH=. python research/value_model2.py [family ...]     (no argument = baseline, each family, then all)
"""
import os
import sys
import warnings

import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import value_model as VM  # noqa: E402
from betfair_bsp_test import load_bsp  # noqa: E402

warnings.filterwarnings("ignore")
CACHE = os.environ.get("VM2_CACHE", "/tmp/value_model2_frame.pkl")
FAM = {
    "bias": ["lean_prev", "lead_prev", "n_prev", "lean_x_bar", "lead_x_style"],
    "horse": ["h_ae", "h_trk_ae", "h_wet_ae", "h_dist_ae", "h_trk_n", "style", "close4", "r_style", "k_style"],
    "gear": ["blink", "blink_first", "gear_chg", "claim", "jk_up"],
    "trial": ["tr_n60", "tr_days", "tr_fin", "tr_won", "tr_since_run"],
    "pace": ["n_lead", "lone_lead", "style_gap_lead", "style_x_nr", "mean_style"],
}


def horse_asof(d, key, k=3.0):
    v, n = VM.asof_mean(d, key, "ae", k)
    return v, n


def build():
    r, T = VM.load(extra=["meeting_id", "position800m", "blinkers_on", "gear_changes", "weight_allowance"], keep_trials=True)
    r["date"] = pd.to_datetime(r.date)
    d = VM.features(r)
    g = d.groupby("horse_id")
    # ---- running style from earlier runs
    d["e0"] = pd.to_numeric(d.position800m, errors="coerce") / d.nr
    le = pd.concat([g.e0.shift(k) for k in range(1, 5)], axis=1)
    d["style"] = le.mean(axis=1)
    late = d.e0 - d.finpct
    d["close4"] = pd.concat([late.groupby(d.horse_id).shift(k) for k in range(1, 5)], axis=1).mean(axis=1)
    gk = d.groupby("race_id")
    d["r_style"] = d["style"] - gk["style"].transform("mean")
    d["k_style"] = gk["style"].rank(pct=True)
    # ---- pace: likely leaders in this field
    d["n_lead"] = (d["style"] < 0.25).groupby(d.race_id).transform("sum").astype(float)
    mn = gk["style"].transform("min")
    second = d["style"].where(d["style"] > mn).groupby(d.race_id).transform("min")
    d["style_gap_lead"] = d["style"] - mn
    d["lone_lead"] = ((d["style"] == mn) & ((second - mn) > 0.10)).astype(float).where(d["style"].notna())
    d["style_x_nr"] = d["style"] * d.nr
    d["mean_style"] = gk["style"].transform("mean")
    # ---- meeting lean from the earlier races of the day (race order = race_id inside the meeting, as in the shape study)
    top4 = d[d.positionFinish <= 4].groupby("race_id").barfrac.mean() - 0.5
    lead = d[d.e0 <= 1 / 3].groupby("race_id").finpct.mean()
    rest = d[d.e0 > 1 / 3].groupby("race_id").finpct.mean()
    R = d.groupby("race_id").agg(meeting_id=("meeting_id", "first"), date=("date", "first"), track=("track", "first"), nr=("nr", "first")).reset_index()
    R["lean"] = R.race_id.map(top4).where(R.nr >= 8)                 # + = wide draws filled the first four
    R["leadadv"] = (R.race_id.map(rest) - R.race_id.map(lead))        # + = on-pace runners finished better than the rest
    R["mk"] = R.meeting_id.fillna(-1).astype(str) + "|" + R.date.astype(str) + "|" + R.track.astype(str)
    R = R.sort_values(["mk", "race_id"])
    gm = R.groupby("mk")
    for c, o in (("lean", "lean_prev"), ("leadadv", "lead_prev")):
        cs = gm[c].transform(lambda x: x.fillna(0).cumsum().shift(1))
        cn = gm[c].transform(lambda x: x.notna().cumsum().shift(1))
        R[o] = (cs / cn).where(cn >= 2)
        R["n_" + o] = cn
    R["n_prev"] = R["n_lean_prev"].fillna(0)
    d = d.merge(R[["race_id", "lean_prev", "lead_prev", "n_prev"]], on="race_id", how="left")
    d["lean_x_bar"] = d.lean_prev * (d.barfrac - 0.5)
    d["lead_x_style"] = d.lead_prev * (0.5 - d["style"])
    # ---- the horse's own record against the price
    d["h_ae"], _ = horse_asof(d.assign(hk=d.horse_id.astype(str)), "hk")
    for nm, key in (("h_trk", d.horse_id.astype(str) + "|" + d.track.astype(str)), ("h_wet", d.horse_id.astype(str) + "|" + d.wet.astype(str)),
                    ("h_dist", d.horse_id.astype(str) + "|" + (d.distance / 400).round().astype(str))):
        v, n = horse_asof(d.assign(hk=key), "hk", 2.0)
        d[nm + "_ae"] = v
        if nm == "h_trk":
            d["h_trk_n"] = n
    # ---- gear, claim, jockey change quality
    g = d.groupby("horse_id")
    d["blink"] = (d.blinkers_on.astype(str).str.lower().isin(["true", "1", "1.0"])).astype(float)
    d["blink_first"] = ((d.blink == 1) & (g.blink.shift(1).fillna(0).groupby(d.horse_id).cummax() == 0)).astype(float)
    d["gear_chg"] = d.gear_changes.fillna("").astype(str).str.strip().str.len().gt(2).astype(float)
    d["claim"] = pd.to_numeric(d.weight_allowance, errors="coerce").fillna(0).clip(0, 4)
    d["jk_up"] = d.jk_win - g.jk_win.shift(1)
    # ---- trials and jump-outs since the last run
    T = T.copy()
    T["date"] = pd.to_datetime(T.date)
    for c in ("positionFinish",):
        T[c] = pd.to_numeric(T[c], errors="coerce")
    T["tn"] = T.groupby("race_id").horse_id.transform("size")
    T["tfin"] = (T.positionFinish - 1) / (T.tn - 1)
    T = T.dropna(subset=["horse_id", "date"]).sort_values("date")
    T["cnt"] = T.groupby("horse_id").cumcount() + 1
    q = d[["horse_id", "date"]].copy()
    q["_i"] = np.arange(len(q))
    q = q.sort_values("date")
    a = pd.merge_asof(q, T[["horse_id", "date", "tfin", "cnt"]].rename(columns={"date": "tdate"}).assign(date=lambda x: x.tdate), on="date", by="horse_id", allow_exact_matches=False)
    b60 = pd.merge_asof(q.assign(date=q.date - pd.Timedelta(days=60)), T[["horse_id", "date", "cnt"]], on="date", by="horse_id", allow_exact_matches=False)
    a = a.sort_values("_i")
    b60 = b60.sort_values("_i")
    d["tr_days"] = (d.date.values - a.tdate.values).astype("timedelta64[D]").astype(float)
    d.loc[a.tdate.isna().values, "tr_days"] = np.nan
    d["tr_n60"] = (a.cnt.fillna(0).values - b60.cnt.fillna(0).values)
    d["tr_fin"] = a.tfin.values
    d["tr_won"] = (a.tfin.values == 0).astype(float)
    d["tr_since_run"] = (d.tr_days < d.days).astype(float).where(d.tr_days.notna())
    d.loc[d.tr_since_run != 1, ["tr_fin", "tr_won"]] = np.nan
    return d


def main():
    if os.path.exists(CACHE):
        d = pd.read_pickle(CACHE)
    else:
        d = build()
        allf = sorted(set(sum(FAM.values(), [])))
        d, _ = VM.prepare(d, load_bsp(), extra_feats=allf)
        d.to_pickle(CACHE)
    base = VM.BASE + ["r_" + c for c in VM.REL] + ["k_" + c for c in VM.REL] + ["lpm", "fav", "pm_rank"]
    args = sys.argv[1:]
    variants = [("baseline", [])] + [(k, v) for k, v in FAM.items()] + [("all", sorted(set(sum(FAM.values(), []))))] if not args else \
        [("+".join(args), sorted(set(sum((FAM[a] for a in args), []))))]
    for name, extra in variants:
        print("\n\n@@@@@@@@@@ VARIANT %s (%d extra inputs) @@@@@@@@@@" % (name, len(extra)), flush=True)
        A = VM.walk(d, base + extra)
        if A is not None:
            A.to_pickle("/tmp/value_model2_%s.pkl" % name)


if __name__ == "__main__":
    main()
