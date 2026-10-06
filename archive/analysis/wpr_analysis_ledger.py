"""
wpr_analysis_ledger.py - persistent post-race analysis record, one row per
resulted runner, for model-drift review over time.

The dashboard's Post Race tab computes variance + verdict on the fly and stores
nothing. This script writes that analysis to a growing CSV so it can be sorted,
filtered, pivoted, and trended later - the thing you need to answer "is the
model drifting / does it need a retrain" rather than eyeballing one race.

ONE row per resulted runner that has a projection and an actual:
  date, venue, race_no, distance, going, race_class, field_size, prize,
  tab, horse, projection, actual, variance (actual - projection),
  offset_miss (actual - (projection + calib_offset)), conf, proj_rank,
  finish, won, verdict, void_reason, comment_video, comment_steward

VERDICT mirrors the dashboard exactly (shared wpr_void logic, same bands):
  void        - strong/weak excuse on an underperformance (incident)
  unexplained - extreme miss (<= -20) with no comment (likely uncaptured incident)
  model_low   - ran 4+ above projection (rated too low)
  model_high  - ran 4+ below projection (rated too high)
  ok          - within +/- 4 of projection
The +/- 4 band and the labels match _classifyVariance in the dashboard so the
ledger and the screen agree.

USAGE
  python wpr_analysis_ledger.py                 # rebuild ledger from scratch
  python wpr_analysis_ledger.py --offset 2.24   # set calibration offset used
  python wpr_analysis_ledger.py --summary       # also print a drift summary

Output: wpr_analysis_ledger.csv (overwritten each run; it is derived from
toprate_runners.csv which is the source of truth, so a full rebuild every cycle
is correct and keeps it current as actuals/comments settle).

NO EM DASHES policy: hyphens only.
"""

import sys
import pandas as pd
import numpy as np
from wpr_void import is_void

RUNNERS = "toprate_runners.csv"
HISTORY = "wpr_form_history.csv"
LEDGER = "wpr_analysis_ledger.csv"

OK_BAND = 4.0            # matches dashboard _classifyVariance Model OK band
UNEXPLAINED_MISS = -20.0  # matches dashboard unexplained guard


def _clean(v):
    if v is None or pd.isna(v):
        return ""
    s = str(v).strip()
    return "" if s.lower() in ("nan", "none", "<na>") else s


def classify(variance, offset_miss, cv, cs):
    """Verdict + void reason, mirroring the dashboard. variance is the plain
    actual-minus-projection; offset_miss is against projection+offset (used for
    the void/incident tests, as on the dashboard)."""
    has_comment = bool(_clean(cv) or _clean(cs))
    if abs(variance) <= OK_BAND:
        return ("ok", "")
    if variance < 0:
        # underperformance - test for void / incident first
        v, reason = is_void(offset_miss, cv, cs)
        if v:
            return ("void", reason)
        if offset_miss <= UNEXPLAINED_MISS and not has_comment:
            return ("unexplained", "no comment - likely incident")
        return ("model_high", "")   # rated too high
    return ("model_low", "")        # rated too low


def main():
    args = sys.argv
    # Offset: explicit flag wins; otherwise read the live model's calib_offset
    # from config so the ledger's offset_miss matches the deployed model.
    if "--offset" in args:
        offset = float(args[args.index("--offset") + 1])
    else:
        offset = 2.24
        try:
            import json
            cfg = json.load(open("wpr_models/config.json"))
            offset = float(cfg.get("calib_offset", offset))
        except Exception:
            pass
    do_summary = "--summary" in args

    d = pd.read_csv(RUNNERS, low_memory=False)
    d = d[d.get("resulted") == 1].copy()
    for c in ["wprp_proj", "wpr_actual", "wprp_conf", "wprp_rank",
              "finish_position", "won", "distance", "prize_money", "race"]:
        if c in d.columns:
            d[c] = pd.to_numeric(d[c], errors="coerce")
    d = d.dropna(subset=["wprp_proj", "wpr_actual"]).copy()

    # Comments may not yet be backfilled into the runners CSV (the self-healing
    # fill runs on the daily cycle). Join them from the form history so the
    # ledger has comment-based verdicts now. Where the CSV already has them,
    # the CSV value wins; otherwise fall back to the history match.
    try:
        fh = pd.read_csv(HISTORY, low_memory=False,
                         usecols=["horse", "date", "comments_video",
                                  "comments_steward", "scrape_date"])
        fh["date"] = pd.to_datetime(fh["date"], errors="coerce")
        fh["scrape_date"] = pd.to_datetime(fh["scrape_date"], errors="coerce")
        fh = fh.sort_values("scrape_date").drop_duplicates(["horse", "date"], keep="last")
        fh["hkey"] = (fh["horse"].astype(str).str.lower().str.strip() + "|" +
                      fh["date"].dt.strftime("%Y-%m-%d"))
        vmap = {k: v for k, v in zip(fh["hkey"], fh["comments_video"]) if _clean(v)}
        smap = {k: v for k, v in zip(fh["hkey"], fh["comments_steward"]) if _clean(v)}
        dt = pd.to_datetime(d["date"], errors="coerce")
        d["hkey"] = (d["horse"].astype(str).str.lower().str.strip() + "|" +
                     dt.dt.strftime("%Y-%m-%d"))
        for col, mp in [("comments_video", vmap), ("comments_steward", smap)]:
            if col not in d.columns:
                d[col] = np.nan
            d[col] = d[col].astype(object)
            empty = d[col].map(lambda x: not _clean(x))
            d.loc[empty, col] = d.loc[empty, "hkey"].map(mp)
    except Exception as e:
        print(f"  (comment join from history skipped: {e})")

    # field size per race (count of runners in the resulted race)
    fs = d.groupby("race_id")["horse"].transform("size")
    d["field_size"] = fs

    d["variance"] = d["wpr_actual"] - d["wprp_proj"]
    d["offset_miss"] = d["wpr_actual"] - (d["wprp_proj"] + offset)

    verdicts, reasons = [], []
    for _, r in d.iterrows():
        v, reason = classify(r["variance"], r["offset_miss"],
                             r.get("comments_video"), r.get("comments_steward"))
        verdicts.append(v)
        reasons.append(reason)
    d["verdict"] = verdicts
    d["void_reason"] = reasons

    out = pd.DataFrame({
        "date": d["date"].astype(str).str[:10],
        "venue": d["venue"],
        "race_no": d.get("race"),
        "distance": d.get("distance"),
        "going": d.get("going"),
        "race_class": d.get("race_class"),
        "field_size": d["field_size"],
        "prize": d.get("prize_money"),
        "tab": d.get("tab_number"),
        "horse": d["horse"],
        "projection": d["wprp_proj"].round(1),
        "actual": d["wpr_actual"].round(1),
        "variance": d["variance"].round(1),
        "offset_miss": d["offset_miss"].round(1),
        "conf": d.get("wprp_conf"),
        "proj_rank": d.get("wprp_rank"),
        "finish": d.get("finish_position"),
        "won": d.get("won"),
        "verdict": d["verdict"],
        "void_reason": d["void_reason"],
        "comment_video": d.get("comments_video", pd.Series(index=d.index)).map(_clean),
        "comment_steward": d.get("comments_steward", pd.Series(index=d.index)).map(_clean),
    })
    out = out.sort_values(["date", "venue", "race_no", "proj_rank"])
    out.to_csv(LEDGER, index=False)
    print(f"wrote {LEDGER}: {len(out):,} resulted runners (offset {offset:+.2f})")

    vc = out["verdict"].value_counts()
    print("\nverdict counts:")
    for k in ["ok", "model_low", "model_high", "void", "unexplained"]:
        print(f"  {k:12s} {int(vc.get(k, 0)):5d}")

    if do_summary:
        # clean = exclude void + unexplained (incidents, not model error)
        clean = out[~out["verdict"].isin(["void", "unexplained"])]
        print(f"\n== drift summary (clean runs only, n={len(clean)}) ==")
        print(f"  mean variance {clean['variance'].mean():+.2f}  "
              f"MAE {clean['variance'].abs().mean():.2f}")
        # by month - the key drift view
        clean = clean.copy()
        clean["ym"] = pd.to_datetime(clean["date"], errors="coerce").dt.to_period("M").astype(str)
        print("\n  by month (clean mean variance / MAE / n):")
        for ym, g in clean.groupby("ym"):
            print(f"    {ym}: {g['variance'].mean():+.2f} / {g['variance'].abs().mean():.2f} / {len(g)}")
        print("\n  (watch for mean variance drifting away from 0 month-on-month")
        print("   or MAE climbing - either signals the model may need a retrain)")


if __name__ == "__main__":
    main()
