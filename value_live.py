"""Forward test of the value model (the correction to the Betfair starting price), 10 Nov 2026. Research only: it places no bets.

The model in value_model/ is LOCKED (trained on races to 8 Oct 2026, see `lock`). Every race after that date is out of sample.
Once Betfair's price file and the result pages for a day are in, `score` builds that day's inputs exactly as the backtest
did (research/value_model2.build on the results files plus TopRate's stored result pages after 8 Oct), applies the fixed rule
(model chance x net return > 1.00 and Betfair starting price under $30, commission 10% NSW / 8% elsewhere) and writes
data/value_log/<date>.csv.gz (every scored runner, bet flag, result). `report` writes value_report.md.

The Betfair starting price is only known at the jump, so this log answers "does the locked model find value at the Betfair
price on new races". It is not yet a placeable rule: placing it needs a price estimate before the jump and a minimum-price bet.

Pass / fail, fixed before any forward day was scored:
  first read at 2,000 settled bets, final read at 6,000. Pass = return after commission is above zero WITHOUT the 10 best
  winners, and the bets win more often than the Betfair price implied. Anything else = stop.

  PYTHONPATH=. python value_live.py lock              train and save the locked model (needs /tmp/value_model3_frame.pkl, see research/value_model3.py build)
  PYTHONPATH=. python value_live.py score [--redo]    score every day after 8 Oct 2026 that has prices and results and no log file yet
  python value_live.py report
"""
import glob
import gzip
import json
import os
import sys
import warnings

import numpy as np
import pandas as pd

warnings.filterwarnings("ignore")
ROOT = os.path.dirname(os.path.abspath(__file__))
MODEL_DIR = os.path.join(ROOT, "value_model")
LOG_DIR = os.path.join(ROOT, "data", "value_log")
REPORT = os.path.join(ROOT, "value_report.md")
SUMMARY = os.path.join(ROOT, "value_summary.json")
RC_RESULTS = os.path.join(ROOT, "race_results_2026_rc.csv.gz")
TRAINED_TO = "2026-10-08"            # last race date the model saw
FIT_END = "2026-07-01"               # fit before this, early stop on FIT_END .. TRAINED_TO (the walk-forward recipe)
SEEDS = tuple(range(1, 11))
DROP = ["lead_prev", "lead_x_style"]  # need same-day 800m positions, which do not exist before a race
BSP_MAX, EV_MIN = 30.0, 1.0
GATES = (2000, 6000)


def _research():
    sys.path.insert(0, os.path.join(ROOT, "research"))
    import value_model as VM
    import value_model2 as VM2
    import value_model3 as VM3
    return VM, VM2, VM3


# ----------------------------------------------------------------------------------------------------------------------
# lock

def cmd_lock():
    import lightgbm as lgb
    VM, VM2, VM3 = _research()
    d = pd.read_pickle(VM3.CACHE)
    sp = d[d.src == "sp"]
    sl = np.linspace(0.9, 1.3, 41)
    a = float(sl[int(np.argmax([np.log(VM.soft(sp, x * sp.lpm.values)[sp.won.values == 1]).mean() for x in sl]))])
    d.loc[d.src == "sp", "lpm"] = np.log(VM.soft(sp, a * sp.lpm.values))      # starting prices straightened, as in the "precal" variant
    FE = [c for c in VM3.FE_ALL if c not in DROP]
    tr, va = d[d.ds < FIT_END], d[d.ds >= FIT_END]
    s, st = VM.ginfo(tr)
    y, yv = tr.won.values, va.won.values

    def obj(preds, ds):
        z = preds - np.repeat(np.maximum.reduceat(preds, st), s)
        e = np.exp(z)
        p = e / np.repeat(np.add.reduceat(e, st), s)
        return p - y, np.maximum(p * (1 - p), 1e-6)

    def ev(preds, ds):
        return "ll", float(np.log(VM.soft(va, preds)[yv == 1].clip(1e-12)).mean()), True
    os.makedirs(MODEL_DIR, exist_ok=True)
    trees, cv = [], []
    for seed in SEEDS:
        P = dict(learning_rate=0.02, num_leaves=8, min_data_in_leaf=400, feature_fraction=0.5, bagging_fraction=0.7, bagging_freq=1, lambda_l2=50, verbose=-1,
                 objective=obj, metric="None", seed=seed, num_threads=4)
        dtr = lgb.Dataset(tr[FE], label=y, init_score=tr.lpm.values)
        dva = lgb.Dataset(va[FE], label=yv, init_score=va.lpm.values, reference=dtr)
        m = lgb.train(P, dtr, num_boost_round=3000, valid_sets=[dva], feval=ev, callbacks=[lgb.early_stopping(150, verbose=False)])
        m.save_model(os.path.join(MODEL_DIR, "seed%d.txt" % seed), num_iteration=m.best_iteration)
        trees.append(int(m.best_iteration))
        cv.append(m.predict(va[FE], num_iteration=m.best_iteration))
        print("seed %d: %d trees" % (seed, m.best_iteration), flush=True)
    c = np.mean(cv, axis=0)
    w = yv == 1
    gain = np.log(VM.soft(va, va.lpm.values + c)[w]) - va.lpm.values[w]
    x = VM3.bets(va, c)
    meta = dict(features=FE, seeds=list(SEEDS), trees=trees, sp_slope=a, fit_end=FIT_END, trained_to=TRAINED_TO, fit_races=int(tr.race_id.nunique()),
                stop_races=int(va.race_id.nunique()), stop_gain_over_betfair=round(float(gain.mean()), 5), stop_bets=int(len(x)),
                stop_roi_pct=round(float(100 * x.pnl.mean()), 2) if len(x) else None,
                note="stop_* figures are on the early-stopping window, so they are in sample for the tree counts")
    json.dump(meta, open(os.path.join(MODEL_DIR, "meta.json"), "w"), indent=1)
    print(json.dumps({k: v for k, v in meta.items() if k != "features"}, indent=1))


# ----------------------------------------------------------------------------------------------------------------------
# races after 8 Oct 2026, put into the results files' columns

def recent_rows():
    """Every race after 8 Oct 2026 from TopRate's stored result pages (data/tr_results) as extra history / target rows in the results files' columns.
    Those pages are the same source as the older results files: TopRate ids and names, the plain rating of EVERY runner, 800m position, steward and
    video comments, starting price. (The first version read the racing.com results, where a quarter of runs had no rating; races holding such a horse
    lost 41% in the first forward month, so the source was switched on 11 Nov 2026 and the month scored again.) Sire comes from the older results
    files, age and sex from runners.csv. Races are keyed by meeting and race number so the day's draw lean reads the earlier races in order."""
    from rc_field_rows import norm_venue
    rows = []
    for f in sorted(glob.glob(os.path.join(ROOT, "data", "tr_results", "*.json.gz"))):
        d = os.path.basename(f)[:10]
        if d <= TRAINED_TO:
            continue
        with gzip.open(f, "rt") as fh:
            races = json.load(fh).get("races", {})
        for rid, race in races.items():
            for u in race.get("runners") or []:
                if u.get("horseId") is None:
                    continue
                rows.append(dict(race_id_tr=rid, date=d, horse_id=u["horseId"], horse=u.get("horse"), track=race.get("venue"), race_no=race.get("race"),
                                 distance=race.get("distance"), going=race.get("going"), race_class=race.get("class"), wpr=u.get("wpr"),
                                 weightCarried=u.get("weightCarried"), barrier=u.get("barrier"), priceStarting=u.get("priceStarting"),
                                 positionFinish=u.get("positionFinish"), marginFinish=u.get("marginFinish"), position800m=u.get("position800m"),
                                 jockey=u.get("jockey"), trainer=u.get("trainer"), comments_steward=u.get("commentsSteward"), comments_video=u.get("commentsVideo")))
    rc = pd.DataFrame(rows)
    for c in ("horse_id", "race_no", "wpr", "position800m"):
        rc[c] = pd.to_numeric(rc[c], errors="coerce")
    old = pd.concat([pd.read_csv(f, usecols=["horse_id", "sire", "track", "horse_sex"], low_memory=False) for f in sorted(glob.glob(os.path.join(ROOT, "race_results_202[3-6].csv.gz")))])
    names = {norm_venue(t): t for t in old.track.dropna().unique()}
    rc["track"] = rc.track.map(lambda t: names.get(norm_venue(t), t))
    last = old.drop_duplicates("horse_id", keep="last").set_index("horse_id")
    rc["sire"] = rc.horse_id.map(old.dropna(subset=["sire"]).drop_duplicates("horse_id", keep="last").set_index("horse_id").sire)
    rn = pd.read_csv(os.path.join(ROOT, "runners.csv"), usecols=["date", "horse_id", "horse_age", "horse_sex"], low_memory=False)
    rn = rn[rn.date > TRAINED_TO].drop_duplicates(["date", "horse_id"], keep="last")
    rc = rc.merge(rn, on=["date", "horse_id"], how="left")
    rc["horse_sex"] = rc.horse_sex.fillna(rc.horse_id.map(last.horse_sex))
    R = rc.groupby("race_id_tr").agg(date=("date", "first"), track=("track", "first"), no=("race_no", "first")).reset_index()
    R["no"] = R.no.fillna(50 + R.groupby(["date", "track"]).race_id_tr.rank())
    R["mk"] = R.date + "|" + R.track.astype(str)
    R["meeting_id"] = 9_000_000 + R.mk.map({k: i for i, k in enumerate(sorted(R.mk.unique()))})
    R["race_id"] = (8_000_000_000_000 + (R.meeting_id - 9_000_000) * 1000 + R.no.round() * 10 + R.groupby(["mk", "no"]).cumcount()).astype("int64")
    rc = rc.merge(R[["race_id_tr", "meeting_id", "race_id"]], on="race_id_tr")
    rc["isBarrierTrial"], rc["is_jumpout"] = False, False
    for c in ("blinkers_on", "gear_changes", "weight_allowance"):
        rc[c] = np.nan
    print("result-page rows after %s: %d in %d races (%s to %s), rating for %.0f%%, 800m position %.0f%%, sire %.0f%%, age %.0f%%" % (
        TRAINED_TO, len(rc), rc.race_id.nunique(), rc.date.min(), rc.date.max(), 100 * rc.wpr.notna().mean(), 100 * rc.position800m.notna().mean(),
        100 * rc.sire.notna().mean(), 100 * rc.horse_age.notna().mean()))
    return rc


def build_recent():
    """the backtest's feature frame for races after 8 Oct 2026 with a Betfair price for every runner"""
    VM, VM2, VM3 = _research()
    import betfair_prices as bf
    d = VM2.build(more=recent_rows())
    d = d[d.date > TRAINED_TO].copy()
    d["ds"] = d.date.dt.strftime("%Y-%m-%d")
    d["hn"] = d.horse.map(bf.norm)
    b = bf.load(sorted(set(d.ds.str[:7])))
    d = d.merge(b.rename(columns={"date": "ds"})[["ds", "hn", "bsp", "win_lose"]], on=["ds", "hn"], how="left")
    g = d.groupby("race_id")
    d["book"] = g.bsp.transform(lambda x: (1 / x).sum())
    n_all = d.race_id.nunique()
    priced = g.bsp.transform(lambda x: x.notna().all())
    d = d[priced & d.book.between(0.95, 1.15) & (g.won.transform("sum") == 1) & (d.nr >= 5)].copy()
    d = d.sort_values(["date", "race_id"]).reset_index(drop=True)
    d["nsw"] = VM3.nsw_flag(d.track)
    d["comm"] = np.where(d.nsw, bf.COMM_NSW, bf.COMM_OTHER)
    d["pm"] = (1 / d.bsp) / d.book
    d["lpm"] = np.log(d.pm)
    gk = d.groupby("race_id")
    for c in VM.REL:
        d["r_" + c] = d[c] - gk[c].transform("mean")
        d["k_" + c] = gk[c].rank(pct=True)
    d["fav"] = (d.pm == gk.pm.transform("max")).astype(float)
    d["pm_rank"] = gk.pm.rank(ascending=False)
    print("races after %s: %d, with a Betfair price for every runner and a clean book: %d" % (TRAINED_TO, n_all, d.race_id.nunique()))
    return d


def model_correction(d):
    import lightgbm as lgb
    meta = json.load(open(os.path.join(MODEL_DIR, "meta.json")))
    X = d[meta["features"]]
    return np.mean([lgb.Booster(model_file=os.path.join(MODEL_DIR, "seed%d.txt" % s)).predict(X) for s in meta["seeds"]], axis=0)


def cmd_score(redo=False):
    VM, VM2, VM3 = _research()
    os.makedirs(LOG_DIR, exist_ok=True)
    d = build_recent()
    have = set() if redo else {os.path.basename(f)[:10] for f in glob.glob(os.path.join(LOG_DIR, "*.csv.gz"))}
    d = d[~d.ds.isin(have)]
    if d.empty:
        print("nothing new to score")
        return
    c = model_correction(d)
    d["p_model"] = VM.soft(d, d.lpm.values + c)
    d["value_pts"] = 5 * (np.log(d.p_model) - d.lpm)
    d["ev"] = d.p_model * (1 + (d.bsp - 1) * (1 - d.comm))
    d["bet"] = ((d.ev > EV_MIN) & (d.bsp < BSP_MAX)).astype(int)
    d["pnl"] = np.where(d.bet == 1, d.won * (d.bsp - 1) * (1 - d.comm) - (1 - d.won), 0.0)
    d["scored_at"] = pd.Timestamp.now("UTC").strftime("%Y-%m-%dT%H:%MZ")
    cols = ["ds", "track", "race_id", "race_id_tr", "horse", "horse_id", "barrier", "nr", "bsp", "comm", "pm", "p_model", "value_pts", "ev", "bet", "won", "pnl", "scored_at"]
    for day, x in d.groupby("ds"):
        x[[k for k in cols if k in x.columns]].round(5).to_csv(os.path.join(LOG_DIR, day + ".csv.gz"), index=False)
        print("%s: %d races, %d runners, %d bets, %+.1f units" % (day, x.race_id.nunique(), len(x), int(x.bet.sum()), x.pnl.sum()))


# ----------------------------------------------------------------------------------------------------------------------
# report

def _line(x):
    n = len(x)
    if n == 0:
        return dict(bets=0)
    o = np.sort(x.pnl.values)[::-1]
    return dict(bets=n, wins=int(x.won.sum()), win_pct=round(100 * x.won.mean(), 2), model_pct=round(100 * x.p_model.mean(), 2), betfair_pct=round(100 * x.pm.mean(), 2),
                avg_price=round(float(x.bsp.mean()), 2), profit_units=round(float(x.pnl.sum()), 1), roi_pct=round(100 * x.pnl.mean(), 1),
                roi_ex10_pct=round(100 * (x.pnl.sum() - o[:10].sum()) / n, 1))


def cmd_report():
    fs = sorted(glob.glob(os.path.join(LOG_DIR, "*.csv.gz")))
    if not fs:
        print("no log files")
        return
    a = pd.concat([pd.read_csv(f) for f in fs], ignore_index=True)
    x = a[a.bet == 1]
    w = a[a.won == 1]
    gain = np.log(w.p_model) - np.log(w.pm)
    tot = _line(x)
    days = x.groupby("ds").pnl.agg(["sum", "size"])
    rng = np.random.default_rng(1)
    idx = rng.integers(0, len(days), (4000, len(days)))
    bs = days["sum"].values[idx].sum(1) / np.maximum(days["size"].values[idx].sum(1), 1)
    gate = next((g for g in GATES if tot["bets"] < g), None)
    if tot["bets"] >= GATES[0]:
        ok = tot["roi_ex10_pct"] > 0 and tot["win_pct"] > tot["betfair_pct"]
        verdict = "%s at the %d-bet read: return without the 10 best winners %+.1f%%, bets won %.2f%% against %.2f%% implied" % (
            "PASS" if ok else "FAIL", max(g for g in GATES if tot["bets"] >= g), tot["roi_ex10_pct"], tot["win_pct"], tot["betfair_pct"])
    else:
        verdict = "no read yet: %d of %d bets" % (tot["bets"], GATES[0])
    S = dict(first_day=a.ds.min(), last_day=a.ds.max(), days=int(a.ds.nunique()), races=int(a.race_id.nunique()), runners=int(len(a)), total=tot,
             roi_90_range_pct=[round(100 * float(np.quantile(bs, 0.05)), 1), round(100 * float(np.quantile(bs, 0.95)), 1)], chance_above_zero_pct=round(100 * float((bs > 0).mean())),
             gain_over_betfair=round(float(gain.mean()), 4), gain_se=round(float(gain.std() / np.sqrt(len(gain))), 4), next_gate=gate, verdict=verdict)
    json.dump(S, open(SUMMARY, "w"), indent=1)
    L = ["# Value model forward test", "",
         "The model was locked on races to %s. Every race below is later than that. Bets are the fixed rule (model chance x net return above 1.00, Betfair starting price under $30), "
         "1 unit each, paid at the Betfair starting price after commission (10%% NSW, 8%% elsewhere). Research only: no bets are placed, and the Betfair starting price is not known "
         "before the jump." % TRAINED_TO, "",
         "Pass rule, fixed before the first day was scored: first read at %d bets, final read at %d. Pass = return above zero without the 10 best winners, and the bets win more "
         "often than the Betfair price implied." % GATES, "",
         "**%s**" % verdict, "",
         "%s to %s: %d days, %d races scored, %d runners." % (S["first_day"], S["last_day"], S["days"], S["races"], S["runners"]), "",
         "| | Bets | Wins | Won | Model said | Betfair said | Avg price | Profit (units) | Return | Return without 10 best |", "|---|---|---|---|---|---|---|---|---|---|"]

    def row(name, t):
        if not t.get("bets"):
            return "| %s | 0 | | | | | | | | |" % name
        return "| %s | %d | %d | %.1f%% | %.1f%% | %.1f%% | $%.2f | %+.1f | %+.1f%% | %+.1f%% |" % (
            name, t["bets"], t["wins"], t["win_pct"], t["model_pct"], t["betfair_pct"], t["avg_price"], t["profit_units"], t["roi_pct"], t["roi_ex10_pct"])
    L.append(row("All bets", tot))
    for name, m in (("Under $6", x.bsp < 6), ("$6 to $12", (x.bsp >= 6) & (x.bsp < 12)), ("$12 to $30", x.bsp >= 12), ("NSW", x.comm > 0.09), ("Other states", x.comm <= 0.09)):
        L.append(row(name, _line(x[m])))
    L += ["", "Return range from resampling days (90%%): %+.1f%% to %+.1f%%; chance the return is above zero: %d%%." % (S["roi_90_range_pct"][0], S["roi_90_range_pct"][1], S["chance_above_zero_pct"]),
          "Winner log-likelihood gain over the Betfair price: %+.4f a race (standard error %.4f)." % (S["gain_over_betfair"], S["gain_se"]), "",
          "## By week", "", "| Week starting | Bets | Wins | Profit (units) | Return |", "|---|---|---|---|---|"]
    wk = pd.to_datetime(x.ds).dt.to_period("W-SUN").dt.start_time.dt.strftime("%Y-%m-%d")
    for k, t in x.groupby(wk):
        L.append("| %s | %d | %d | %+.1f | %+.1f%% |" % (k, len(t), int(t.won.sum()), t.pnl.sum(), 100 * t.pnl.mean()))
    open(REPORT, "w").write("\n".join(L) + "\n")
    print("\n".join(L[:22]))


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "report"
    if cmd == "lock":
        cmd_lock()
    elif cmd == "score":
        cmd_score(redo="--redo" in sys.argv)
        cmd_report()
    else:
        cmd_report()
