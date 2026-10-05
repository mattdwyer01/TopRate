"""bet_log.py -- the betting rules card applied automatically: bets frozen before the jump, settled on real dividends.

Rules (racing-model tests on pre-race dashboard values, 3 Oct 2026; same rules as the race page's Bets box,
frontend/src/lib/betRules.ts):
  Win        Proj + price top pick 4+ clear of the 2nd, SM >= +1, no first starter in the race.
             Stake so the bet RETURNS $200 at the fixed price: stake = 200 / price.
  Trifecta   1st / 2nd from within 4, 3rd from the 8 line set (within 4, or 4-8 back with SM > -1); at least one
             within-4 runner with SM >= +1; no first starter in the race; <= 36 combinations; $10 flexi.
  Quinella   box the within-4 runners when there are 2 to 4 (<= 6 combinations), one of them with SM >= +1; no first
             starter in the race (user rule 3 Oct 2026; the test showed no harm); $15 flexi.
  Bush       no bets at bush meetings (top race prize $20k or less, the dashboard's bush filter).
  Quaddie    main quaddie = last 4 races of the meeting; each leg the 8 line set; no first starter in any leg;
             <= 400 combinations; $25 flexi.
  Early quad the 4 races before the main quaddie (races 1-4 at meetings of 7 races or fewer); same rule; $25 flexi.
  Heavy      going Heavy (any leg for a quaddie): every stake halved (win returns $100).

Why a log: the race page recomputes from CURRENT data, and TopRate rewrites its rating after the jump (look-ahead), so a
results page built from it would flatter the rules. Each bet is frozen once, the first poll that finds its race (for a
quaddie, its first leg) starting within LOCK_MINUTES, from the runners file and racing_model.json as they are then.
A race that has already started is never logged.

Combo / SM are built as the dashboard builds them (lib/racingModel.ts withModelAdjustments + lib/raceModel.ts
compositeScore): adjusted projection = wprp_proj - TopRate (speed_map + track_barrier) + Racing Model (d + past ground
loss), both demeaned over the field; Combo = 2/3 adjusted projection + 1/3 TopRate rating rescaled to the WPR scale;
SM = the Racing Model part demeaned over the field; gaps over non-scratched runners.

Settling: win from finish_position (refund if the horse is scratched after logging); exotics from tab_dividends.csv
(TAB's winning selections and dividend): return = dividend x stake / combinations (flexi). Written to bets_log.csv
(committed) and bets_log.json (what the dashboard's Bets tab reads).
"""
import json
import re
from datetime import datetime, timedelta, timezone
from pathlib import Path

import numpy as np
import pandas as pd

DIR = Path(__file__).parent
LOG_CSV = DIR / "bets_log.csv"
LOG_JSON = DIR / "bets_log.json"
VALUE_CSV = DIR / "value_log.csv"
RM_JSON = DIR / "racing_model.json"
DIVIDENDS = DIR / "tab_dividends.csv"

LOCK_MINUTES = 12
INNER, OUTER, SM_T = 4.0, 8.0, 1.0   # Proj + price lines 4 / 8 (6 Oct 2026, user decision; lib/raceModel.ts); SM favoured at +/-1
# win rule: Proj top pick 3+ clear (walk-forward, no first starter, SP $2+: 3 clear -7.6% at SP over 3,695 bets, -7.9% /
# -7.3% in 2023-24 / 2025-26; 2 clear -11.3%, 2.3 clear -8.8%)
WIN_CLEAR = 4.0   # with the price adjustment: 3,554 bets, 34.7%, -8.1% at SP (2025-26 -5.3%)
MKT_WPR = 2.0     # price adjustment: WPR per unit of log fixed price vs the field (lib/racingModel.ts)
WIN_RETURN = 200.0
# exotic stakes halved from 4 Oct 2026 until the ~23 Oct review on real dividends (user decision after a -32% day);
# full stakes were trifecta 10, quinella 15, quaddies 25
TRI_CAP, TRI_STAKE = 36, 5.0
QUIN_CAP, QUIN_STAKE = 6, 7.5
QUAD_CAP, QUAD_STAKE, EARLY_QUAD_STAKE = 400, 12.5, 12.5
# bush meetings (top race prize <= $20k, the dashboard's BUSH_TRACK_THRESHOLD) get no bets (user rule 3 Oct 2026)
BUSH_PRIZE = 20000
WPR_M, WPR_S, TRR_M, TRR_S = 72.57, 10.48, 96.26, 2.71
RM_WPR = 8.205   # WPR points per unit of log chance of the layered Racing Model p (6.843 / 0.834)
TOPRATE_PARTS_OUT = ("speed_map", "track_barrier", "own_going", "own_trend", "own_distance")
JSON_DAYS = 60

FIELDS = ["bet_id", "date", "venue", "race", "race_id", "start_utc", "logged_utc", "bet", "legs", "selection",
          "runner_ids", "combos", "stake", "price", "flexi_pct", "status", "winners", "dividend", "return", "profit"]


def _contrib(v, key):
    try:
        x = json.loads(v).get(key) if isinstance(v, str) else None
        return float(x) if x is not None else 0.0
    except (ValueError, TypeError, AttributeError):
        return 0.0


def race_frame(r, rm):
    """One race's live runners with combo gap, SM and the in / out sets (pandas frame, sorted by gap)."""
    r = r[pd.to_numeric(r["scratched"], errors="coerce").fillna(0) == 0].copy()
    r["proj"] = pd.to_numeric(r["wprp_proj"], errors="coerce")
    r = r[r["proj"].notna()]
    if len(r) < 2:
        return None
    # TopRate terms taken out (as lib/racingModel.ts TOPRATE_PARTS_OUT): speed map / barrier (replaced by the Racing
    # Model's part) and own going / trend / distance (noise, 4 Oct 2026)
    r["tp"] = r["wprp_contrib"].map(lambda v: sum(_contrib(v, k) for k in TOPRATE_PARTS_OUT))
    ours = []
    for rid in r["run_id"].astype(str):
        m = rm.get(rid)
        ours.append(np.nan if not m else (m.get("d") or 0.0) + ((m.get("gb") or {}).get("ground loss (past runs)") or 0.0))
    r["ours"] = ours
    has = r["ours"].notna()
    if has.sum() >= 2:
        r.loc[has, "proj"] = (r.loc[has, "proj"] - (r.loc[has, "tp"] - r.loc[has, "tp"].mean())
                              + (r.loc[has, "ours"] - r.loc[has, "ours"].mean()))
        r["sm"] = r["ours"] - r.loc[has, "ours"].mean()
    else:
        sm = r["wprp_contrib"].map(lambda v: _contrib(v, "speed_map"))
        r["sm"] = sm - sm.mean()
    # Proj (6 Oct 2026, user decision; lib/raceModel.ts compositeScore): the Racing Model's projected WPR from prior form
    # (racing_model.json wp, front-weighted WPR model); TopRate's adjusted projection when the runner has none
    wp = pd.Series([(rm.get(str(i)) or {}).get("wp") for i in r["run_id"]], index=r.index, dtype=float)
    r["combo"] = wp.fillna(r["proj"]) if wp.notna().sum() >= 2 else r["proj"]
    # + price adjustment when every live runner has a fixed price (6 Oct 2026, as the dashboard)
    fx = pd.to_numeric(r["fixed_win_price"], errors="coerce")
    if (fx > 1).all():
        lp = -np.log(fx)
        r["combo"] = r["combo"] + MKT_WPR * (lp - lp.mean())
    r["gap"] = r["combo"].max() - r["combo"]
    r = r.sort_values("gap")
    r["inner"] = r["gap"] <= INNER
    r["outer"] = r["inner"] | ((r["gap"] <= OUTER) & ~(r["sm"] <= -SM_T))
    return r


def _nums(r):
    return ",".join(str(int(float(x))) for x in r["tab_number"])


def _fs(race_rows):
    return str(race_rows["has_first_starter"].iloc[0]).strip().lower() in ("true", "1", "1.0")


def _factor(*race_rows):
    """0.5 on a heavy track (any of the races), else 1."""
    return 0.5 if any(re.search(r"\bh(ea)?vy", str(g["going"].iloc[0]), re.I) for g in race_rows) else 1.0


def _quad_legs(nos, kind):
    nos = sorted(nos)
    if kind == "Quaddie":
        return nos[-4:] if len(nos) >= 4 else None
    if len(nos) >= 8:
        return nos[-8:-4]
    return nos[:4] if len(nos) >= 5 else None


def new_bets(runners, rm, now, logged_ids):
    """Bets for races starting within LOCK_MINUTES (and not yet started) that are not in the log yet."""
    rows = []
    today = runners[runners["date"].astype(str).str[:10] >= (now - timedelta(days=1)).date().isoformat()].copy()
    today["start"] = pd.to_datetime(today["start_time"], utc=True, errors="coerce")
    today["race_n"] = pd.to_numeric(today["race"], errors="coerce")
    stamp = now.isoformat(timespec="seconds")
    for (day, venue), meet in today.groupby([today["date"].astype(str).str[:10], "venue"]):
        if pd.to_numeric(meet["prize_money"], errors="coerce").fillna(0).max() <= BUSH_PRIZE:
            continue
        races = {int(n): g for n, g in meet.groupby("race_n")}
        frames = {}

        def frame(n):
            if n not in frames:
                frames[n] = race_frame(races[n], rm) if n in races else None
            return frames[n]

        def soon(n):
            st = races[n]["start"].iloc[0] if n in races else pd.NaT
            return pd.notna(st) and now < st <= now + timedelta(minutes=LOCK_MINUTES)

        for n, g in races.items():
            if not soon(n):
                continue
            base = dict(date=day, venue=venue, race=n, race_id=str(g["race_id"].iloc[0]),
                        start_utc=g["start"].iloc[0].isoformat(), logged_utc=stamp, status="pending")
            f = frame(n)
            if f is None or _fs(g):
                continue
            # win
            bid = f"{base['race_id']}:Win"
            if bid not in logged_ids and len(f) >= 2:
                top, second = f.iloc[0], f.iloc[1]
                price = pd.to_numeric(pd.Series([top["fixed_win_price"]]), errors="coerce").iloc[0]
                if second["gap"] >= WIN_CLEAR and top["sm"] >= SM_T and pd.notna(price) and price > 1:
                    rows.append({**base, "bet_id": bid, "bet": "Win", "legs": str(n),
                                 "selection": f"{int(float(top['tab_number']))} {top['horse']}",
                                 "runner_ids": str(top["run_id"]), "combos": 1,
                                 "stake": round(WIN_RETURN * _factor(g) / price, 2),
                                 "price": float(price), "flexi_pct": 100.0})
            # trifecta
            bid = f"{base['race_id']}:Trifecta"
            a, b = f[f["inner"]], f[f["outer"]]
            combos = len(a) * (len(a) - 1) * max(0, len(b) - 2)
            if (bid not in logged_ids and len(a) >= 2 and len(b) >= 3 and combos <= TRI_CAP
                    and (a["sm"] >= SM_T).any()):
                stake = TRI_STAKE * _factor(g)
                rows.append({**base, "bet_id": bid, "bet": "Trifecta", "legs": str(n),
                             "selection": f"{_nums(a)} / {_nums(a)} / {_nums(b)}",
                             "runner_ids": "|".join([",".join(a["run_id"].astype(str)), ",".join(b["run_id"].astype(str))]),
                             "combos": combos, "stake": stake, "price": np.nan,
                             "flexi_pct": round(100 * stake / combos, 1)})
        # quinella: box of the within-4 runners, no first starter in the race
        for n, g in races.items():
            if not soon(n):
                continue
            f = frame(n)
            bid = f"{g['race_id'].iloc[0]}:Quinella"
            if f is None or bid in logged_ids or _fs(g):
                continue
            a = f[f["inner"]]
            combos = len(a) * (len(a) - 1) // 2
            if len(a) >= 2 and combos <= QUIN_CAP and (a["sm"] >= SM_T).any():
                stake = QUIN_STAKE * _factor(g)
                rows.append(dict(bet_id=bid, date=day, venue=venue, race=n, race_id=str(g["race_id"].iloc[0]),
                                 start_utc=g["start"].iloc[0].isoformat(), logged_utc=stamp, status="pending",
                                 bet="Quinella", legs=str(n), selection=f"box {_nums(a)}",
                                 runner_ids=",".join(a["run_id"].astype(str)), combos=combos, stake=stake,
                                 price=np.nan, flexi_pct=round(100 * stake / combos, 1)))
        # quaddies: locked when their first leg is about to start
        for kind, stake in (("EarlyQuaddie", EARLY_QUAD_STAKE), ("Quaddie", QUAD_STAKE)):
            legs = _quad_legs(list(races), kind)
            if not legs or not soon(legs[0]) or any(l not in races for l in legs):
                continue
            last = races[legs[-1]]
            bid = f"{last['race_id'].iloc[0]}:{kind}"
            if bid in logged_ids or any(_fs(races[l]) for l in legs):
                continue
            fr = [frame(l) for l in legs]
            if any(x is None or not x["outer"].any() for x in fr):
                continue
            sets = [x[x["outer"]] for x in fr]
            combos = int(np.prod([len(s) for s in sets]))
            if combos > QUAD_CAP:
                continue
            first = races[legs[0]]
            stake = stake * _factor(*[races[l] for l in legs])
            rows.append(dict(bet_id=bid, date=day, venue=venue, race=legs[-1], race_id=str(last["race_id"].iloc[0]),
                             start_utc=first["start"].iloc[0].isoformat(), logged_utc=stamp, status="pending",
                             bet=kind, legs=f"{legs[0]}-{legs[-1]}",
                             selection=" / ".join(f"R{l}: {_nums(s)}" for l, s in zip(legs, sets)),
                             runner_ids="|".join(",".join(s["run_id"].astype(str)) for s in sets),
                             combos=combos, stake=stake, price=np.nan, flexi_pct=round(100 * stake / combos, 1)))
    return rows


def _winner_sets(sel):
    """TAB selections '3/14/5' (dead heats '2+5') -> [{3}, {14}, {5}]."""
    return [set(p.split("+")) for p in str(sel).split("/")]


def settle(log, runners, dividends, venue_of):
    """Fill status / winners / dividend / return / profit for pending bets whose result is in."""
    if log.empty:
        return log
    run = runners.assign(run_id=runners["run_id"].astype(str)).set_index("run_id")
    divs = {}
    if dividends is not None and not dividends.empty:
        for x in dividends.itertuples():
            divs.setdefault((str(x.date), venue_of(x.venue).upper(), int(x.race_no), x.product), []).append(x)
    for i, b in log[log["status"] == "pending"].iterrows():
        if b["bet"] == "Win":
            rid = str(b["runner_ids"])
            row = run.loc[rid] if rid in run.index else pd.Series(dtype=object)
            row = row.iloc[0] if isinstance(row, pd.DataFrame) else row
            if pd.to_numeric(pd.Series([row.get("scratched")]), errors="coerce").fillna(0).iloc[0] == 1:
                log.loc[i, ["status", "return"]] = ["refund", b["stake"]]
            else:
                fp = pd.to_numeric(pd.Series([row.get("finish_position")]), errors="coerce").iloc[0]
                if pd.notna(fp):
                    won = int(fp) == 1
                    log.loc[i, ["status", "winners", "return"]] = [
                        "won" if won else "lost", str(int(fp)), round(b["stake"] * b["price"], 2) if won else 0.0]
                else:
                    # finish positions reach the runners file later than TAB's dividends: settle from the Win pool's
                    # winner (selection "4", dead heat "2+5" -> half the return each)
                    rows = divs.get((str(b["date"]), str(b["venue"]).upper(), int(b["race"]), "Win"))
                    if rows:
                        w = _winner_sets(rows[0].selections)[0]
                        tab = str(b["selection"]).split()[0]
                        won = tab in w
                        log.loc[i, ["status", "winners", "return"]] = [
                            "won" if won else "lost", '+'.join(sorted(w)),
                            round(b["stake"] * b["price"] / len(w), 2) if won else 0.0]
        else:
            key = (str(b["date"]), str(b["venue"]).upper(), int(b["race"]), b["bet"])
            rows = divs.get(key)
            if not rows:
                continue
            # Trifecta selection "a / a / b" (numbers); quaddie "R5: x,y / R6: ..." -> strip the "n:" prefix
            if b["bet"] == "Quinella":         # "box 3,1,10": both placegetters in the box, any order
                box = set(str(b["selection"]).replace("box", "").strip().split(","))
                tab_sets = [box, box]
            else:
                tab_sets = [set(p.split(":")[-1].strip().split(",")) for p in str(b["selection"]).split(" / ")]
            ret, winners = 0.0, rows[0].selections
            for x in rows:
                w = _winner_sets(x.selections)
                if len(w) == len(tab_sets) and all(ws & ts for ws, ts in zip(w, tab_sets)):
                    ret += float(x.amount) * float(b["stake"]) / float(b["combos"])
                    winners = x.selections
            log.loc[i, ["status", "winners", "dividend", "return"]] = [
                "won" if ret > 0 else "lost", str(winners), float(rows[0].amount), round(ret, 2)]
    # no result / dividend a day after the race (e.g. a meeting TAB does not cover): void, stake back
    stale = (log["status"] == "pending") & (pd.to_datetime(log["start_utc"], utc=True, errors="coerce")
                                           < pd.Timestamp.now(tz="UTC") - pd.Timedelta(hours=30))
    log.loc[stale, "status"] = "void"
    log.loc[stale, "return"] = log.loc[stale, "stake"]
    done = log["status"] != "pending"
    log.loc[done, "profit"] = (pd.to_numeric(log.loc[done, "return"], errors="coerce").fillna(0)
                               - pd.to_numeric(log.loc[done, "stake"], errors="coerce"))
    return log


# Value log (logged only, no stake on the bets card): the Racing Model's value model (racing-model model/value_live.py,
# walk-forward 2024 to Sep 2026: value >= 1.0 and SP <= $21 made +5.7% over 1,916 bets at SP). Every runner whose
# value at the fixed price 12 min before the jump is >= 1.0 (price <= $51, VIC / SA / QLD, bush included) is frozen with a
# notional $10, then settled like a win bet. win chance p = softmax(vs x log p_fixed + vu) over the field.
# NSW added 5 Oct 2026 (racing-model value_model --five-states: VIC/SA/QLD-fitted model on NSW 536 bets +2.5%, -14 to +19;
# WA 122 bets -23%, left out)
# WA and TAS added 5 Oct 2026 (user decision, logged only): WA lost 23% over 122 backtest bets; TAS was not backtested
VALUE_STATES = ("VIC", "SA", "QLD", "NSW", "WA", "TAS")
VALUE_CUT, VALUE_MAX_PRICE, VALUE_STAKE = 1.0, 51.0, 10.0   # cap $51 (5 Oct: +6.3% vs +5.7% at $21)
VALUE_FIELDS = ["bet_id", "date", "state", "venue", "race", "race_id", "start_utc", "logged_utc", "run_id", "selection", "price",
                "p_value", "value", "combo_gap", "sm", "stake", "status", "finish", "return", "profit"]


def value_bets(runners, rm, now, logged_ids):
    rows = []
    t = runners[runners["date"].astype(str).str[:10] >= (now - timedelta(days=1)).date().isoformat()].copy()
    t["start"] = pd.to_datetime(t["start_time"], utc=True, errors="coerce")
    t = t[(t["start"] > now) & (t["start"] <= now + timedelta(minutes=LOCK_MINUTES))]
    if "state" in t:
        t = t[t["state"].astype(str).str.upper().isin(VALUE_STATES)]
    stamp = now.isoformat(timespec="seconds")
    for (day, venue), meet in t.groupby([t["date"].astype(str).str[:10], "venue"]):
        # bush meetings included (5 Oct 2026): the backtest covered every VIC/SA/QLD race, and country races were
        # among its best (+8.8%, provincial +11.5%, metro -7.4%)
        for n, g in meet.groupby(pd.to_numeric(meet["race"], errors="coerce")):
            g = g[pd.to_numeric(g["scratched"], errors="coerce").fillna(0) == 0].copy()
            g["price"] = pd.to_numeric(g["fixed_win_price"], errors="coerce")
            m = [rm.get(str(i)) or {} for i in g["run_id"].astype(str)]
            g["vu"] = [x.get("vu") for x in m]
            g["vs"] = [x.get("vs") for x in m]
            if len(g) < 2 or g["price"].isna().any() or (g["price"] <= 1).any() or g["vu"].isna().any():
                continue
            inv = 1 / g["price"]
            lp = np.log(inv / inv.sum())
            u = g["vs"].astype(float) * lp + g["vu"].astype(float)
            p = np.exp(u - u.max())
            g["p"] = p / p.sum()
            g["value"] = g["p"] * g["price"]
            f = race_frame(g, rm)
            gap = f.set_index(f["run_id"].astype(str))[["gap", "sm"]] if f is not None else pd.DataFrame(columns=["gap", "sm"])
            for _, x in g[(g["value"] >= VALUE_CUT) & (g["price"] <= VALUE_MAX_PRICE)].iterrows():
                rid = str(x["run_id"])
                bid = f"{rid}:Value"
                if bid in logged_ids:
                    continue
                rows.append(dict(bet_id=bid, date=day, state=str(x.get("state", "")), venue=venue, race=int(n),
                                 race_id=str(x["race_id"]),
                                 start_utc=x["start"].isoformat(), logged_utc=stamp, run_id=rid,
                                 selection=f"{int(float(x['tab_number']))} {x['horse']}", price=float(x["price"]),
                                 p_value=round(float(x["p"]), 4), value=round(float(x["value"]), 3),
                                 combo_gap=round(float(gap["gap"].get(rid)), 2) if rid in gap.index else None,
                                 sm=round(float(gap["sm"].get(rid)), 2) if rid in gap.index else None,
                                 stake=VALUE_STAKE, status="pending"))
    return rows


def settle_value(log, runners):
    run = runners.assign(run_id=runners["run_id"].astype(str)).drop_duplicates("run_id").set_index("run_id")
    for i, b in log[log["status"] == "pending"].iterrows():
        row = run.loc[b["run_id"]] if b["run_id"] in run.index else pd.Series(dtype=object)
        if pd.to_numeric(pd.Series([row.get("scratched")]), errors="coerce").fillna(0).iloc[0] == 1:
            log.loc[i, ["status", "return"]] = ["refund", b["stake"]]
            continue
        fp = pd.to_numeric(pd.Series([row.get("finish_position")]), errors="coerce").iloc[0]
        if pd.notna(fp):
            won = int(fp) == 1
            log.loc[i, ["status", "finish", "return"]] = ["won" if won else "lost", str(int(fp)),
                                                          round(float(b["stake"]) * float(b["price"]), 2) if won else 0.0]
    stale = (log["status"] == "pending") & (pd.to_datetime(log["start_utc"], utc=True, errors="coerce")
                                           < pd.Timestamp.now(tz="UTC") - pd.Timedelta(hours=48))
    log.loc[stale, ["status", "return"]] = ["void", VALUE_STAKE]
    done = log["status"] != "pending"
    log.loc[done, "profit"] = (pd.to_numeric(log.loc[done, "return"], errors="coerce").fillna(0)
                               - pd.to_numeric(log.loc[done, "stake"], errors="coerce"))
    return log


def update_value(runners, rm, now):
    """Value log: freeze value >= 1.0 runners before the jump, settle from finish positions. Never raises."""
    try:
        log = pd.read_csv(VALUE_CSV, dtype={"race_id": str, "run_id": str, "bet_id": str, "finish": str}) \
            if VALUE_CSV.exists() else pd.DataFrame(columns=VALUE_FIELDS)
        new = value_bets(runners, rm, now, set(log["bet_id"].astype(str)))
        if new:
            log = pd.concat([log, pd.DataFrame(new)], ignore_index=True)
            print("  Value logged: " + ", ".join(f"{r['venue']} R{r['race']} {r['selection']} ${r['price']}" for r in new))
        log = log.reindex(columns=VALUE_FIELDS)
        for c in ("status", "finish", "selection", "run_id", "bet_id", "race_id"):
            log[c] = log[c].astype("object")
        before = (log["status"] != "pending").sum()
        log = settle_value(log, runners)
        if new or (log["status"] != "pending").sum() != before or not VALUE_CSV.exists():
            log.to_csv(VALUE_CSV, index=False)
    except Exception as e:  # noqa: BLE001
        print(f"  value log failed (non-fatal): {type(e).__name__}: {e}")


def update(runners, venue_of, now=None):
    """Log new bets, settle pending ones, write bets_log.csv / .json. Best-effort: never raises."""
    try:
        now = now or datetime.now(timezone.utc)
        log = pd.read_csv(LOG_CSV, dtype={"race_id": str, "runner_ids": str, "bet_id": str, "winners": str}) \
            if LOG_CSV.exists() \
            else pd.DataFrame(columns=FIELDS)
        rm = json.loads(RM_JSON.read_text()).get("runners", {}) if RM_JSON.exists() else {}
        new = new_bets(runners, rm, now, set(log["bet_id"].astype(str)))
        if new:
            log = pd.concat([log, pd.DataFrame(new)], ignore_index=True)
            print(f"  Bets logged: " + ", ".join(f"{r['venue']} R{r['race']} {r['bet']}" for r in new))
        log = log.reindex(columns=FIELDS)
        for c in ("winners", "status", "selection", "legs", "runner_ids", "bet_id", "race_id"):
            log[c] = log[c].astype("object")
        divs = pd.read_csv(DIVIDENDS, dtype={"selections": str}) if DIVIDENDS.exists() else None
        before = (log["status"] != "pending").sum()
        log = settle(log, runners, divs, venue_of)
        n_settled = (log["status"] != "pending").sum() - before
        if n_settled:
            print(f"  Bets settled: {n_settled}")
        if new or n_settled or not LOG_CSV.exists():
            log = log.reindex(columns=FIELDS)
            log.to_csv(LOG_CSV, index=False)
            cut = (now - timedelta(days=JSON_DAYS)).date().isoformat()
            recent = log[log["date"].astype(str) >= cut].replace({np.nan: None})
            LOG_JSON.write_text(json.dumps({"updated": now.isoformat(timespec="seconds"),
                                            "bets": recent.to_dict(orient="records")}, separators=(",", ":")))
    except Exception as e:  # noqa: BLE001
        print(f"  bet log failed (non-fatal): {type(e).__name__}: {e}")
    rm = json.loads(RM_JSON.read_text()).get("runners", {}) if RM_JSON.exists() else {}
    update_value(runners, rm, now or datetime.now(timezone.utc))
