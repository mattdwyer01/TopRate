"""bet_log.py -- the betting rules card applied automatically: bets frozen before the jump, settled on real dividends.

Rules (racing-model tests on pre-race dashboard values, 3 Oct 2026; same rules as the race page's Bets box,
frontend/src/lib/betRules.ts):
  Win        Combo top pick 4+ points clear of the 2nd, SM >= +0.5, no first starter in the race.
             Stake so the bet RETURNS $200 at the fixed price: stake = 200 / price.
  Trifecta   1st / 2nd from within 4, 3rd from the 8 line set (within 4, or 4-8 back with SM > -0.5); at least one
             within-4 runner with SM >= +0.5; no first starter in the race; <= 36 combinations; $10 flexi.
  Quinella   box the within-4 runners when there are 2 to 4 (<= 6 combinations), one of them with SM >= +0.5; first
             starters allowed; $15 flexi.
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
RM_JSON = DIR / "racing_model.json"
DIVIDENDS = DIR / "tab_dividends.csv"

LOCK_MINUTES = 12
INNER, OUTER, SM_T = 4.0, 8.0, 0.5
WIN_RETURN = 200.0
TRI_CAP, TRI_STAKE = 36, 10.0
QUIN_CAP, QUIN_STAKE = 6, 15.0
QUAD_CAP, QUAD_STAKE, EARLY_QUAD_STAKE = 400, 25.0, 25.0
WPR_M, WPR_S, TRR_M, TRR_S = 72.57, 10.48, 96.26, 2.71
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
    r["tp"] = r["wprp_contrib"].map(lambda v: _contrib(v, "speed_map") + _contrib(v, "track_barrier"))
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
    trr = pd.to_numeric(r["toprate_rating"], errors="coerce")
    r["combo"] = np.where(trr.notna(), (2 * r["proj"] + (WPR_M + (trr - TRR_M) / TRR_S * WPR_S)) / 3, r["proj"])
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
                if second["gap"] >= INNER and top["sm"] >= SM_T and pd.notna(price) and price > 1:
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
        # quinella (no first-starter filter): box of the within-4 runners
        for n, g in races.items():
            if not soon(n):
                continue
            f = frame(n)
            bid = f"{g['race_id'].iloc[0]}:Quinella"
            if f is None or bid in logged_ids:
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
            if rid not in run.index:
                continue
            row = run.loc[rid]
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
