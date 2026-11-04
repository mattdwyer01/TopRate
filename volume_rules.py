"""Volume rules tracker (4 Nov 2026).

Two research betting rules, logged side by side so they can be judged on bets taken before the jump (not on the 30 days they were tuned on):

  Volume v1 (the original rule)
      a runner qualifies when it is forecast to settle in the FIRST THIRD of its field (trip map, rank on forecast gap behind the leader:
      (rank - 1) / (n - 1) <= 1/3) and its fixed price is over $3; v1 bets every qualifier within 4 Proj points of the top-rated runner.
  Volume v2 (v1 with the "top pick" condition)
      A: when the top-rated runner is itself a qualifier, bet the qualifiers within 2 points of the top;
      B: when NO qualifier is within 1 point of the top, bet the qualifiers within 4 points;
      otherwise no bet in the race.

Both skip a race when: the field has under 5 live runners, any live runner is a first starter / light-history / has no Proj, any live runner has no trip map
forecast, or the meeting is bush (biggest single race prize $20,000 or less, same rule as the dashboard). Stake is $25 a race per rule, split equally across the
bets the rule makes in that race. Prices are the fixed prices in runners.csv (TAB, updated every few minutes) at logging time.

Commands (run from the repo root):
  python volume_rules.py list [--date D]       print today's bets for both rules, nothing is written
  python volume_rules.py log [--now ISO]       freeze the bets of races jumping in the next 40 minutes (replaces a race's rows until 1 minute before the jump)
  python volume_rules.py settle                fill won / finish / starting price for logged bets whose race has a result
  python volume_rules.py snapshot              save today's and later trip map forecasts to data/trip_map_archive/<date>.json.gz
  python volume_rules.py report                write volume_report.md and volume_summary.json from the log
  python volume_rules.py backtest [--from D] [--to D]   the same rules on resulted races in runners.csv (starting prices), as a check of this code

Files: volume_bets_log.csv (one row per bet), volume_races_log.csv (one row per race checked, with the reason when it had no bet),
volume_overrides.json (hand exclusions, for example a meeting that was transferred).
"""
import argparse
import gzip
import json
import os
import sys

import numpy as np
import pandas as pd

RUNNERS = "runners.csv"
TRIP_MAP = "trip_map.json"
BETS_LOG = "volume_bets_log.csv"
RACES_LOG = "volume_races_log.csv"
OVERRIDES = "volume_overrides.json"
ARCHIVE_DIR = "data/trip_map_archive"
REPORT_MD = "volume_report.md"
SUMMARY_JSON = "volume_summary.json"

BUSH_MAX_PRIZE = 20000       # same as frontend lib/meetings.ts BUSH_TRACK_THRESHOLD
MIN_FIELD = 5
MIN_PRICE = 3.0              # strictly over (raised from 2.0 on 4 Nov 2026)
FIRST_THIRD = 1 / 3
V1_MAX_OFF = 4.0
V2A_MAX_OFF = 2.0            # top pick is a bet: qualifiers under 2 points off the top
V2B_NEAR = 1.0               # nobody within this many points of the top qualifies ...
V2B_MAX_OFF = 4.0            # ... then qualifiers up to this many points off
STAKE_PER_RACE = 25.0
LOG_MIN_MINS = 1             # a race is (re)logged while it is 1 to 40 minutes from the jump
LOG_MAX_MINS = 40
SKIP_SOURCES = {"duplicate entry"}

RUNNER_COLS = ["date", "venue", "race", "race_id", "run_id", "horse", "tab_number", "barrier", "start_time", "scratched", "wprp_proj", "wprp_model",
               "fixed_win_price", "starting_price_sp", "going", "prize_money", "rs_label", "won", "finish_position", "interim_resulted", "resulted",
               "field_source"]

BET_COLS = ["logged_at", "mins_to_jump", "date", "venue", "race", "race_id", "run_id", "start_time", "horse", "tab_number", "barrier", "price_logged",
            "v1", "v2", "stake_v1", "stake_v2", "proj", "top_proj", "off_top", "gap", "gap_rank", "field_n", "sp_frac", "top_is_bet", "n_qual_within1",
            "going", "rs_label", "meeting_min_prize", "race_prize", "prev_races", "prev_win_first_third", "prev_win_sp", "prev_top3_sp", "won", "finish_position", "sp_final", "void", "settled_at"]
RACE_COLS = ["checked_at", "mins_to_jump", "date", "venue", "race", "race_id", "start_time", "field_n", "reason", "v1_bets", "v2_bets"]


def num(s):
    return pd.to_numeric(s, errors="coerce")


# ----------------------------------------------------------------------------------------------------------------------------------------------
# inputs

def read_runners(date=None):
    df = pd.read_csv(RUNNERS, usecols=lambda c: c in RUNNER_COLS, low_memory=False)
    if date is not None:
        df = df[df["date"] == date]
    return df.copy()


def read_gaps(path=TRIP_MAP):
    """run_id (as text) -> forecast gap in lengths behind the leader."""
    t = json.load(open(path))
    out = {}
    for v in t.get("races", {}).values():
        for r in v.get("runners", []):
            if r.get("gap") is not None:
                out[str(r["rid"])] = float(r["gap"])
    return out, t.get("generated")


def read_overrides():
    if not os.path.exists(OVERRIDES):
        return []
    return json.load(open(OVERRIDES)).get("exclude", [])


# ----------------------------------------------------------------------------------------------------------------------------------------------
# the rules

def evaluate(df, gaps, price_mode="fixed", overrides=None):
    """Apply both rules to every race in df (rows of one or more dates). Returns (runners, races): live runners with rule flags, and one row per race
    with the reason it was or was not eligible."""
    d = df.copy()
    d["prize_money"] = num(d["prize_money"])
    # bush: biggest single race of the meeting (all rows, scratched or not), unknown prize never counts as bush
    top_prize = d.drop_duplicates("race_id").groupby(["date", "venue"])["prize_money"].max().rename("meet_top").reset_index()
    d = d.merge(top_prize, on=["date", "venue"], how="left")
    d["bush"] = d["meet_top"].notna() & (d["meet_top"] <= BUSH_MAX_PRIZE)
    # lowest race prize of the meeting (segment column for the forward test: meetings where every race is over $30k / $40k ...)
    low_prize = d.drop_duplicates("race_id").groupby(["date", "venue"])["prize_money"].min().rename("meet_min").reset_index()
    d = d.merge(low_prize, on=["date", "venue"], how="left")
    for o in overrides or []:
        d = d[~((d["date"] == o.get("date")) & (d["venue"] == o.get("venue")))]
    d = d[num(d["scratched"]).fillna(0) != 1]
    d = d[~d["field_source"].astype(str).isin(SKIP_SOURCES)]
    d = d[num(d["run_id"]).notna()].copy()
    d["rid"] = num(d["run_id"]).astype("int64").astype(str)
    d["gap"] = d["rid"].map(gaps)
    d["proj"] = num(d["wprp_proj"])
    fixed = num(d["fixed_win_price"])
    d["price"] = num(d["starting_price_sp"]).fillna(fixed) if price_mode == "sp" else fixed
    d["unk"] = d["wprp_model"].isin(["debut", "light"]) | d["proj"].isna()
    g = d.groupby("race_id")
    d["n"] = g["race_id"].transform("size")
    d["anyunk"] = g["unk"].transform("any")
    d["nogap"] = g["gap"].transform(lambda s: s.isna().any())
    d["top"] = g["proj"].transform("max")
    d["off"] = d["top"] - d["proj"]
    d["rk"] = g["gap"].rank(method="min")
    d["sp"] = (d["rk"] - 1) / (d["n"] - 1).replace(0, np.nan)

    def reason(r):
        if r.bush:
            return "bush meeting"
        if r.n < MIN_FIELD:
            return f"field under {MIN_FIELD}"
        if r.anyunk:
            return "first starter, light-history or no-Proj runner"
        if r.nogap:
            return "no trip map forecast for some runner"
        return "ok"

    rc = d.groupby("race_id").agg(date=("date", "first"), venue=("venue", "first"), race=("race", "first"), start_time=("start_time", "first"), field_n=("n", "first"),
                                  bush=("bush", "first"), anyunk=("anyunk", "first"), nogap=("nogap", "first"), n=("n", "first")).reset_index()
    rc["reason"] = rc.apply(reason, axis=1)
    ok = set(rc.loc[rc["reason"] == "ok", "race_id"])
    d["race_ok"] = d["race_id"].isin(ok)
    d["qual"] = d["race_ok"] & (d["sp"] <= FIRST_THIRD + 1e-9) & (d["price"] > MIN_PRICE)
    d["v1"] = d["qual"] & (d["off"] <= V1_MAX_OFF + 1e-9)
    d["is_top_bet"] = d["qual"] & (d["off"] <= 1e-9)
    g = d.groupby("race_id")
    d["top_is_bet"] = g["is_top_bet"].transform("any")
    near = (d["qual"] & (d["off"] <= V2B_NEAR + 1e-9)).groupby(d["race_id"]).transform("sum")
    d["n_qual_within1"] = near
    a = d["top_is_bet"] & d["qual"] & (d["off"] < V2A_MAX_OFF)
    b = (d["n_qual_within1"] == 0) & d["qual"] & (d["off"] <= V2B_MAX_OFF + 1e-9)
    d["v2"] = a | b
    for r in ("v1", "v2"):
        cnt = d.groupby("race_id")[r].transform("sum")
        d[f"stake_{r}"] = np.where(d[r], STAKE_PER_RACE / cnt.replace(0, np.nan), 0.0)
    rc["v1_bets"] = rc["race_id"].map(d.groupby("race_id")["v1"].sum()).fillna(0).astype(int)
    rc["v2_bets"] = rc["race_id"].map(d.groupby("race_id")["v2"].sum()).fillna(0).astype(int)
    return d, rc


def melb(ts):
    return pd.Timestamp(ts).tz_convert("Australia/Melbourne")


def now_utc(arg=None):
    if not arg:
        return pd.Timestamp.now("UTC")
    t = pd.Timestamp(arg)
    return t.tz_localize("UTC") if t.tzinfo is None else t.tz_convert("UTC")


# ----------------------------------------------------------------------------------------------------------------------------------------------
# commands

def cmd_list(a):
    now = now_utc(a.now)
    date = a.date or melb(now).strftime("%Y-%m-%d")
    gaps, gen = read_gaps(a.trip_map)
    d, rc = evaluate(read_runners(date), gaps, "fixed", read_overrides())
    print(f"{date}: now {melb(now).strftime('%a %H:%M')} Melbourne, trip map generated {gen}")
    b = d[d["v1"] | d["v2"]].copy()
    b["st"] = pd.to_datetime(b["start_time"])
    b["time"] = b["st"].dt.tz_convert("Australia/Melbourne").dt.strftime("%-I:%M%p")
    b["rule"] = np.where(b["v1"] & b["v2"], "v1+v2", np.where(b["v1"], "v1", "v2"))
    b = b.sort_values(["st", "race_id", "price"])
    print(b[["time", "venue", "race", "horse", "tab_number", "price", "rule", "stake_v1", "stake_v2", "off", "going"]].round(2).to_string(index=False))
    for r in ("v1", "v2"):
        x = b[b[r]]
        print(f"{r}: {x['race_id'].nunique()} races, {len(x)} runners, ${x['stake_' + r].sum():.2f} staked")
    print("races skipped:", rc["reason"].value_counts().to_dict())


TEXT_COLS = ["logged_at", "checked_at", "date", "venue", "start_time", "horse", "going", "rs_label", "settled_at", "reason", "run_id", "race_id"]


def _read_csv(path, cols):
    if os.path.exists(path):
        df = pd.read_csv(path, low_memory=False, dtype={c: object for c in TEXT_COLS})
        for c in cols:
            if c not in df.columns:
                df[c] = np.nan
        return df[cols]
    return pd.DataFrame(columns=cols)


def meeting_bias(d):
    """Per race: how the EARLIER races at the same meeting (same date and venue, earlier start) ran against the trip map forecast.
    prev_races = earlier races with a result, a forecast for every runner and a single winner; prev_win_first_third = share of those won from the first
    third of the forecast; prev_win_sp = mean forecast position of the winners (0 = leader, 1 = last; 0.5 is neutral); prev_top3_sp = the same for the
    first three. Tested 4 Nov 2026: no carry-over in the backtest, logged to check it forward."""
    x = d[(~d["nogap"]) & (d["n"] >= MIN_FIELD)].copy()
    x["st"] = pd.to_datetime(x["start_time"], utc=True, errors="coerce")
    x["w"] = num(x["won"])
    x["fp"] = num(x["finish_position"])
    nw = x.groupby("race_id")["w"].transform(lambda s: (s == 1).sum())
    x = x[nw == 1]
    win = x[x["w"] == 1].groupby("race_id").agg(date=("date", "first"), venue=("venue", "first"), st=("st", "first"), wsp=("sp", "first"))
    top3 = x[x["fp"] <= 3].groupby("race_id")["sp"].mean().rename("t3sp")
    win = win.join(top3)
    out = {}
    for rid, r in d.drop_duplicates("race_id").set_index("race_id").iterrows():
        st = pd.to_datetime(r["start_time"], utc=True, errors="coerce")
        prev = win[(win["date"] == r["date"]) & (win["venue"] == r["venue"]) & (win["st"] < st)]
        out[rid] = (len(prev), (prev["wsp"] <= FIRST_THIRD + 1e-9).mean() if len(prev) else np.nan, prev["wsp"].mean() if len(prev) else np.nan,
                    prev["t3sp"].mean() if len(prev) else np.nan)
    return out


def cmd_log(a):
    now = now_utc(a.now)
    date = a.date or melb(now).strftime("%Y-%m-%d")
    gaps, gen = read_gaps(a.trip_map)
    rn = read_runners(date)
    if rn.empty:
        print("no runners for", date)
        return
    d, rc = evaluate(rn, gaps, "fixed", read_overrides())
    ran = rn.assign(ran=(num(rn["interim_resulted"]).fillna(0) == 1) | (num(rn["resulted"]).fillna(0) == 1)).groupby("race_id")["ran"].any()
    rc["st"] = pd.to_datetime(rc["start_time"], utc=True, errors="coerce")
    rc["mins"] = (rc["st"] - now).dt.total_seconds() / 60
    rc = rc[(rc["mins"] >= LOG_MIN_MINS) & (rc["mins"] <= LOG_MAX_MINS) & ~rc["race_id"].map(ran).fillna(False)]
    if rc.empty:
        print("no race jumping in the next", LOG_MAX_MINS, "minutes")
        return
    bets = _read_csv(BETS_LOG, BET_COLS)
    races = _read_csv(RACES_LOG, RACE_COLS)
    ids = set(rc["race_id"])
    sids = {str(i) for i in ids}  # logs are read as text, runners.csv ids as numbers: compare as text or a re-log never replaces the earlier rows
    bets = bets[~bets["race_id"].astype(str).isin(sids)]
    races = races[~races["race_id"].astype(str).isin(sids)]
    stamp = now.strftime("%Y-%m-%dT%H:%M:%SZ")
    mins = rc.set_index("race_id")["mins"]
    new_races = rc.assign(checked_at=stamp, mins_to_jump=rc["mins"].round(1))[RACE_COLS]
    x = d[d["race_id"].isin(ids) & (d["v1"] | d["v2"])]
    mb = meeting_bias(d)
    nb = pd.DataFrame({
        "logged_at": stamp, "mins_to_jump": x["race_id"].map(mins).round(1), "date": x["date"], "venue": x["venue"], "race": x["race"], "race_id": x["race_id"],
        "run_id": x["rid"], "start_time": x["start_time"], "horse": x["horse"], "tab_number": x["tab_number"], "barrier": x["barrier"], "price_logged": x["price"],
        "v1": x["v1"].astype(int), "v2": x["v2"].astype(int), "stake_v1": x["stake_v1"].round(2), "stake_v2": x["stake_v2"].round(2), "proj": x["proj"],
        "top_proj": x["top"], "off_top": x["off"].round(2), "gap": x["gap"], "gap_rank": x["rk"], "field_n": x["n"], "sp_frac": x["sp"].round(3),
        "top_is_bet": x["top_is_bet"].astype(int), "n_qual_within1": x["n_qual_within1"], "going": x["going"], "rs_label": x["rs_label"],
        "meeting_min_prize": x["meet_min"], "race_prize": x["prize_money"],
        "prev_races": x["race_id"].map(lambda r: mb[r][0]), "prev_win_first_third": x["race_id"].map(lambda r: round(mb[r][1], 3) if mb[r][0] else np.nan),
        "prev_win_sp": x["race_id"].map(lambda r: round(mb[r][2], 3) if mb[r][0] else np.nan), "prev_top3_sp": x["race_id"].map(lambda r: round(mb[r][3], 3) if mb[r][0] else np.nan),
        "won": np.nan, "finish_position": np.nan, "sp_final": np.nan, "void": 0, "settled_at": np.nan})[BET_COLS]
    bets = pd.concat([bets, nb], ignore_index=True) if len(bets) else nb
    races = pd.concat([races, new_races], ignore_index=True) if len(races) else new_races
    bets.to_csv(BETS_LOG, index=False)
    races.to_csv(RACES_LOG, index=False)
    print(f"logged {len(ids)} race(s): v1 {int(nb['v1'].sum())} bets, v2 {int(nb['v2'].sum())} bets (trip map {gen})")


def cmd_settle(a):
    bets = _read_csv(BETS_LOG, BET_COLS)
    if bets.empty:
        print("nothing logged")
        return
    rn = read_runners()
    rn["run_id"] = num(rn["run_id"])
    rn = rn[rn["run_id"].notna()].drop_duplicates("run_id", keep="last").set_index("run_id")
    stamp = pd.Timestamp.now("UTC").strftime("%Y-%m-%dT%H:%M:%SZ")
    n_set = n_void = n_sp = 0
    for i, r in bets.iterrows():
        rid = num(pd.Series([r["run_id"]])).iloc[0]
        if rid not in rn.index:
            continue
        x = rn.loc[rid]
        if pd.isna(r["won"]):
            if num(pd.Series([x["scratched"]])).fillna(0).iloc[0] == 1:
                bets.at[i, "void"] = 1
                bets.at[i, "settled_at"] = stamp
                n_void += 1
                continue
            w = num(pd.Series([x["won"]])).iloc[0]
            if pd.notna(w):
                bets.at[i, "won"] = int(w)
                bets.at[i, "finish_position"] = num(pd.Series([x["finish_position"]])).iloc[0]
                bets.at[i, "settled_at"] = stamp
                n_set += 1
        if pd.notna(bets.at[i, "won"]) and pd.isna(r["sp_final"]):
            sp = num(pd.Series([x["starting_price_sp"]])).iloc[0]
            if pd.notna(sp):
                bets.at[i, "sp_final"] = sp
                n_sp += 1
    bets.to_csv(BETS_LOG, index=False)
    print(f"settled {n_set} bet(s), {n_void} void (scratched), {n_sp} starting price(s) filled; {int(bets['won'].isna().sum() - bets['void'].fillna(0).sum())} still open")


def cmd_snapshot(a):
    t = json.load(open(a.trip_map))
    today = melb(now_utc(a.now)).strftime("%Y-%m-%d")
    by = {}
    for k, v in t.get("races", {}).items():
        if v.get("date", "") >= today:
            by.setdefault(v["date"], {})[k] = {"venue": v["venue"], "race": v["race"], "distance": v.get("distance"), "going": v.get("going"), "state": v.get("state"),
                                              "runners": [{"rid": r["rid"], "name": r["name"], "barrier": r["barrier"], "gap": r["gap"], "lane": r.get("lane"),
                                                           "nHist": r.get("nHist")} for r in v["runners"]]}
    os.makedirs(ARCHIVE_DIR, exist_ok=True)
    import io
    for date, races in by.items():
        raw = json.dumps({"generated": t.get("generated"), "date": date, "races": races}, separators=(",", ":")).encode()
        buf = io.BytesIO()
        with gzip.GzipFile(fileobj=buf, mode="wb", mtime=0) as f:  # mtime 0: same content gives the same bytes, so an unchanged forecast makes no commit
            f.write(raw)
        path = os.path.join(ARCHIVE_DIR, f"{date}.json.gz")
        if not (os.path.exists(path) and open(path, "rb").read() == buf.getvalue()):
            open(path, "wb").write(buf.getvalue())
    for fn in sorted(os.listdir(ARCHIVE_DIR))[:-240]:  # keep about 8 months
        os.remove(os.path.join(ARCHIVE_DIR, fn))
    print("archived trip map for", sorted(by))


def _summ(b, rule, price_col):
    s = b[b[rule] == 1].copy()
    s = s[s["void"].fillna(0) != 1]
    s = s[s["won"].notna()]
    st = s[f"stake_{rule}"]
    ret = np.where(s["won"] == 1, st * s[price_col], 0.0)
    out = {"races": int(s["race_id"].nunique()), "bets": int(len(s)), "wins": int((s["won"] == 1).sum()), "staked": round(float(st.sum()), 2),
           "returned": round(float(ret.sum()), 2)}
    out["profit"] = round(out["returned"] - out["staked"], 2)
    out["roi_pct"] = round(out["profit"] / out["staked"] * 100, 1) if out["staked"] else None
    return out


def _going_num(g):
    return pd.to_numeric(g.astype(str).str.extract(r"(\d+)")[0], errors="coerce")


# segments tracked in the forward test (named after the 4 Nov 2026 backtest cuts; judge them here, not on the 30 days they were found in)
SEGMENTS = [
    ("All bets", lambda b: b["v1"].notna()),
    ("Meeting minimum prize $30k+", lambda b: num(b["meeting_min_prize"]) >= 30000),
    ("Meeting minimum prize $40k+", lambda b: num(b["meeting_min_prize"]) >= 40000),
    ("Meeting minimum prize $50k+", lambda b: num(b["meeting_min_prize"]) >= 50000),
    ("Good or firm going (1 to 4)", lambda b: _going_num(b["going"]) <= 4),
    ("$30k+ and good/firm", lambda b: (num(b["meeting_min_prize"]) >= 30000) & (_going_num(b["going"]) <= 4)),
    ("$40k+ and good/firm", lambda b: (num(b["meeting_min_prize"]) >= 40000) & (_going_num(b["going"]) <= 4)),
    ("Field of 8 or more", lambda b: num(b["field_n"]) >= 8),
    ("Field of 5 to 7", lambda b: num(b["field_n"]) <= 7),
    ("$40k+ and field of 8+", lambda b: (num(b["meeting_min_prize"]) >= 40000) & (num(b["field_n"]) >= 8)),
    # meeting bias: did earlier winners at the meeting come from the first third of the forecast? (no carry-over in the 4 Nov backtest)
    ("3+ earlier races, 40%+ won from first third", lambda b: (num(b["prev_races"]) >= 3) & (num(b["prev_win_first_third"]) >= 0.4)),
    ("3+ earlier races, under 25% won from first third", lambda b: (num(b["prev_races"]) >= 3) & (num(b["prev_win_first_third"]) < 0.25)),
    ("3+ earlier races, winners forecast at the back (mean 0.55+)", lambda b: (num(b["prev_races"]) >= 3) & (num(b["prev_win_sp"]) >= 0.55)),
]


def _segments(b):
    out = []
    for name, f in SEGMENTS:
        try:
            m = f(b).fillna(False)
        except Exception:
            continue
        row = {"segment": name}
        for rule in ("v1", "v2"):
            row[rule] = _summ(b[m], rule, "price_logged")
        out.append(row)
    return out


def build_report(b, races):
    b = b.copy()
    b["price_sp"] = b["sp_final"].fillna(b["price_logged"])
    rep = {}
    for rule in ("v1", "v2"):
        rep[rule] = {"at_logged_price": _summ(b, rule, "price_logged"), "at_starting_price": _summ(b, rule, "price_sp")}
        by_day = []
        for dte, g in b.groupby("date"):
            s = _summ(g, rule, "price_logged")
            if s["bets"]:
                by_day.append({"date": dte, **s})
        rep[rule]["by_day"] = by_day
    rep["segments"] = _segments(b)
    rep["races_checked"] = int(len(races))
    rep["races_with_reason"] = races["reason"].value_counts().to_dict() if len(races) else {}
    rep["open_bets"] = int(b["won"].isna().sum() - b["void"].fillna(0).sum()) if len(b) else 0
    rep["first_date"] = str(b["date"].min()) if len(b) else None
    rep["last_date"] = str(b["date"].max()) if len(b) else None
    return rep


def write_report(rep, path_md=REPORT_MD, path_json=SUMMARY_JSON):
    json.dump(rep, open(path_json, "w"), indent=1)
    L = ["# Volume rules tracker", "",
         "Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.", "",
         f"Logged {rep['first_date']} to {rep['last_date']}; races checked {rep['races_checked']}; bets still open {rep['open_bets']}.", "",
         "| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |", "|---|---|---|---|---|---|---|---|---|"]
    for rule, name in (("v1", "Volume v1"), ("v2", "Volume v2")):
        a, s = rep[rule]["at_logged_price"], rep[rule]["at_starting_price"]
        L.append(f"| {name} | {a['races']} | {a['bets']} | {a['wins']} | ${a['staked']:.0f} | ${a['returned']:.0f} | ${a['profit']:.0f} | {a['roi_pct']}% | {s['roi_pct']}% |")
    L += ["", "## By day (at logged price)", "", "| Date | v1 bets | v1 profit | v2 bets | v2 profit |", "|---|---|---|---|---|"]
    d1 = {x["date"]: x for x in rep["v1"]["by_day"]}
    d2 = {x["date"]: x for x in rep["v2"]["by_day"]}
    for dte in sorted(set(d1) | set(d2)):
        a, b2 = d1.get(dte), d2.get(dte)
        L.append(f"| {dte} | {a['bets'] if a else 0} | ${a['profit'] if a else 0:.0f} | {b2['bets'] if b2 else 0} | ${b2['profit'] if b2 else 0:.0f} |")
    L += ["", "## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)", "",
          "| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI |", "|---|---|---|---|---|---|---|"]
    for sg in rep.get("segments", []):
        a, c = sg["v1"], sg["v2"]
        L.append(f"| {sg['segment']} | {a['bets']} | ${a['profit']:.0f} | {a['roi_pct']}% | {c['bets']} | ${c['profit']:.0f} | {c['roi_pct']}% |")
    L += ["", "## Races checked without a bet, by reason", ""] + [f"- {k}: {v}" for k, v in rep["races_with_reason"].items()]
    open(path_md, "w").write("\n".join(L) + "\n")


def cmd_report(a):
    b = _read_csv(BETS_LOG, BET_COLS)
    races = _read_csv(RACES_LOG, RACE_COLS)
    if b.empty:
        print("no bets logged yet")
        return
    rep = build_report(b, races)
    write_report(rep)
    print(open(REPORT_MD).read())


def cmd_backtest(a):
    gaps, gen = read_gaps(a.trip_map)
    rn = read_runners()
    # only dates the trip map covers and where results exist
    dates = sorted(set(rn["date"]))
    ids_with_gap = set(gaps)
    rn["rid"] = num(rn["run_id"]).astype("Int64").astype(str)
    covered = rn[rn["rid"].isin(ids_with_gap)]["date"].unique()
    rn = rn[rn["date"].isin(covered)]
    if a.date_from:
        rn = rn[rn["date"] >= a.date_from]
    if a.date_to:
        rn = rn[rn["date"] <= a.date_to]
    d, rc = evaluate(rn, gaps, "sp", read_overrides())
    # resulted races with exactly one winner
    won = d.assign(w=num(d["won"])).groupby("race_id")["w"].agg(["count", "sum", "size"])
    done = won[(won["count"] == won["size"]) & (won["sum"] == 1)].index
    d = d[d["race_id"].isin(done)]
    print(f"backtest {d['date'].min()} to {d['date'].max()}, {d['race_id'].nunique()} resulted races, trip map generated {gen}")
    for rule, name in (("v1", "Volume v1"), ("v2", "Volume v2")):
        s = d[d[rule]].copy()
        st = s[f"stake_{rule}"]
        ret = np.where(num(s["won"]) == 1, st * s["price"], 0.0)
        print(f"{name}: races {s['race_id'].nunique()}, bets {len(s)}, wins {int((num(s['won']) == 1).sum())}, staked ${st.sum():.0f}, profit ${ret.sum() - st.sum():.0f}, ROI {(ret.sum() / st.sum() - 1) * 100:.1f}% at starting price")


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("cmd", choices=["list", "log", "settle", "snapshot", "report", "backtest"])
    p.add_argument("--date")
    p.add_argument("--now", help="pretend it is this UTC time (testing)")
    p.add_argument("--trip-map", default=TRIP_MAP)
    p.add_argument("--from", dest="date_from")
    p.add_argument("--to", dest="date_to")
    a = p.parse_args()
    {"list": cmd_list, "log": cmd_log, "settle": cmd_settle, "snapshot": cmd_snapshot, "report": cmd_report, "backtest": cmd_backtest}[a.cmd](a)


if __name__ == "__main__":
    main()
