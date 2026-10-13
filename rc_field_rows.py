"""rc_field_rows.py -- runner rows for a race from the racing.com declared field (data/rc_fields/<date>.json, written by rc_fields.py).

Used by toprate_daily.fetch_todays_races() for a race whose toprate.au detail fetch failed (403 since Oct 2026) and that has no rows yet.
rows_for(race_meta, date_str) matches the calendar race (venue, number, distance) to a racing.com race and returns row dicts in the
runners-file layout: only what racing.com knows is filled (horse, barrier, weight, rider, trainer, saddle number, silks, scratching);
everything else stays empty and is computed downstream (projection, prices from TAB, results).
"""
import json
import re
from pathlib import Path

DIR = Path(__file__).parent / "data" / "rc_fields"
_SPONSOR = re.compile(r"^(bet365|sportsbet|ladbrokes|picklebet|tab|southside|pointsbet|neds|racing\.?com)\s+", re.I)
_cache = {}


def norm_venue(s):
    n = str(s or "").strip().lower()
    for _ in range(2):
        n = _SPONSOR.sub("", n)
    n = re.sub(r"[^a-z0-9]+", " ", n).strip()
    return re.sub(r"^mount ", "mt ", n)


def _distance_m(v):
    m = re.search(r"(\d+)", str(v or ""))
    return int(m.group(1)) if m else None


RC_RUN_ID_BASE = 7_000_000_000_000   # far above TopRate's own ids (below 2e7); the projection pipeline needs integer run_ids


def numeric_run_id(meeting_code, race_no, slot):
    """Integer run_id for a racing.com-built row: base + meeting*10000 + race*100 + saddle number (slot < 100)."""
    return RC_RUN_ID_BASE + int(meeting_code) * 10000 + int(race_no) * 100 + int(slot)


def load(date_str):
    if date_str not in _cache:
        try:
            _cache[date_str] = json.loads((DIR / f"{date_str}.json").read_text())
        except Exception:
            _cache[date_str] = {"meetings": []}
    return _cache[date_str]


def find_race(date_str, venue, number, distance):
    """(meeting, race) of the racing.com race matching the calendar race, or (None, None)."""
    nv = norm_venue(venue)
    dist = _distance_m(distance)
    for m in load(date_str).get("meetings", []):
        mv = norm_venue(m.get("venue"))
        if not mv or not (mv == nv or mv in nv or nv in mv):
            continue
        races = m.get("races", [])
        same_no = [r for r in races if r.get("race_no") == number and (dist is None or _distance_m(r.get("distance")) in (None, dist))]
        if same_no:
            return m, same_no[0]
        same_dist = [r for r in races if dist is not None and _distance_m(r.get("distance")) == dist]
        if len(same_dist) == 1:
            return m, same_dist[0]
    return None, None


def rows_for(race_meta, date_str):
    m, r = find_race(date_str, race_meta.get("venue"), race_meta.get("number"), race_meta.get("distance"))
    if not r:
        return []
    out = []
    for i, h in enumerate(r.get("runners", [])):
        if h.get("emergency"):          # a reserve, not in the field unless drawn in
            continue
        try:
            slot = int(h.get("tab_number"))
        except (TypeError, ValueError):
            slot = 0
        if not 0 < slot < 50:
            slot = 50 + i % 50          # no usable saddle number: a slot no real number uses
        out.append({
            "date": date_str, "venue": race_meta["venue"], "state": race_meta.get("state"), "race": race_meta["number"],
            "race_id": str(race_meta["raceId"]), "race_name": race_meta.get("name"), "distance": race_meta.get("distance"),
            "race_class": race_meta.get("class") or r.get("class"), "prize_money": race_meta.get("prizeMoney"),
            "going": race_meta.get("going") or r.get("going"), "track_grading": race_meta.get("track_grading"),
            "rail_position": race_meta.get("rail_position"), "start_time": race_meta.get("startTime") or r.get("time"),
            "run_id": numeric_run_id(m["meeting_code"], r["race_no"], slot), "scratched": 1 if h.get("scratched") else 0,
            "tab_number": h.get("tab_number"), "barrier": h.get("barrier"), "horse": h.get("horse"), "horse_id": None,
            "jockey": h.get("jockey"), "trainer": h.get("trainer"), "weight_carried": h.get("weight_kg"),
            "silk_url": h.get("silk_url"),
            "horse_age": h.get("age"), "horse_sex": h.get("sex"), "gear": h.get("gear"), "gear_changes": h.get("gear_changes"),
            "handicap_rating": h.get("rating"), "weight_previous": h.get("weight_prev_kg"), "rc_win_price": h.get("win_price"),
            "fixed_win_price": h.get("win_price"), "open_price": h.get("win_price"), "resulted": 0, "interim_resulted": 0, "field_source": "racing.com",
        })
    return out


RC_RACE_ID_BASE = 7_500_000_000_000   # race_id for a race no earlier row carries (earlier rows keep the id they were built with)

# Declared-field columns that racing.com is the source of: refreshed on rows that have not been resulted. Prices, weights and start times are
# only filled when blank (TAB writes those later and wins).
_REFRESH = ("barrier", "jockey", "trainer", "tab_number", "silk_url", "horse_age", "horse_sex", "gear", "gear_changes", "handicap_rating",
            "weight_previous", "rc_win_price")
_FILL_IF_BLANK = ("weight_carried", "start_time", "going", "race_class", "race_name", "fixed_win_price", "open_price", "state")


def _set(df, i, c, v):
    try:
        df.at[i, c] = v
    except (TypeError, ValueError):
        df.at[i, c] = str(v)


def merge_rc_fields(runners_df, date_str):
    """Bring the declared fields of every racing.com race of `date_str` into the runners frame, without deleting anything.

    A race that already has rows (matched on venue and race number) keeps its race_id; its pending rows are refreshed (scratchings only ever
    set, never cleared) and runners that are new to the field are added. A race with no rows gets rows_for() rows with a race_id from
    RC_RACE_ID_BASE. Returns (runners_df, n_added, n_updated)."""
    import pandas as pd
    day = runners_df["date"].astype(str).str[:10] == date_str if len(runners_df) else pd.Series([], dtype=bool)
    have = runners_df[day] if len(runners_df) else runners_df
    key_of = {}
    if len(have):
        for (v, n), g in have.groupby([have["venue"].map(norm_venue), have["race"].astype(str)]):
            key_of[(v, n)] = str(g["race_id"].iloc[0])
    new_rows, updates = [], {}
    for m in load(date_str).get("meetings", []):
        mv = norm_venue(m.get("venue"))
        for r in m.get("races", []):
            rid = key_of.get((mv, str(r.get("race_no"))))
            meta = {"venue": m.get("venue"), "state": m.get("state"), "number": r.get("race_no"), "name": r.get("name"), "distance": r.get("distance"),
                    "class": r.get("class"), "going": r.get("going"), "startTime": r.get("time"), "prizeMoney": None,
                    "raceId": rid or RC_RACE_ID_BASE + int(m["meeting_code"]) * 100 + int(r["race_no"])}
            for row in rows_for(meta, date_str):
                updates[str(row["run_id"])] = row
                row["_new_race"] = rid is None
    if not updates:
        return runners_df, 0, 0
    ids = runners_df["run_id"].astype(str) if len(runners_df) else pd.Series([], dtype=str)
    pos = {rid: i for i, rid in zip(ids.index, ids)} if len(ids) else {}
    n_up = 0
    out = runners_df.copy()
    for rid, row in updates.items():
        i = pos.get(rid)
        if i is None:
            row = {k: v for k, v in row.items() if k != "_new_race"}
            new_rows.append(row)
            continue
        if str(out.at[i, "resulted"]) in ("1", "1.0"):
            continue
        changed = False
        for c in _REFRESH:
            v = row.get(c)
            if c in out.columns and v is not None and str(out.at[i, c]) != str(v):
                _set(out, i, c, v)
                changed = True
        for c in _FILL_IF_BLANK:
            v = row.get(c)
            cur = out.at[i, c] if c in out.columns else None
            if c in out.columns and v is not None and (cur is None or str(cur).strip() in ("", "nan", "None")):
                _set(out, i, c, v)
                changed = True
        if row.get("scratched") == 1 and str(out.at[i, "scratched"]) not in ("1", "1.0"):
            _set(out, i, "scratched", 1)
            changed = True
        n_up += changed
    if new_rows:
        import warnings
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", category=FutureWarning)
            out = pd.concat([out, pd.DataFrame(new_rows)], ignore_index=True)
    return out, len(new_rows), n_up


if __name__ == "__main__":
    # selftest: a made-up file in a temp dir
    import tempfile
    DIR = Path(tempfile.mkdtemp())
    (DIR / "2026-10-13.json").write_text(json.dumps({"meetings": [{"meeting_code": 1, "venue": "bet365 Park Kilmore", "races": [
        {"race_no": 3, "distance": "1207m", "class": "BM 0-57", "going": "Soft", "time": "x", "runners": [
            {"horse": "A", "horse_code": "9", "barrier": 1, "weight_kg": 55.0, "tab_number": 1, "jockey": "J", "trainer": "T", "scratched": 0, "emergency": 0},
            {"horse": "B", "horse_code": "8", "barrier": 2, "weight_kg": 56.0, "tab_number": 2, "scratched": 1, "emergency": 0},
            {"horse": "R", "horse_code": "7", "emergency": 1}]}]}]}))
    rows = rows_for({"venue": "Kilmore", "number": 3, "distance": 1207, "raceId": 55, "state": "VIC"}, "2026-10-13")
    assert [r["run_id"] for r in rows] == [numeric_run_id(1, 3, 1), numeric_run_id(1, 3, 2)], rows
    assert [r["horse"] for r in rows] == ["A", "B"] and rows[1]["scratched"] == 1 and rows[0]["race_id"] == "55", rows
    assert rows_for({"venue": "Kilmore", "number": 4, "distance": 1500, "raceId": 56}, "2026-10-13") == []
    print("selftest ok")
