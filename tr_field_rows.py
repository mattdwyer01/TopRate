"""tr_field_rows.py -- TopRate is the PRIMARY source of the declared field and its numbers; racing.com (rc_field_rows.py) is the backup.

Reads data/tr_fields/<date>.json (written by toprate_race_fetch.py) into the runners frame:
  * a runner already in the frame (matched on date, normalised venue, race number, then horse name, then tab number) gets TopRate's
    numbers and declared-field columns and field_source 'toprate.au'. Its run_id and race_id are NEVER changed (the projection log, results
    and payload key on them), and a resulted row is never touched. A scratching is only ever set, never cleared.
  * a race with no rows at all is created from TopRate with TopRate's own race_id / run_id.
  * a runner TopRate lists that the race does not have yet (a late entry) is added only if its tab number is free in that race.
A file older than MAX_AGE_HOURS (the fetch has been failing) is ignored, so racing.com simply carries on as before.

Usage (dry run, prints counts, writes nothing):  python tr_field_rows.py DATE [DATE ...]
"""
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path

from rc_field_rows import norm_venue

DIR = Path(__file__).parent / "data" / "tr_fields"
MAX_AGE_HOURS = 30
SOURCE = "toprate.au"
DROPPED = "racing.com (not in toprate field)"   # a racing.com nomination TopRate does not list: scratched, restored if TopRate lists it later

# runner column <- fetcher row key. Numbers are always overwritten (TopRate is their only source).
NUMBER_COLUMNS = {
    "wpr_nett": "wpr_nett", "toprate_rating": "toprate_rating", "speed_rating": "speed_rating", "pfm_score": "pfm_score",
    "pfm_score_rank": "pfm_score_rank", "jockey_rating": "jockey_rating", "toprate_price": "toprate_price",
}
# Declared-field columns TopRate now owns on a row that has not been resulted.
DECLARED_COLUMNS = {
    "barrier": "barrier", "jockey": "jockey", "trainer": "trainer", "tab_number": "tab_number", "weight_carried": "weight",
    "horse_age": "horse_age", "horse_sex": "horse_sex", "silk_url": "silk_url", "handicap_rating": "handicap_rating",
}
# Filled only when the row has nothing (TAB writes prices later and wins; the race facts are the same on both sources).
FILL_IF_BLANK = {
    "horse_id": "horse_id", "fixed_win_price": "fixed_win_price", "open_price": "fixed_win_opening", "going": "going",
    "race_class": "race_class", "race_name": "race_name", "distance": "distance", "prize_money": "prize_money",
    "start_time": "start_time", "state": "state", "track_grading": "track_grading",
}


def _hn(s):
    return re.sub(r"[^a-z0-9]", "", str(s or "").lower())


def _blank(v):
    return v is None or str(v).strip() in ("", "nan", "None", "NaT")


def load(date_str, now=None):
    """The fetched rows for a date, or [] if the file is missing, unreadable or older than MAX_AGE_HOURS."""
    try:
        d = json.loads((DIR / f"{date_str}.json").read_text())
        fetched = datetime.fromisoformat(str(d.get("fetched", "")).replace("Z", "+00:00"))
        if fetched.tzinfo is None:
            fetched = fetched.replace(tzinfo=timezone.utc)
        age = ((now or datetime.now(timezone.utc)) - fetched).total_seconds() / 3600
        return d.get("rows", []) if age <= MAX_AGE_HOURS else []
    except Exception:
        return []


def _set(df, i, c, v):
    try:
        df.at[i, c] = v
    except (TypeError, ValueError):
        df.at[i, c] = str(v)


def _new_row(r):
    return {
        "date": r["date"], "venue": r["venue"], "state": r.get("state"), "race": r["race_no"], "race_id": r["race_id"],
        "race_name": r.get("race_name"), "distance": r.get("distance"), "race_class": r.get("race_class"),
        "prize_money": r.get("prize_money"), "going": r.get("going"), "track_grading": r.get("track_grading"),
        "start_time": r.get("start_time"), "run_id": r["run_id"], "horse_id": r.get("horse_id"),
        "scratched": 1 if r.get("scratched") else 0, "tab_number": r.get("tab_number"), "barrier": r.get("barrier"),
        "horse": r.get("horse"), "jockey": r.get("jockey"), "trainer": r.get("trainer"), "weight_carried": r.get("weight"),
        "horse_age": r.get("horse_age"), "horse_sex": r.get("horse_sex"), "silk_url": r.get("silk_url"),
        "handicap_rating": r.get("handicap_rating"), "fixed_win_price": r.get("fixed_win_price"),
        "open_price": r.get("fixed_win_opening"), "resulted": 0, "interim_resulted": 0, "field_source": SOURCE,
        **{col: r.get(key) for col, key in NUMBER_COLUMNS.items()},
    }


def merge_tr_fields(runners_df, date_str, dry_run=False, now=None):
    """Return (runners_df, stats). With dry_run the frame is returned unchanged and only stats are filled.

    Race numbers are NOT trusted as a key (TopRate and racing.com number some meetings differently, found 14 Oct 2026: 75 horses twice at a
    venue on one day). A horse cannot run twice at a venue on a day, so a runner is matched on (venue, horse name) first, whatever race number
    either source gives it; the row keeps the race it already has. Only a TopRate race with no runner matched anywhere is created."""
    import pandas as pd
    rows = [r for r in load(date_str, now) if r.get("race_id") and r.get("run_id")]
    stats = {"tr_rows": len(rows), "updated": 0, "renumbered": 0, "added_rows": 0, "added_races": 0, "unmatched_skipped": 0,
             "resulted_skipped": 0, "changed": {c: 0 for c in list(NUMBER_COLUMNS) + list(DECLARED_COLUMNS)}}
    if not rows:
        return runners_df, stats
    out = runners_df.copy()
    day = out["date"].astype(str).str[:10] == date_str if len(out) else pd.Series([], dtype=bool)
    by_vname, by_tab, races, taken_ids = {}, {}, {}, set(out["run_id"].astype(str)) if len(out) else set()
    for i in out.index[day]:
        v, n = norm_venue(out.at[i, "venue"]), str(out.at[i, "race"])
        races.setdefault((v, n), str(out.at[i, "race_id"]))
        by_vname.setdefault((v, _hn(out.at[i, "horse"])), []).append(i)
        t = out.at[i, "tab_number"] if "tab_number" in out.columns else None
        if not _blank(t) and str(t) not in ("0", "0.0"):
            by_tab[(v, n, str(int(float(t))))] = i

    def pick(v, n, hn):
        """The live row of this horse at this venue: the one in the race number TopRate gives it, else a row TopRate already owns, else the first."""
        lst = by_vname.get((v, hn))
        if not lst:
            return None
        for i in lst:
            if str(out.at[i, "race"]) == n:
                return i
        for i in lst:
            if str(out.at[i, "field_source"]) == SOURCE:
                return i
        return lst[0]

    # which live race (number, race_id) each TopRate race maps to: the one most of its runners already sit in; none -> a race to create
    live_race = {}
    tally = {}
    for r in rows:
        v, n = norm_venue(r.get("venue")), str(r.get("race_no"))
        i = pick(v, n, _hn(r.get("horse")))
        if i is not None:
            k = (str(out.at[i, "race"]), str(out.at[i, "race_id"]))
            tally.setdefault((v, n), {}).setdefault(k, 0)
            tally[(v, n)][k] += 1
    for key, cnt in tally.items():
        live_race[key] = max(cnt, key=cnt.get)

    new_rows = []
    created = set()
    for r in rows:
        v, n = norm_venue(r.get("venue")), str(r.get("race_no"))
        i = pick(v, n, _hn(r.get("horse")))
        if i is None and (v, n) in live_race:               # a renamed horse: saddle number inside the race it maps to
            i = by_tab.get((v, live_race[(v, n)][0], str(r.get("tab_number"))))
        elif i is None and (v, n) in races:
            i = by_tab.get((v, n, str(r.get("tab_number"))))
        if i is None:
            if (v, n) in live_race or (v, n) in races:     # late entry into an existing race, only if its saddle number is free
                ln, lid = live_race.get((v, n), (n, races.get((v, n))))
                if r.get("scratched") or (v, ln, str(r.get("tab_number"))) in by_tab or str(r["run_id"]) in taken_ids:
                    stats["unmatched_skipped"] += 1
                    continue
                row = _new_row(r)
                row["race"], row["race_id"] = r.get("race_no") if ln == n else int(float(ln)), lid
                new_rows.append(row)
            else:                                           # a race nobody has: TopRate creates it with its own ids
                if str(r["run_id"]) in taken_ids:
                    continue
                new_rows.append(_new_row(r))
                created.add((v, n))
            taken_ids.add(str(r["run_id"]))
            stats["added_rows"] += 1
            continue
        if str(out.at[i, "resulted"]) in ("1", "1.0"):
            stats["resulted_skipped"] += 1
            continue
        stats["updated"] += 1
        if str(out.at[i, "field_source"]) == DROPPED and not r.get("scratched"):
            _set(out, i, "scratched", 0)                    # TopRate lists it after all (a late acceptance)
        if str(out.at[i, "race"]) != n:
            stats["renumbered"] += 1
        for col, key in NUMBER_COLUMNS.items():
            val = r.get(key)
            if val is not None and col in out.columns:
                old = out.at[i, col]
                if _blank(old) or float(old) != float(val):
                    stats["changed"][col] += 1
                    _set(out, i, col, val)
        for col, key in DECLARED_COLUMNS.items():
            val = r.get(key)
            if val is not None and col in out.columns and str(out.at[i, col]) != str(val):
                stats["changed"][col] += 1
                _set(out, i, col, val)
        for col, key in FILL_IF_BLANK.items():
            val = r.get(key)
            if val is not None and col in out.columns and _blank(out.at[i, col]):
                _set(out, i, col, val)
        if r.get("scratched") and str(out.at[i, "scratched"]) not in ("1", "1.0"):
            _set(out, i, "scratched", 1)
        if "field_source" in out.columns:
            _set(out, i, "field_source", SOURCE)
    if new_rows:
        import warnings
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", category=FutureWarning)
            out = pd.concat([out, pd.DataFrame(new_rows)], ignore_index=True)
        stats["added_races"] = len(created)
    return (runners_df if dry_run else out), stats


# --- runner pages (data/tr_runners/<date>.json.gz, toprate_runner_fetch.py) -------------------------------------------------------------
RUNNER_DIR = Path(__file__).parent / "data" / "tr_runners"
# TopRate stats block -> runners.csv column prefix (<prefix>_starts / _wins / _places). The first six are the old toprate_json_capture columns.
STATS_BLOCKS = {
    "firstUp": "stats_first_up", "secondUp": "stats_second_up", "track": "stats_track", "sireDry": "stats_sire_dry",
    "sireWet": "stats_sire_wet", "currentJockey": "stats_current_jockey",
    "career": "tr_stats_career", "distance": "tr_stats_distance", "trackDistance": "tr_stats_track_distance", "firm": "tr_stats_firm",
    "good": "tr_stats_good", "soft": "tr_stats_soft", "heavy": "tr_stats_heavy", "synthetic": "tr_stats_synthetic", "jumps": "tr_stats_jumps",
    "sireOfDamDry": "tr_stats_sire_of_dam_dry", "sireOfDamWet": "tr_stats_sire_of_dam_wet",
}
BIO_COLUMNS = ("horse_country", "horse_colour", "horse_foaled", "dam", "dam_country", "owners", "training_location", "weight_handicap_today")
RUNNER_COLUMNS = ([f"{p}_{k}" for p in STATS_BLOCKS.values() for k in ("starts", "wins", "places")]
                  + ["rating_career_best_wpr", "rating_career_best_rank", "rating_career_next_wpr", "rating_career_next_rank"] + list(BIO_COLUMNS))


PAST_DIR = Path(__file__).parent / "data" / "tr_past"


def merge_tr_past(runners_df):
    """Fill blank TopRate numbers on rows of races that have already run from data/tr_past/<date>.json (toprate_past_fetch.py), matched on run_id.
    Only blanks are filled and a value already there is never replaced. Returns (frame, cells filled)."""
    import pandas as pd
    if not PAST_DIR.exists() or "run_id" not in runners_df.columns:
        return runners_df, 0
    rid = pd.to_numeric(runners_df["run_id"], errors="coerce")
    pos = {int(v): i for i, v in zip(runners_df.index, rid) if pd.notna(v)}
    filled = 0
    for f in sorted(PAST_DIR.glob("*.json")):
        try:
            rows = json.loads(f.read_text()).get("rows", {})
        except Exception:
            continue
        for k, vals in rows.items():
            i = pos.get(int(k))
            if i is None:
                continue
            for c, v in vals.items():
                if not c.startswith("_") and c in runners_df.columns and _blank(runners_df.at[i, c]):
                    _set(runners_df, i, c, v)
                    filled += 1
    return runners_df, filled


def remap_ids(runners_df):
    """Replace racing.com / placeholder run_id and race_id with TopRate's own for rows of days scanned by `toprate_past_fetch.py --scan-from` (the
    "_id" identity in data/tr_past/<date>.json), matched on date, normalised venue and horse name. A row already carrying the TopRate run_id is left
    alone, so this is idempotent. Returns (frame, {old run_id: (new run_id, new race_id)})."""
    import pandas as pd
    mapping = {}
    if not PAST_DIR.exists() or "run_id" not in runners_df.columns:
        return runners_df, mapping
    dcol = runners_df["date"].astype(str).str[:10]
    for f in sorted(PAST_DIR.glob("*.json")):
        try:
            d = json.loads(f.read_text())
        except Exception:
            continue
        ident = {k: v["_id"] for k, v in d.get("rows", {}).items() if isinstance(v.get("_id"), dict)}
        if not ident:
            continue
        key = {(norm_venue(v["venue"]), _hn(v["horse"])): (int(k), int(v["race_id"])) for k, v in ident.items()}
        have = {int(k) for k in ident}
        rows = runners_df.index[dcol == d.get("date", f.stem)]
        for i in rows:
            old = runners_df.at[i, "run_id"]
            if pd.isna(old) or int(old) in have:
                continue
            new = key.get((norm_venue(runners_df.at[i, "venue"]), _hn(runners_df.at[i, "horse"])))
            if new:
                mapping[int(old)] = new
                runners_df.at[i, "run_id"] = new[0]
                runners_df.at[i, "race_id"] = new[1]
    return runners_df, mapping


def remap_projection_log(mapping):
    """Re-key wpr_projection_log.csv.gz rows from the old run_id / race_id to the TopRate ones (same mapping as remap_ids)."""
    if not mapping:
        return 0
    from projection import projlog as plog
    lg = plog.load()
    hit = lg.run_id.isin(mapping)
    if not hit.any():
        return 0
    new = lg.loc[hit, "run_id"].map(mapping)
    lg.loc[hit, "race_id"] = [m[1] for m in new]
    lg.loc[hit, "run_id"] = [m[0] for m in new]
    lg.sort_values(["date", "race_id", "run_id"]).to_csv(plog.PATH, index=False, compression="gzip", float_format="%.2f")
    return int(hit.sum())


def _melbourne_today():
    from zoneinfo import ZoneInfo
    return datetime.now(ZoneInfo("Australia/Melbourne")).date().isoformat()


def load_runners(date_str):
    import gzip
    try:
        with gzip.open(RUNNER_DIR / f"{date_str}.json.gz", "rt") as fh:
            return json.load(fh).get("rows", {})
    except Exception:
        return {}


def runner_values(rec):
    """Flat {runners column: value} for one fetched runner record."""
    out = {}
    stats = rec.get("stats") or {}
    for src, prefix in STATS_BLOCKS.items():
        block = stats.get(src)
        if isinstance(block, dict):
            for k in ("starts", "wins", "places"):
                if block.get(k) is not None:
                    out[f"{prefix}_{k}"] = block[k]
    for prof in rec.get("rating_profiles") or []:
        if not isinstance(prof, dict) or (prof.get("domain") or {}).get("period") != "Career":
            continue
        allb = prof.get("all") or {}
        for which, col in (("best", "rating_career_best"), ("next", "rating_career_next")):
            b = allb.get(which)
            if isinstance(b, dict):
                for k in ("wpr", "rank"):
                    if b.get(k) is not None:
                        out[f"{col}_{k}"] = b[k]
        break
    for c in BIO_COLUMNS:
        if rec.get(c) is not None:
            out[c] = rec[c]
    return out


def _has_run(df, i):
    """True if this row's race has been run or resulted, by ANY signal: resulted, interim_resulted (TAB poller), a finish/won value, or a start time in the
    past. TopRate's runner-page stats are current-state aggregates and may already include that run, so such a row is never written."""
    for col in ("resulted", "interim_resulted"):
        if col in df.columns and str(df.at[i, col]) in ("1", "1.0"):
            return True
    for col in ("won", "finish_position"):
        if col in df.columns and not _blank(df.at[i, col]):
            return True
    if "start_time" in df.columns and not _blank(df.at[i, "start_time"]):
        try:
            t = datetime.fromisoformat(str(df.at[i, "start_time"]).replace("Z", "+00:00"))
            if t.tzinfo is None:
                t = t.replace(tzinfo=timezone.utc)
            return t <= datetime.now(timezone.utc)
        except ValueError:
            return False
    return False


def merge_tr_runners(runners_df, date_str, dry_run=False):
    """Fill the runner-page columns of UPCOMING, unresulted rows. TopRate's stats and rating profiles are current-state aggregates: a row whose
    race date is before today (Melbourne) or that has a result is never touched, so a past row can never pick up a figure from after its race.
    Rows are matched on (venue, horse name). Returns (runners_df, stats)."""
    import pandas as pd
    recs = load_runners(date_str)
    stats = {"records": len(recs), "matched": 0, "filled": 0, "skipped_past_or_resulted": 0, "unmatched": 0}
    if not recs or not len(runners_df):
        return runners_df, stats
    if date_str < _melbourne_today():
        stats["skipped_past_or_resulted"] = len(recs)
        return runners_df, stats
    out = runners_df.copy()
    for c in RUNNER_COLUMNS:
        if c not in out.columns:
            out[c] = None
    day = out["date"].astype(str).str[:10] == date_str
    idx = {}
    for i in out.index[day]:
        if str(out.at[i, "scratched"]) in ("1", "1.0"):
            continue
        idx.setdefault((norm_venue(out.at[i, "venue"]), _hn(out.at[i, "horse"])), []).append(i)
    for rec in recs.values():
        if rec.get("empty"):
            continue
        rows = idx.get((norm_venue(rec.get("venue")), _hn(rec.get("horse"))))
        if not rows:
            stats["unmatched"] += 1
            continue
        stats["matched"] += 1
        vals = runner_values(rec)
        for i in rows[:1]:
            if _has_run(out, i):
                stats["skipped_past_or_resulted"] += 1
                continue
            for col, v in vals.items():
                _set(out, i, col, v)
            stats["filled"] += 1
    return (runners_df if dry_run else out), stats


def flag_unlisted(runners_df, date_str, dry_run=False, now=None):
    """After BOTH merges: in a race TopRate covers, scratch racing.com rows TopRate does not list, and for a horse with several rows at one
    venue keep only the row in the race TopRate puts it in. racing.com's pre-declaration files carry up to 50 nominations per race with the
    same horses repeated across races (15 Oct 2026, Warrnambool), TopRate lists the accepted field. Resulted rows, rows already scratched,
    rows TopRate owns and races TopRate has no runner in are never touched. Returns (runners_df, stats)."""
    import pandas as pd
    rows = load(date_str, now)
    stats = {"unlisted_scratched": 0, "duplicate_rows_scratched": 0}
    if not rows or not len(runners_df):
        return runners_df, stats
    out = runners_df.copy()
    tr_names, tr_venue_n = {}, {}
    for r in rows:
        v = norm_venue(r.get("venue"))
        tr_names.setdefault(v, set()).add(_hn(r.get("horse")))
        if not r.get("scratched"):
            tr_venue_n[v] = tr_venue_n.get(v, 0) + 1
    day = out["date"].astype(str).str[:10] == date_str
    idx = [i for i in out.index[day] if norm_venue(out.at[i, "venue"]) in tr_venue_n and tr_venue_n[norm_venue(out.at[i, "venue"])] >= 4]
    covered = set()       # (venue, race number) that holds at least one row TopRate owns (a runner TopRate lists in that race)
    for i in idx:
        if str(out.at[i, "field_source"]) == SOURCE:
            covered.add((norm_venue(out.at[i, "venue"]), str(out.at[i, "race"])))
    for i in idx:
        v, n, hn = norm_venue(out.at[i, "venue"]), str(out.at[i, "race"]), _hn(out.at[i, "horse"])
        if str(out.at[i, "resulted"]) in ("1", "1.0") or str(out.at[i, "scratched"]) in ("1", "1.0"):
            continue
        if str(out.at[i, "field_source"]) == SOURCE or (v, n) not in covered or hn in tr_names[v]:
            continue
        stats["unlisted_scratched"] += 1
        _set(out, i, "scratched", 1)
        _set(out, i, "field_source", DROPPED)
    # a listed horse with more than one live row at the venue: keep TopRate's row (or the one in the race TopRate says), scratch the rest
    groups = {}
    for i in idx:
        if str(out.at[i, "scratched"]) in ("1", "1.0"):
            continue
        groups.setdefault((norm_venue(out.at[i, "venue"]), _hn(out.at[i, "horse"])), []).append(i)
    for (v, hn), lst in groups.items():
        if len(lst) < 2 or hn not in tr_names[v]:
            continue
        keep = next((i for i in lst if str(out.at[i, "field_source"]) == SOURCE), None)
        if keep is None:
            continue
        for i in lst:
            if i != keep and str(out.at[i, "resulted"]) not in ("1", "1.0"):
                stats["duplicate_rows_scratched"] += 1
                _set(out, i, "scratched", 1)
                _set(out, i, "field_source", DROPPED)
    return (runners_df if dry_run else out), stats


if __name__ == "__main__":
    import pandas as pd
    df = pd.read_csv("runners.csv", low_memory=False)
    for d in sys.argv[1:]:
        res, s = merge_tr_fields(df, d, dry_run=False)   # computed in memory, never saved
        dup = res[res.date.astype(str).str[:10] == d].duplicated(["venue", "race", "horse"]).sum()
        print(d, json.dumps(s), "| duplicate (venue, race, horse) rows after merge:", int(dup),
              "| rows", len(df), "->", len(res))
