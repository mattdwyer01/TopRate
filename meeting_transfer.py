"""meeting_transfer.py -- a meeting moved to another track on race day (Oct 2026).

2 Oct 2026: Cranbourne's night meeting was transferred to Pakenham. toprate.au kept the old Cranbourne races AND
created a new "Pakenham" meeting (new race_ids / run_ids, same fields, race numbers and start times), but the new
copy has no TopRate rating / price, no fixed price, half the jockeys missing and no going. The dashboard showed
Pakenham with those columns blank, plus a duplicate Cranbourne meeting that will never get results (TAB names the
meeting "CRANBOURNE at PAKENHAM", which tab_results_poller.provider_venue_for maps to Pakenham).

merge_transfers(new_df) runs on each Daily fetch's freshly fetched rows (both copies come back from the API):
  - pairs races on the same date with the same race number and start time at different venues whose fields are the
    same horses (>= 80% of the smaller field); the higher race_id is the new copy (toprate.au creates it later)
  - fills the new copy's blank CARRY columns from the old copy by horse_id and records transferred_from (old race_id)
  - drops the old copy, so the dashboard shows one meeting under the new track
Going / track grading are NOT carried (the old track's going is wrong for the new track); TAB conditions fill them.

restore(new_df, removed) puts carried values back after a same-day re-fetch removed the pending rows, in case
toprate.au stops serving the old copy (then there is nothing left to carry from).
"""
import pandas as pd

CARRY = ["toprate_rating", "toprate_price", "speed_rating", "pfm_score", "pfm_score_rank",
         "fixed_win_price", "open_price",
         "jockey", "jockey_win_pct_90d", "jockey_rating", "jockey_starts_90d", "jockey_pot_pct_90d",
         "jockey_lt3l_pct_90d", "jt_combo_win_pct", "jt_combo_rides", "jt_combo_pot_pct", "jt_combo_lt3l_pct"]
MIN_OVERLAP = 0.8


def _blank(s):
    return s.isna() | s.astype(str).str.strip().isin(["", "nan", "None"])


def find_transfers(df):
    """{old race_id: new race_id} for transferred races in df."""
    need = {"race_id", "venue", "race", "start_time", "horse_id", "date"}
    if df is None or df.empty or not need <= set(df.columns):
        return {}
    d = df[df["horse_id"].notna() & df["start_time"].notna()]
    races = (d.groupby("race_id")
               .agg(date=("date", lambda s: str(s.iloc[0])[:10]), venue=("venue", "first"), race=("race", "first"),
                    start=("start_time", "first"), horses=("horse_id", lambda s: frozenset(s.astype(str))))
               .reset_index())
    races["race_n"] = pd.to_numeric(races["race"], errors="coerce")
    races["start"] = pd.to_datetime(races["start"], utc=True, errors="coerce")
    pairs = {}
    for _, g in races.dropna(subset=["race_n", "start"]).groupby(["date", "race_n", "start"]):
        if g["venue"].nunique() < 2:
            continue
        rows = list(g.itertuples(index=False))
        for i, a in enumerate(rows):
            for b in rows[i + 1:]:
                if a.venue == b.venue or min(len(a.horses), len(b.horses)) < 2:
                    continue
                if len(a.horses & b.horses) < MIN_OVERLAP * min(len(a.horses), len(b.horses)):
                    continue
                ka, kb = pd.to_numeric(a.race_id, errors="coerce"), pd.to_numeric(b.race_id, errors="coerce")
                old, new = (a, b) if (ka if pd.notna(ka) else 0) < (kb if pd.notna(kb) else 0) else (b, a)
                pairs[str(old.race_id)] = str(new.race_id)
    return pairs


def merge_transfers(df):
    """Fill the new copy of each transferred race from the old one and drop the old one. Returns (df, pairs)."""
    pairs = find_transfers(df)
    if not pairs:
        return df, pairs
    df = df.copy()
    rid = df["race_id"].astype(str)
    if "transferred_from" not in df.columns:
        df["transferred_from"] = pd.NA
    for old, new in pairs.items():
        o = df[rid == old].assign(_h=lambda x: x["horse_id"].astype(str)).drop_duplicates("_h", keep="last") \
            .set_index("_h")
        m = rid == new
        hid = df.loc[m, "horse_id"].astype(str)
        for c in CARRY:
            if c not in df.columns or c not in o.columns:
                continue
            fill = hid.map(o[c])
            gap = _blank(df.loc[m, c])
            df.loc[gap[gap].index, c] = fill[gap]
        df.loc[m, "transferred_from"] = old
        o0 = df.loc[rid == old].iloc[0]
        n0 = df.loc[m].iloc[0]
        print(f"  Transferred meeting: {o0['venue']} R{o0['race']} (race {old}) -> {n0['venue']} (race {new}); "
              f"filled blanks from the old copy, dropped the old copy")
    return df[~rid.isin(pairs)].reset_index(drop=True), pairs


def removed_values(pending):
    """CARRY values of transferred rows a re-fetch is about to remove, by run_id."""
    if pending is None or pending.empty or "transferred_from" not in pending.columns:
        return pd.DataFrame()
    t = pending[pending["transferred_from"].notna() & ~_blank(pending["transferred_from"])]
    cols = [c for c in CARRY + ["transferred_from"] if c in t.columns]
    return t.assign(_r=t["run_id"].astype(str)).drop_duplicates("_r", keep="last").set_index("_r")[cols]


def restore(df, kept):
    """Fill blanks on re-fetched rows from removed_values() (same run_id)."""
    if kept is None or kept.empty or df is None or df.empty:
        return df
    df = df.copy()
    rid = df["run_id"].astype(str)
    m = rid.isin(kept.index)
    if not m.any():
        return df
    for c in kept.columns:
        if c not in df.columns:
            df[c] = pd.NA
        gap = m & _blank(df[c])
        df.loc[gap, c] = rid[gap].map(kept[c])
    return df
