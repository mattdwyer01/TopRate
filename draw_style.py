"""Draw and style card data (27 Oct 2026, branch claude/draw-style-card).

Per venue, how runners of each barrier and running style have won against the rate their starting price implied, filterable by distance, rail, going and race pace,
plus the rating effect of the draw at that venue (wpr put on the ATW scale of each race with wfa_scale, compared within the race).

  python draw_style.py --build      one-off build of data/venue_draw/<venue>.json.gz and index.json from the results files (2017 to 8 Oct 2026; the results files
                                    carry the 800m position only up to then, so the stats are static until a newer source exists). Takes a few minutes.
  draw_style.apply(runners_df)      daily (toprate_daily Step 3c): runner column `draw_style` = average 800m position (share of the field, 0 = led) over the horse's last 6
                                    earlier runs with 5+ starters, from the runner-page store data/tr_form; blank with under 2 such runs.

Style groups (EDGES): L up to 0.15, OP to 0.30, OP/MF to 0.42, MF to 0.55, MF/BM to 0.70, BM beyond. The frontend (lib/drawStyle.ts) uses the same edges.
Row format in the venue files: [barrier (capped 16), style 0-5, distance group 0-2 (up to 1300m, to 1650m, longer), rail -1..3 (true, out 1-4m, 5-9m, 10m+), going -1..6 (Firm, Good 3, Good 4,
Soft 5, Soft 6, Soft 7+, Heavy), race pace 0-2 (Forward-style runners in the race: 0-1, 2-3, 4+), won, normalised price-implied chance]."""
import argparse
import functools
import gzip
import json
import re
import sys
from pathlib import Path

import numpy as np
import pandas as pd

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "data" / "venue_draw"
FORM_DIR = ROOT / "data" / "tr_form"
EDGES = [0.15, 0.30, 0.42, 0.55, 0.70]
MIN_VENUE_ROWS = 2000
THROUGH = "2026-10-08"


def _venue_key(s):
    from rc_field_rows import norm_venue
    return re.sub(r"\s*(synthetic|poly|polytrack|inner|outer)\b.*$", "", norm_venue(str(s))).strip()


def _slug(k):
    return re.sub(r"[^a-z0-9]+", "-", k).strip("-")


def _rail(x):
    x = str(x)
    if x.startswith("True"):
        return 0
    m = re.search(r"(\d+)\s*m", x)
    if not m:
        return -1
    k = int(m.group(1))
    return 1 if k <= 4 else 2 if k <= 9 else 3


def _going(x):
    m = re.match(r"(Firm|Good|Soft|Heavy)\s*(\d+)?", str(x))
    if not m:
        return -1
    k, n = m.group(1), int(m.group(2) or 0)
    if k == "Firm":
        return 0
    if k == "Good":
        return 1 if n <= 3 else 2
    if k == "Soft":
        return 3 if n <= 5 else 4 if n == 6 else 5
    return 6


def _rating_slopes(d):
    """Draw slope of the within-race ATW rating, rating points from the inside to the widest barrier, with a cluster-robust standard error, per distance group and overall."""
    import wfa_scale as W

    @functools.lru_cache(None)
    def off(foaled, age, sex, date, dist, wt):
        a = W.racing_age(foaled, date) if isinstance(foaled, str) and len(foaled) >= 10 else (None if pd.isna(age) else int(age))
        v = W.atw_offset(a, sex, date.date(), float(dist), wt)
        return np.nan if v is None else v

    d = d[(d.field_size >= 8) & d.wpr.notna() & d.weightCarried.notna() & d.distance.notna()].copy()
    d["c"] = [off(f, a, str(s).upper()[:1], dt, dist, w) for f, a, s, dt, dist, w in zip(d.horse_foaled, d.horse_age, d.horse_sex, d.date, d.distance, d.weightCarried)]
    d = d[d.c.notna()]
    d["atw"] = d.wpr + d.c
    d["ad"] = d.atw - d.groupby("race_id").atw.transform("mean")
    d["bf"] = (d.barrier - 1) / (d.field_size - 1)
    d["dg"] = np.where(d.distance <= 1300, 0, np.where(d.distance <= 1650, 1, 2))
    out = {}
    for v, x in d.groupby("v"):
        res = {}
        for k, z in [("all", x)] + [(str(i), x[x.dg == i]) for i in range(3)]:
            if len(z) < 800:
                continue
            xc = z.bf - z.bf.mean()
            sxx = (xc ** 2).sum()
            b = (xc * z.ad).sum() / sxx
            sc = (xc * (z.ad - b * xc)).groupby(z.race_id).sum()
            res[k] = [round(float(b), 2), round(float(np.sqrt((sc ** 2).sum()) / sxx), 2), int(len(z))]
        out[v] = res
    return out


def build():
    cols = ["race_id", "date", "track", "distance", "field_size", "barrier", "horse_id", "priceStarting", "positionFinish", "position800m", "rail_position", "going",
            "isBarrierTrial", "is_jumpout", "race_class", "wpr", "weightCarried", "horse_foaled", "horse_age", "horse_sex"]
    d = pd.concat([pd.read_csv(ROOT / f"race_results_{y}.csv.gz", usecols=lambda c: c in cols, low_memory=False) for y in range(2017, 2027)])
    d = d[(d.isBarrierTrial.astype(str) != "True") & (d.is_jumpout.astype(str) != "True") & ~d.race_class.astype(str).str.contains("Hurdle|Steeple", na=False)]
    d["date"] = pd.to_datetime(d.date)
    for c in ["distance", "field_size", "barrier", "priceStarting", "positionFinish", "position800m", "wpr", "weightCarried"]:
        d[c] = pd.to_numeric(d[c], errors="coerce")
    d = d.dropna(subset=["horse_id", "field_size", "barrier"]).sort_values(["horse_id", "date"])
    d["pf"] = ((d.position800m - 1) / (d.field_size - 1)).where(d.field_size >= 5)
    d["style_avg"] = d.groupby("horse_id").pf.transform(lambda s: s.shift(1).rolling(6, min_periods=2).mean())
    raw = {str(t).strip().lower(): _venue_key(t) for t in d.track.dropna().unique()}
    d["v"] = d.track.astype(str).str.strip().str.lower().map(raw)
    print("rating slopes ...", flush=True)
    rating = _rating_slopes(d)
    # priced single-winner races with a clean SP book
    d = d[(d.field_size >= 5) & (d.barrier > 0) & (d.priceStarting > 1)]
    d["won"] = (d.positionFinish == 1).astype(int)
    g = d.groupby("race_id")
    d = d[(g.won.transform("sum") == 1) & (g.priceStarting.transform(lambda s: (1 / s).sum()).between(1.05, 2.0)) & (g.priceStarting.transform("size") >= 0.9 * g.field_size.transform("first"))]
    book = d.groupby("race_id").priceStarting.transform(lambda s: (1 / s).sum())
    d["p"] = (1 / d.priceStarting) / book
    d["fwd"] = (d.style_avg <= 0.30).astype(int)
    d["nf"] = d.race_id.map(d.groupby("race_id").fwd.sum())
    d = d[d.style_avg.notna()].copy()
    d["si"] = np.digitize(d.style_avg, EDGES)
    d["pc"] = np.digitize(d.nf, [2, 4])
    d["dg"] = np.where(d.distance <= 1300, 0, np.where(d.distance <= 1650, 1, 2))
    d["rg"] = d.rail_position.map(_rail)
    d["gi"] = d.going.map(_going)
    d["bc"] = d.barrier.clip(upper=16).astype(int)
    OUT.mkdir(parents=True, exist_ok=True)
    for f in OUT.glob("*.json.gz"):
        f.unlink()
    index = {}
    n_files = 0
    for v, x in d.groupby("v"):
        if len(x) < MIN_VENUE_ROWS or not v:
            continue
        slug = _slug(v)
        rows = [[int(a), int(b), int(c), int(e), int(f), int(h), int(w), round(float(p), 4)] for a, b, c, e, f, h, w, p in zip(x.bc, x.si, x.dg, x.rg, x.gi, x.pc, x.won, x.p)]
        obj = {"venue": v, "runners": len(rows), "races": int(x.race_id.nunique()), "from": str(x.date.min().date()), "through": str(x.date.max().date()), "rating": rating.get(v, {}), "rows": rows}
        with gzip.GzipFile(OUT / f"{slug}.json.gz", "wb", mtime=0) as fh:
            fh.write(json.dumps(obj, separators=(",", ":")).encode())
        index[v] = slug
        n_files += 1
    # aliases: every raw track name and every venue name runners.csv has used, mapped to a built venue
    aliases = {k: _slug(vk) for k, vk in raw.items() if vk in index}
    try:
        import runners_io
        rv = runners_io.read_runners()
        for name in rv.venue.dropna().astype(str).str.strip().unique():
            vk = _venue_key(name)
            if vk in index:
                aliases[name.lower()] = _slug(vk)
    except Exception as e:  # noqa: BLE001
        print("runners.csv aliases skipped:", e)
    (OUT / "index.json").write_text(json.dumps({"through": THROUGH, "venues": {v: s for v, s in index.items()}, "aliases": aliases}, separators=(",", ":")))
    tot = sum(f.stat().st_size for f in OUT.glob("*.json.gz"))
    print(f"{n_files} venues, {len(aliases)} aliases, {tot / 1e6:.1f} MB gz")


def apply(df, days=28):
    """Runner column draw_style: mean 800m position share over the horse's last 6 earlier runs (5+ starters, trials out), from data/tr_form. Rows dated in the last `days` days or later only."""
    today = pd.Timestamp.now(tz="UTC").tz_localize(None).normalize()
    keep = pd.to_datetime(df["date"], errors="coerce") >= today - pd.Timedelta(days=days)
    if "draw_style" not in df.columns:
        df["draw_style"] = np.nan
    if not keep.any():
        return df
    recs = []
    for f in sorted(FORM_DIR.glob("*.json.gz")):
        if f.stem < (today - pd.Timedelta(days=420)).strftime("%Y-%m"):
            continue
        try:
            with gzip.open(f, "rt") as fh:
                runs = json.load(fh).get("runs", {}).values()
        except Exception:  # noqa: BLE001
            continue
        for r in runs:
            pos, st = r.get("position800m"), r.get("starters")
            if not pos or pos < 1 or not st or st < 5 or r.get("isBarrierTrial") or r.get("isJumpout"):
                continue
            recs.append((r.get("horse_id"), r.get("date"), (pos - 1) / (st - 1)))
    if not recs:
        return df
    h = pd.DataFrame(recs, columns=["horse_id", "date", "pf"]).dropna()
    h["date"] = pd.to_datetime(h.date)
    by = {k: (z.date.values, z.pf.values) for k, z in h.sort_values("date").groupby("horse_id")}
    hid = pd.to_numeric(df["horse_id"], errors="coerce")
    dts = pd.to_datetime(df["date"], errors="coerce")
    out = df["draw_style"].copy()
    for i in np.flatnonzero(keep.values):
        e = by.get(hid.iloc[i])
        if e is None:
            continue
        m = e[0] < np.datetime64(dts.iloc[i])
        pf = e[1][m][-6:]
        out.iloc[i] = float(pf.mean()) if len(pf) >= 2 else np.nan
    df["draw_style"] = out
    print(f"  draw style: {int(df.loc[keep, 'draw_style'].notna().sum()):,} of {int(keep.sum()):,} recent/upcoming runners have a style")
    return df


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--build", action="store_true")
    a = ap.parse_args()
    if a.build:
        sys.path.insert(0, str(ROOT))
        build()
