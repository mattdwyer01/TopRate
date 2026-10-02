"""
tab_dividends.py -- log of TAB dividends (every pool: win, place, exotics, quaddie, early quaddie, ...) per race.

Why (Oct 2026): quaddie strategy tests in racing-model could only ESTIMATE dividends from SP (0.8 / product of the
winners' SP probabilities). Three real ones on 2 Oct paid 1.20-1.64x that estimate, which flips the conclusion, so
the real figure is needed for every meeting.

How: tab_results_poller.fetch_today_results() calls the race's detail endpoint ONCE when a race first shows as
Paying (one extra call per race per day; races already in the log are skipped) and passes the payload to parse().
Quaddie / early quaddie dividends sit on their last leg's race.

parse() is deliberately tolerant: it walks the whole payload for dicts carrying a product name ("wageringProduct",
"productType", "product", "betType") and reads their pool dividends ("poolDividends" / "dividends" / "payouts",
amount in "amount" / "dividend" / "payout" / "value"). Each row keeps a truncated raw JSON of its entry, so a
payload shape change is visible in the log instead of silently dropping data.

WHERE IT WRITES
    tab_dividends.csv in the repo root (committed by tab_results.yml; ~50 races a day, a few rows each).
Best-effort: any error is printed and swallowed, never breaks the poll.
"""
import csv
import json
from datetime import datetime, timezone
from pathlib import Path

LOG = Path(__file__).parent / "tab_dividends.csv"
FIELDS = ["captured_utc", "date", "venue", "race_no", "jurisdiction", "status", "product", "selections",
          "amount", "raw"]
PRODUCT_KEYS = ("wageringProduct", "productType", "product", "betType")
POOL_KEYS = ("poolDividends", "dividends", "payouts")
AMOUNT_KEYS = ("amount", "dividend", "payout", "value")
SELECTION_KEYS = ("selections", "runners", "legs", "runnerNumbers")


def key(d, venue, race_no):
    return f"{d}|{str(venue).strip().upper()}|{int(race_no)}"


def done_keys():
    """Races already logged (date|VENUE|race_no)."""
    if not LOG.exists():
        return set()
    try:
        with LOG.open(newline="") as f:
            return {key(r["date"], r["venue"], r["race_no"]) for r in csv.DictReader(f)
                    if r.get("date") and r.get("race_no")}
    except Exception as e:
        print(f"  dividend log read failed (non-fatal): {type(e).__name__}: {e}")
        return set()


def _first(d, keys):
    for k in keys:
        if k in d and d[k] not in (None, ""):
            return d[k]
    return None


def _sel(v):
    if v is None:
        return ""
    if isinstance(v, (list, tuple)):
        # legs / places joined by "/", dead heats inside a leg by "+" (e.g. 2/5+7/1/3)
        return "/".join("+".join(map(str, x)) if isinstance(x, (list, tuple)) else str(x) for x in v)
    return str(v)


def parse(payload):
    """[(product, selections, amount, raw)] for every pool dividend found anywhere in payload."""
    out = []

    def walk(o):
        if isinstance(o, dict):
            prod = _first(o, PRODUCT_KEYS)
            if isinstance(prod, str):
                pools = _first(o, POOL_KEYS)
                if isinstance(pools, list) and pools:
                    for p in pools:
                        if isinstance(p, dict):
                            out.append((prod, _sel(_first(p, SELECTION_KEYS)), _first(p, AMOUNT_KEYS),
                                        json.dumps(p, separators=(",", ":"))[:400]))
                    return
                amt = _first(o, AMOUNT_KEYS)
                if amt is not None and not isinstance(amt, (dict, list)):
                    out.append((prod, _sel(_first(o, SELECTION_KEYS)), amt,
                                json.dumps(o, separators=(",", ":"))[:400]))
                    return
            for v in o.values():
                walk(v)
        elif isinstance(o, list):
            for v in o:
                walk(v)

    walk(payload)
    return out


def append(rows):
    """rows: dicts with FIELDS (captured_utc filled here)."""
    if not rows:
        return
    try:
        new = not LOG.exists()
        now = datetime.now(timezone.utc).isoformat(timespec="seconds")
        with LOG.open("a", newline="") as f:
            w = csv.DictWriter(f, fieldnames=FIELDS, extrasaction="ignore")
            if new:
                w.writeheader()
            for r in rows:
                w.writerow({**r, "captured_utc": now})
        n_races = len({(r["date"], r["venue"], r["race_no"]) for r in rows})
        quads = [r for r in rows if "quad" in str(r.get("product", "")).lower()]
        print(f"  Logged {len(rows)} TAB dividend rows for {n_races} race(s)"
              + (f"; quaddie: " + ", ".join(f"{r['venue']} R{r['race_no']} {r['product']} ${r['amount']}"
                                             for r in quads) if quads else ""))
    except Exception as e:
        print(f"  dividend log write failed (non-fatal): {type(e).__name__}: {e}")
