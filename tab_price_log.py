"""
tab_price_log.py -- permanent, append-only log of every TAB fixed-odds read.

Drop this file into the TopRate repo next to tab_results_poller.py.
The poller already fetches fixed odds for every open race starting within
2 hours on each 1-2 minute cycle. This module writes each of those reads
to a dated CSV so the price history is never overwritten or culled.

WHERE IT WRITES
    $PRICE_LOG_DIR/YYYY-MM-DD.csv       (default ~/racing-data/tab_prices)
The default sits OUTSIDE the runner's repo checkout on purpose: the
workflow's checkout step runs `git clean -ffdx`, which deletes any
gitignored file inside the workspace. Files outside it survive.

Previous days' files are gzipped automatically to keep disk use small.
Best-effort: any error is printed and swallowed, never breaks the poll.
"""
import csv
import gzip
import os
import shutil
from datetime import date, datetime, timezone
from pathlib import Path

LOG_DIR = Path(os.environ.get("PRICE_LOG_DIR", Path.home() / "racing-data" / "tab_prices"))
FIELDS = ["captured_utc", "date", "venue", "race_no", "tab_number", "race_start_utc",
          "fixed_win_price", "fixed_place_price", "betting_status", "scratched"]


def append(prices):
    """prices: the list of dicts built in fetch_today_results()."""
    if not prices:
        return
    try:
        LOG_DIR.mkdir(parents=True, exist_ok=True)
        now = datetime.now(timezone.utc).isoformat(timespec="seconds")
        path = LOG_DIR / f"{date.today().isoformat()}.csv"
        new = not path.exists()
        with path.open("a", newline="") as f:
            w = csv.DictWriter(f, fieldnames=FIELDS, extrasaction="ignore")
            if new:
                w.writeheader()
            for p in prices:
                w.writerow({**p, "captured_utc": now})
        _compress_old()
    except Exception as e:
        print(f"  price log write failed (non-fatal): {type(e).__name__}: {e}")


def _compress_old():
    today = f"{date.today().isoformat()}.csv"
    for p in LOG_DIR.glob("*.csv"):
        if p.name == today:
            continue
        with p.open("rb") as src, gzip.open(str(p) + ".gz", "wb") as dst:
            shutil.copyfileobj(src, dst)
        p.unlink()
