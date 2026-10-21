"""Fixed win prices for Hong Kong races from Betr (21 Oct 2026). TAB has no fixed odds for Hong Kong (tote only), and TopRate's Hong Kong
"fixed" price is tote too, so this is the only fixed-price source for those races.

Read-only, plain urllib with an honest header, run from the AU runner as part of tab_results_poller's cycle. Betr's site API
(web20-api.bluebet.com.au, the calls its own pages make, no login) answers a plain request from the Vultr box; from cloud hosts it sits behind a
Cloudflare challenge, which is NOT worked around (any non-JSON answer just means no price this cycle).
Volume: one race-list call every 30 minutes (about 350 KB) plus one `Race?eventId=` call per Hong Kong race starting within 2 hours, per cycle.
Best-effort: every error is swallowed, so a Betr problem can never break the results poll.
Entries have the same shape as tab_results_poller's `prices` (date, venue, race_no, tab_number, fixed_win_price, ...), so apply_prices() and
tab_price_log take them unchanged. `betting_status` is "Betr" so the price log can tell the source apart.
"""
import json
import time
import urllib.error
import urllib.request
from datetime import datetime, timedelta, timezone

H = "https://web20-api.bluebet.com.au"
HDR = {"Accept": "application/json", "User-Agent": "Mozilla/5.0 (X11; Linux x86_64) TopRate-personal-dashboard",
       "Origin": "https://www.betr.com.au", "Referer": "https://www.betr.com.au/"}
COUNTRIES = ("HKG",)
LOOKAHEAD = timedelta(hours=2)
PAST = timedelta(minutes=30)
MAP_REFRESH_S = 1800
PAUSE_S = 0.5

_map = {"at": 0.0, "races": []}


def _get(path, timeout=20):
    """Parsed JSON, or None for any error, non-200 or non-JSON answer (including a Cloudflare challenge)."""
    try:
        with urllib.request.urlopen(urllib.request.Request(H + path, headers=HDR), timeout=timeout) as r:
            body = r.read()
        return json.loads(body) if body[:1] in (b"{", b"[") else None
    except (urllib.error.URLError, ValueError, OSError):
        return None


def _t(s):
    """UTC time from Betr's '2026-10-21T10:40:00.0000000Z' (the first 19 characters are all that is needed)."""
    try:
        return datetime.strptime(str(s)[:19], "%Y-%m-%dT%H:%M:%S").replace(tzinfo=timezone.utc)
    except ValueError:
        return None


def _hk_races(d):
    out = []

    def walk(o):
        if isinstance(o, dict):
            if o.get("CountryCode") in COUNTRIES and o.get("EventId") and o.get("RaceNumber") is not None:
                out.append(o)
            else:
                for v in o.values():
                    walk(v)
        elif isinstance(o, list):
            for v in o:
                walk(v)
    walk(d)
    return out


def _races():
    if time.time() - _map["at"] > MAP_REFRESH_S:
        d = _get("/GroupedRaceCard?DaysToRace=0")
        if d is not None:
            _map["races"], _map["at"] = _hk_races(d), time.time()
    return _map["races"]


def parse_race(race, detail):
    """Price entries for one race from Betr's `Race?eventId=` answer (Outcomes[].OutcomeId is the tab number)."""
    start = str(race.get("AdvertisedStartTime") or "")
    entries = []
    for o in detail.get("Outcomes") or []:
        tab = o.get("OutcomeId")
        if tab is None:
            continue
        fp = {p.get("MarketTypeCode"): p for p in (o.get("FixedPrices") or [])}
        win = (fp.get("WIN") or {}).get("Price")
        e = dict(date=start[:10], venue=race.get("Venue"), race_no=race.get("RaceNumber"), tab_number=tab, scratched=False,
                 race_start_utc=start, fixed_place_price=(fp.get("PLC") or {}).get("Price"), betting_status="Betr")
        if isinstance(win, (int, float)) and win > 1:
            e["fixed_win_price"] = float(win)
        entries.append(e)
    return entries


def fetch_hk_prices(now=None):
    """Price entries for every Hong Kong race starting within 2 hours (or jumped under 30 minutes ago and not yet resulted)."""
    now = now or datetime.now(timezone.utc)
    out = []
    for race in _races():
        st = _t(race.get("AdvertisedStartTime"))
        if st is None or not (-PAST <= st - now <= LOOKAHEAD):
            continue
        time.sleep(PAUSE_S)
        detail = _get(f"/Race?eventId={race['EventId']}")
        if isinstance(detail, dict):
            out.extend(parse_race(race, detail))
    return out


def _selftest():
    race = {"EventId": 1, "Venue": "Happy Valley", "RaceNumber": 1, "CountryCode": "HKG", "AdvertisedStartTime": "2026-10-21T10:40:00.0000000Z"}
    detail = {"Outcomes": [
        {"OutcomeId": 1, "FixedPrices": [{"MarketTypeCode": "PLC", "Price": 2.45}, {"MarketTypeCode": "WIN", "Price": 7.0, "OpenPrice": 7.5}]},
        {"OutcomeId": 2, "FixedPrices": [{"MarketTypeCode": "WIN", "Price": 3.8}, {"MarketTypeCode": "PLC", "Price": 1.65}]},
        {"OutcomeId": 3, "FixedPrices": []}]}
    e = parse_race(race, detail)
    assert [x.get("fixed_win_price") for x in e] == [7.0, 3.8, None], e
    assert e[0]["date"] == "2026-10-21" and e[0]["venue"] == "Happy Valley" and e[1]["fixed_place_price"] == 1.65
    assert len(_hk_races({"Thoroughbred": [[race, {"CountryCode": "TUR", "EventId": 2, "RaceNumber": 1}]]})) == 1
    assert _t("2026-10-21T10:40:00.0000000Z") == datetime(2026, 10, 21, 10, 40, tzinfo=timezone.utc)
    print("ok")


if __name__ == "__main__":
    _selftest()
