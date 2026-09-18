"""One-off scratch analysis: direct follow-up to
wpr_speedmap_winner_stats_test.py's finding that the "!" wide-gate caution
flag showed almost no relationship with actually winning (flagged winners
30.0% vs a 27.6% field base rate) - real user question, 2026-09-19: "does
the flag correlate with anything else worth checking".

Checks the flag against the things that would actually matter for
betting/interpretation, reusing exactly the same replicated logic
(SpeedMapGrid.tsx's demeaning/tagging, computeCautionRunIds()'s caution
flag incl. its single-Fast-tempo-exemption rule, estimatePace()'s tempo
priority chain) as that script, over the same population (every
non-scratched runner in a resulted race with a known winner, current
~25-day toprate_data.json window):

  1. Price/ROI - is the market already pricing the flag's risk in (flagged
     runners priced longer, in line with a lower "should" win rate), or is
     there a real mispricing either direction? Backs EVERY flagged/
     unflagged runner to win, flat and proportional ROI (same stake_for()
     convention as every other ROI script this session).
  2. Cross-tab with the demeaned speed_map TAG (unfavoured/neutral/
     favoured) - is "flagged" just a proxy for "unfavoured" (both driven
     off barrier), or a materially different population?
  3. Tempo bucket (Fast/Even/Slow) - the caution flag's own logic already
     treats Fast specially (single-exemption rule), so does the flag's win
     rate/ROI actually differ by tempo, matching the flag's own design
     intent ("needs to cross rivals/hot pace to be plausible")?
  4. Field size bucket - the flag is partly a function of draw fraction,
     which is mechanically more common to trigger in bigger fields (more
     ways to draw wide) - check if flag rate and win rate/ROI vary with
     field size.

Read-only against toprate_data.json - writes nothing.
"""
import json
from datetime import date

DATA_JSON = "toprate_data.json"
TODAY = date.today().isoformat()
DEMEAN_THRESHOLD = 0.5
MIDFIELD_IDX = 4
CAUTION_DRAW_FRAC_MIN = 0.5

BANDS = [
    (9 / 10, 1), (8 / 10, 9 / 10), (7 / 10, 8 / 10), (6 / 10, 7 / 10),
    (5 / 10, 6 / 10), (4 / 10, 5 / 10), (3 / 10, 4 / 10), (2 / 10, 3 / 10),
    (1 / 10, 2 / 10), (0, 1 / 10),
]
BAND_MIDPOINT = {"Leader": 0.1, "On-pace": 0.325, "Midfield": 0.575, "Back": 0.85}


def col_index_of(rel: float) -> int:
    for i, (lo, hi) in enumerate(BANDS):
        if lo <= rel <= hi:
            return i
    return len(BANDS) - 1


def rel_settle_of(u: dict) -> float:
    if u.get("psr") is not None:
        return u["psr"]
    band = u.get("psBand")
    if band and band in BAND_MIDPOINT:
        return BAND_MIDPOINT[band]
    return 0.5


def draw_frac_of(u: dict, field_size: int) -> float:
    b = u.get("b")
    if b is None or field_size < 2:
        return 0.5
    return max(0.0, min(1.0, (b - 1) / (field_size - 1)))


def tempo_bucket_of(r: dict, runners: list) -> str:
    rse = r.get("rse")
    if rse is not None:
        if rse > 0.15:
            return "Fast"
        if rse < -0.15:
            return "Slow"
        return "Even"
    rs_label = r.get("rs_label")
    if rs_label:
        return "Slow" if rs_label == "Slow" else ("Even" if rs_label == "Even" else "Fast")
    leaders = sum(1 for u in runners if u.get("asp") is not None and u["asp"] <= 2)
    on_pace = sum(1 for u in runners if u.get("asp") is not None and 2 < u["asp"] <= 4)
    mid_or_back = sum(1 for u in runners if u.get("asp") is not None and u["asp"] > 4)
    if leaders >= 3:
        return "Fast"
    if leaders >= 2 and on_pace >= 2:
        return "Fast"
    if leaders <= 1 and mid_or_back >= 4:
        return "Slow"
    return "Even"


def compute_caution_run_ids(runners: list, field_size: int, col_idx_by_rid: dict, tempo: str) -> set:
    candidates = []
    for u in runners:
        rid = u.get("rid")
        draw_frac = draw_frac_of(u, field_size)
        col_idx = col_idx_by_rid.get(rid, MIDFIELD_IDX)
        if draw_frac >= CAUTION_DRAW_FRAC_MIN and col_idx >= MIDFIELD_IDX:
            candidates.append((draw_frac, rid))
    candidates.sort(key=lambda x: x[0])
    exempt_count = 1 if tempo == "Fast" else 0
    return set(rid for _, rid in candidates[exempt_count:])


def stake_for(price, return_units=4.0):
    return return_units / price


def roi_stats(rows):
    n = len(rows)
    if n == 0:
        return float("nan"), float("nan"), float("nan"), float("nan"), float("nan")
    wins = sum(1 for r in rows if r["won"])
    win_pct = 100 * wins / n
    avg_price = sum(r["price"] for r in rows) / n
    flat_returned = sum(r["price"] for r in rows if r["won"])
    flat_roi = 100 * (flat_returned - n) / n
    prop_staked = sum(stake_for(r["price"]) for r in rows)
    prop_returned = 4.0 * wins
    prop_roi = 100 * (prop_returned - prop_staked) / prop_staked if prop_staked else float("nan")
    return win_pct, avg_price, flat_roi, prop_roi, n


def main():
    with open(DATA_JSON) as f:
        data = json.load(f)

    rows = []
    n_races = 0
    for r in data.get("RACES", []):
        d = r.get("date")
        if not d or d > TODAY:
            continue
        runners = [u for u in r.get("runners", []) if not u.get("scr")]
        if len(runners) < 2:
            continue
        if not any(u.get("won") == 1 for u in runners):
            continue
        n_races += 1

        sm_vals = [(u.get("wpjcb") or {}).get("speed_map") for u in runners]
        sm_vals = [v for v in sm_vals if v is not None]
        sm_mean = sum(sm_vals) / len(sm_vals) if sm_vals else 0.0

        field_size = len(runners)
        col_idx_by_rid = {u.get("rid"): col_index_of(rel_settle_of(u)) for u in runners}
        tempo = tempo_bucket_of(r, runners)
        caution_rids = compute_caution_run_ids(runners, field_size, col_idx_by_rid, tempo)

        for u in runners:
            won = u.get("won")
            f_pos = u.get("f")
            if won is None and f_pos is None:
                continue  # not resulted
            price = u.get("sp") if u.get("sp") is not None else u.get("fx")
            if price is None or price <= 1.0:
                continue

            sm = (u.get("wpjcb") or {}).get("speed_map")
            demeaned = (sm - sm_mean) if sm is not None else None
            if demeaned is None:
                tag = "unknown"
            elif demeaned <= -DEMEAN_THRESHOLD:
                tag = "unfavoured"
            elif demeaned >= DEMEAN_THRESHOLD:
                tag = "favoured"
            else:
                tag = "neutral"

            if field_size <= 8:
                size_bucket = "small (<=8)"
            elif field_size <= 12:
                size_bucket = "medium (9-12)"
            else:
                size_bucket = "large (13+)"

            rows.append({
                "won": (won == 1),
                "price": price,
                "flagged": u.get("rid") in caution_rids,
                "tag": tag,
                "tempo": tempo,
                "size_bucket": size_bucket,
            })

    print(f"Resulted races with a known winner: {n_races}, runner-rows with known result+price: {len(rows)}")

    print("\n=== ROI backing every runner to win, flagged vs unflagged ===")
    print(f"{'group':>12}  {'n':>6}  {'win %':>6}  {'avg price':>9}  {'flat ROI':>9}  {'prop ROI':>9}")
    for label, sub in [("flagged", [r for r in rows if r["flagged"]]),
                        ("unflagged", [r for r in rows if not r["flagged"]])]:
        win_pct, avg_price, flat_roi, prop_roi, n = roi_stats(sub)
        print(f"{label:>12}  {n:>6}  {win_pct:>5.1f}%  ${avg_price:>8.2f}  {flat_roi:>+8.1f}%  {prop_roi:>+8.1f}%")

    print("\n=== Cross-tab: flagged vs speed_map tag ===")
    print(f"{'tag':>12}  {'n total':>8}  {'n flagged':>10}  {'% of tag flagged':>17}")
    for tag in ("unfavoured", "neutral", "favoured"):
        tag_rows = [r for r in rows if r["tag"] == tag]
        n_flagged = sum(1 for r in tag_rows if r["flagged"])
        pct = 100 * n_flagged / len(tag_rows) if tag_rows else float("nan")
        print(f"{tag:>12}  {len(tag_rows):>8}  {n_flagged:>10}  {pct:>16.1f}%")

    print("\n=== Flagged runners only: win%/ROI broken out by tempo bucket ===")
    print(f"{'tempo':>6}  {'n':>6}  {'win %':>6}  {'avg price':>9}  {'flat ROI':>9}  {'prop ROI':>9}  {'flag rate':>9}")
    for tempo in ("Fast", "Even", "Slow"):
        tempo_rows = [r for r in rows if r["tempo"] == tempo]
        flagged_sub = [r for r in tempo_rows if r["flagged"]]
        win_pct, avg_price, flat_roi, prop_roi, n = roi_stats(flagged_sub)
        flag_rate = 100 * len(flagged_sub) / len(tempo_rows) if tempo_rows else float("nan")
        print(f"{tempo:>6}  {n:>6}  {win_pct:>5.1f}%  ${avg_price:>8.2f}  {flat_roi:>+8.1f}%  {prop_roi:>+8.1f}%  {flag_rate:>8.1f}%")

    print("\n=== Flagged runners only: win%/ROI broken out by field size ===")
    print(f"{'size':>14}  {'n':>6}  {'win %':>6}  {'avg price':>9}  {'flat ROI':>9}  {'prop ROI':>9}  {'flag rate':>9}")
    for bucket in ("small (<=8)", "medium (9-12)", "large (13+)"):
        size_rows = [r for r in rows if r["size_bucket"] == bucket]
        flagged_sub = [r for r in size_rows if r["flagged"]]
        win_pct, avg_price, flat_roi, prop_roi, n = roi_stats(flagged_sub)
        flag_rate = 100 * len(flagged_sub) / len(size_rows) if size_rows else float("nan")
        print(f"{bucket:>14}  {n:>6}  {win_pct:>5.1f}%  ${avg_price:>8.2f}  {flat_roi:>+8.1f}%  {prop_roi:>+8.1f}%  {flag_rate:>8.1f}%")

    # Robustness check on the headline flagged-vs-unflagged ROI numbers,
    # same two checks every apparently-notable result in this file's
    # history gets before being called a finding.
    print("\n=== Robustness check: flagged group, date-half split + exclude 3 biggest winners ===")
    flagged = [r for r in rows if r["flagged"]]
    winners = sorted([r for r in flagged if r["won"]], key=lambda r: -r["price"])
    excl = [r for r in flagged if r not in winners[:3]]
    _, _, e_flat, e_prop, _ = roi_stats(excl)
    _, _, o_flat, o_prop, _ = roi_stats(flagged)
    print(f"flagged (n={len(flagged)}): overall flat={o_flat:+.1f}%/prop={o_prop:+.1f}%  "
          f"excl-top3-winners flat={e_flat:+.1f}%/prop={e_prop:+.1f}%")


if __name__ == "__main__":
    main()
