"""One-off scratch analysis: real user question, 2026-09-19: "With the
speed map adj and actual winners, what is the avg & median adj? How many
unfav map adjs win? How many flagged speed map horses win?" - a direct
descriptive-stats check on the Speed Map component itself (unrelated to
Combo), using ACTUAL race winners as the population.

Read-only against toprate_data.json (speed_map isn't in
toprate_runners.csv - same reason every other speed_map analysis this
session reads the JSON instead of the CSV). Replicates
SpeedMapGrid.tsx's/speedmap_jockey_tracker.py's own logic exactly rather
than reinventing it:
  - demeaned speed_map = raw wpjcb.speed_map - (mean over this race's own
    non-scratched runners with a speed_map value) - see
    speedMapDemeanedByRunId in raceModel.ts.
  - tag: "unfavoured" if demeaned <= -0.5, "favoured" if >= +0.5, else
    "neutral" (SPEED_MAP_TINT_THRESHOLD).
  - "flagged" = carries the Speed Map's own "!" caution badge
    (computeCautionRunIds in SpeedMapGrid.tsx): drawFrac (barrier
    position, (barrier-1)/(fieldSize-1)) >= 1/2 (widened from 2/3 to 1/2,
    2026-09-19 - see CLAUDE.md) AND tactical column index >= MIDFIELD_IDX
    (4, out of the current 10-column layout, also 2026-09-19) - i.e. "a
    wide gate sitting Midfield-forward or better" - with at most ONE
    exemption per race (the single LEAST-wide qualifying runner) when the
    race's own tempo is "Fast" (estimatePace() in pace.ts: prefers the
    real post-race raceShapeEarly ('rse') once resulted, matching
    >0.15/< -0.15/else Fast/Slow/Even, falling back to the pre-race
    rs_label prediction only if rse is somehow still null on a resulted
    race).
  - tactical column index: same 10-band predictedRelSettle ('psr')
    boundaries as SpeedMapGrid.tsx's COLUMNS array, falling back to the
    4-way predictedSettlingBand ('psBand') midpoint if psr is null, then
    0.5 if both are null.

Winner = won==1 (the authoritative field, not finish_position, matching
this session's "confirmed against a real payload that an unresulted
runner's won is always NaN/None, never 0" convention already documented
in CLAUDE.md).
"""
import json
import statistics
from datetime import date

DATA_JSON = "toprate_data.json"
TODAY = date.today().isoformat()
DEMEAN_THRESHOLD = 0.5
MIDFIELD_IDX = 4
CAUTION_DRAW_FRAC_MIN = 0.5

# 10-band predictedRelSettle boundaries, in COLUMNS order (index 0 =
# Backmarker-deep ... index 9 = Leader), matching SpeedMapGrid.tsx exactly.
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


def main():
    with open(DATA_JSON) as f:
        data = json.load(f)

    winner_demeaned = []
    winner_tags = []
    winner_flagged = []
    n_races = 0
    n_winners_no_speedmap = 0
    # Field-wide base rates, for context - is the winner rate above just
    # proportionate to how common these tags/flags are across the whole
    # field, or actually elevated/depressed relative to base rate?
    field_tag_counts = {"unfavoured": 0, "neutral": 0, "favoured": 0}
    field_n_with_speedmap = 0
    field_n_flagged = 0
    field_n_total = 0

    for r in data.get("RACES", []):
        d = r.get("date")
        if not d or d > TODAY:
            continue
        runners = [u for u in r.get("runners", []) if not u.get("scr")]
        if len(runners) < 2:
            continue
        winner = next((u for u in runners if u.get("won") == 1), None)
        if winner is None:
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
            field_n_total += 1
            if u.get("rid") in caution_rids:
                field_n_flagged += 1
            u_sm = (u.get("wpjcb") or {}).get("speed_map")
            if u_sm is not None:
                field_n_with_speedmap += 1
                u_demeaned = u_sm - sm_mean
                u_tag = "unfavoured" if u_demeaned <= -DEMEAN_THRESHOLD else (
                    "favoured" if u_demeaned >= DEMEAN_THRESHOLD else "neutral")
                field_tag_counts[u_tag] += 1

        raw_sm = (winner.get("wpjcb") or {}).get("speed_map")
        if raw_sm is None:
            n_winners_no_speedmap += 1
            continue
        demeaned = raw_sm - sm_mean
        tag = "unfavoured" if demeaned <= -DEMEAN_THRESHOLD else ("favoured" if demeaned >= DEMEAN_THRESHOLD else "neutral")
        flagged = winner.get("rid") in caution_rids

        winner_demeaned.append(demeaned)
        winner_tags.append(tag)
        winner_flagged.append(flagged)

    n = len(winner_demeaned)
    print(f"Resulted races with a known winner: {n_races}")
    print(f"Winners with a computable demeaned speed_map: {n} "
          f"({n_winners_no_speedmap} winners had no speed_map value at all)")

    print(f"\nAvg demeaned speed_map for winners: {statistics.mean(winner_demeaned):+.3f}")
    print(f"Median demeaned speed_map for winners: {statistics.median(winner_demeaned):+.3f}")

    n_unfav = sum(1 for t in winner_tags if t == "unfavoured")
    n_neutral = sum(1 for t in winner_tags if t == "neutral")
    n_fav = sum(1 for t in winner_tags if t == "favoured")
    print(f"\nWinners tagged unfavoured (demeaned <= -0.5): {n_unfav} ({100*n_unfav/n:.1f}%)")
    print(f"Winners tagged neutral:                        {n_neutral} ({100*n_neutral/n:.1f}%)")
    print(f"Winners tagged favoured (demeaned >= +0.5):    {n_fav} ({100*n_fav/n:.1f}%)")

    n_flagged = sum(1 for f in winner_flagged if f)
    print(f"\nWinners carrying the \"!\" wide-gate caution flag: {n_flagged} ({100*n_flagged/n:.1f}%)")

    print(f"\n=== For context: same tags/flag rates across the WHOLE field (all "
          f"non-scratched runners, not just winners) ===")
    print(f"Field runners with a computable speed_map: {field_n_with_speedmap}")
    for tag in ("unfavoured", "neutral", "favoured"):
        c = field_tag_counts[tag]
        print(f"  {tag:>10}: {c} ({100*c/field_n_with_speedmap:.1f}%)")
    print(f"Field runners carrying the \"!\" flag: {field_n_flagged}/{field_n_total} "
          f"({100*field_n_flagged/field_n_total:.1f}%)")


if __name__ == "__main__":
    main()
