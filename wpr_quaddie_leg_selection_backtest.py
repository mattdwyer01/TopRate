"""
wpr_quaddie_leg_selection_backtest.py - tests quaddie leg-selection and
staking strategies. Per explicit user instruction, no real quaddie leg
grouping or dividend data exists anywhere in this codebase (confirmed: the
old toprate_html_v3.py "Quaddie tab" cumulative score was removed in a
prior "Stage 2" rework and never rebuilt in the new frontend; no exotic
pool/dividend field exists in toprate_runners.csv; a live TAB API probe for
real leg/dividend data was blocked by this environment's outbound proxy
policy, not TAB's own geo-block). Two proxies are used instead, both
explicit simplifications, not real pari-mutuel mechanics:

  LEGS: the last 4 resulted races of a (venue, date) meeting, sorted by
  race number. Real quaddies are nominated legs (usually the last 4 races
  on a metro Saturday card), so "last 4" is the closest reconstructable
  approximation from what's in toprate_runners.csv (venue/race/date only,
  no leg-nomination flag).

  DIVIDEND: product of the 4 legs' actual winning price (fixed_win_price,
  falling back to starting_price_sp), per explicit user directive ("Just
  assume each leg is multipled for the quaddie dividend for the time
  being"). Real quaddie dividends are pari-mutuel pool payouts, not a
  simple product of win prices - this is a known, acknowledged
  simplification for testing selection-strategy efficiency, not a claim
  about real payouts.

STAKING MODEL: flat $1 per combination (the simplest quaddie staking
convention - "full" coverage of every combination in your selections, no
flexi%). cost = combos = picks_leg1 * picks_leg2 * picks_leg3 * picks_leg4.
A hit (your selections cover the actual winner in all 4 legs) returns the
proxy dividend (in $1-per-combo units); a miss returns 0. This is
mathematically identical to a flexi bet at 100% of a budget equal to the
combo count, so flat-per-combo ROI is the right first cut before layering a
smaller flexi budget on top.

SELECTION STRATEGIES tested per leg, reusing the rating-gap shortlist
concept from wpr_rating_gap_qualitative_screen_test.py:
  - UNIFORM: same gap-from-top threshold N for all 4 legs, grid N in
    {0(top pick only),1,2,3,4,6,8}.
  - BANKER: N_TIGHT (usually 0 or 1) applied to the leg with the largest
    gap between its #1 and #2 ranked runner (the "most confident" leg -
    a big gap-to-second means the model is unusually sure), N_LOOSE
    applied to the other 3 legs. Tests whether concentrating combos on
    the genuinely uncertain legs (and banking the confident one down to
    fewer picks) beats spending combos evenly.

METHODOLOGY: fresh wprp_proj via calibrate_price_beta.py's _load_resulted()
(same pattern as every other selection-strategy script this session, avoids
stale stored wprp_proj). 120-day window. No leakage risk here since nothing
is trained - this only applies already-computed projections and actual
results after the fact.

NO EM DASHES policy: hyphens only.
"""
import numpy as np
import pandas as pd

from calibrate_price_beta import _load_resulted

DAYS_BACK = 120
UNIFORM_N_GRID = [0, 1, 2, 3, 4, 6, 8]
BANKER_TIGHT_GRID = [0, 1]
BANKER_LOOSE_GRID = [2, 3, 4, 6]


def build_legs(d):
    """Returns a list of dicts, one per meeting, each holding up to 4
    "leg" DataFrames (the last 4 resulted races of that venue/date,
    sorted by race number)."""
    d = d.copy()
    d["date_only"] = d["date"].astype(str).str[:10]
    d["top_wpr"] = d.groupby("race_id")["wprp_proj"].transform("max")
    d["gap_from_top"] = d["top_wpr"] - d["wprp_proj"]
    d["field_size"] = d.groupby("race_id")["race_id"].transform("size")

    # second-highest wprp_proj per race, for the banker "gap to 2nd" signal
    def second_max(g):
        s = g.sort_values(ascending=False)
        return s.iloc[1] if len(s) > 1 else s.iloc[0]

    second = d.groupby("race_id")["wprp_proj"].apply(second_max)
    d["second_wpr"] = d["race_id"].map(second)
    d["top_to_2nd_gap"] = d["top_wpr"] - d["second_wpr"]

    meetings = []
    for (venue, date_only), g in d.groupby(["venue", "date_only"]):
        races = sorted(g["race"].unique())
        if len(races) < 4:
            continue
        last4 = races[-4:]
        legs = []
        ok = True
        for rno in last4:
            leg = g[g["race"] == rno]
            if leg["field_size"].iloc[0] < 4:
                ok = False
                break
            if leg["won"].sum() != 1:
                ok = False
                break
            legs.append(leg)
        if ok and len(legs) == 4:
            meetings.append({"venue": venue, "date": date_only, "legs": legs})
    return meetings


def leg_picks(leg, n):
    """Runners selected in this leg at gap-from-top threshold n."""
    return leg[leg["gap_from_top"] <= n + 1e-9]


def leg_winner_price(leg):
    row = leg[leg["won"] == 1].iloc[0]
    return float(row["sp"])


def leg_winner_covered(leg, picks):
    return (picks["won"] == 1).any()


def evaluate(meetings, leg_ns):
    """leg_ns: either a single int (uniform N for all 4 legs) or a
    function(leg_index, leg_df) -> N. Returns dict of aggregate stats."""
    total_cost = 0.0
    total_return = 0.0
    n_quaddies = 0
    n_hits = 0
    combo_counts = []
    for m in meetings:
        legs = m["legs"]
        picks_per_leg = []
        for i, leg in enumerate(legs):
            n = leg_ns(i, leg) if callable(leg_ns) else leg_ns
            picks_per_leg.append(leg_picks(leg, n))
        combos = 1
        for p in picks_per_leg:
            combos *= max(len(p), 1)
        cost = combos * 1.0
        hit = all(leg_winner_covered(legs[i], picks_per_leg[i]) for i in range(4))
        payout = 0.0
        if hit:
            div = 1.0
            for leg in legs:
                div *= leg_winner_price(leg)
            payout = div
        total_cost += cost
        total_return += payout
        n_quaddies += 1
        n_hits += int(hit)
        combo_counts.append(combos)
    if total_cost == 0:
        return None
    roi = (total_return - total_cost) / total_cost * 100
    return {
        "n_quaddies": n_quaddies,
        "n_hits": n_hits,
        "strike_pct": n_hits / n_quaddies * 100 if n_quaddies else float("nan"),
        "avg_combos": float(np.mean(combo_counts)),
        "median_combos": float(np.median(combo_counts)),
        "total_cost": total_cost,
        "total_return": total_return,
        "roi_pct": roi,
    }


def print_row(label, stats):
    if stats is None:
        print(f"  {label:45s}  (no data)")
        return
    print(f"  {label:45s}  n={stats['n_quaddies']:4d}  hits={stats['n_hits']:3d} "
          f"({stats['strike_pct']:5.1f}%)  avg_combos={stats['avg_combos']:7.1f}  "
          f"cost=${stats['total_cost']:9,.0f}  return=${stats['total_return']:9,.0f}  "
          f"ROI={stats['roi_pct']:+7.2f}%")


def run():
    print(f"Loading resulted races (fresh wprp_proj via compute_wpr_projection, "
          f"{DAYS_BACK} days back)...")
    d = _load_resulted(days_back=DAYS_BACK)
    d = d.dropna(subset=["wprp_proj", "won", "race_id", "date", "venue", "race"])

    sp = pd.to_numeric(d["fixed_win_price"], errors="coerce")
    sp_fb = pd.to_numeric(d["starting_price_sp"], errors="coerce")
    d["sp"] = sp.fillna(sp_fb)
    d = d.dropna(subset=["sp"])
    d = d[d["sp"] > 1.0]

    print(f"Loaded: {len(d):,} resulted rows, {d['race_id'].nunique():,} races")

    meetings = build_legs(d)
    print(f"Meetings with a valid 4-leg 'last 4 races' quaddie: {len(meetings)}")
    if not meetings:
        print("No valid meetings found, aborting.")
        return

    print("\n" + "=" * 100)
    print("UNIFORM N (same rating-gap threshold applied to all 4 legs)")
    print("=" * 100)
    for n in UNIFORM_N_GRID:
        stats = evaluate(meetings, n)
        print_row(f"N<={n}" + (" (top pick only)" if n == 0 else ""), stats)

    print("\n" + "=" * 100)
    print("BANKER (tight N on the leg with the biggest top-to-2nd gap, loose N on the other 3)")
    print("=" * 100)
    for tight in BANKER_TIGHT_GRID:
        for loose in BANKER_LOOSE_GRID:
            if tight >= loose:
                continue

            def leg_ns(i, leg, _tight=tight, _loose=loose, _legs_ref=None):
                return _tight if leg["_is_banker_leg"].iloc[0] else _loose

            # precompute which leg index is the banker leg per meeting
            for m in meetings:
                gaps = [leg["top_to_2nd_gap"].iloc[0] for leg in m["legs"]]
                banker_idx = int(np.argmax(gaps))
                for i, leg in enumerate(m["legs"]):
                    leg["_is_banker_leg"] = (i == banker_idx)

            stats = evaluate(meetings, leg_ns)
            print_row(f"banker tight={tight} loose={loose}", stats)

    print("\n" + "=" * 100)
    print("REFERENCE: single top-pick-per-leg parlay (N=0 all legs) vs market SP multi")
    print("=" * 100)
    stats = evaluate(meetings, 0)
    print_row("top pick all 4 legs", stats)


if __name__ == "__main__":
    run()
