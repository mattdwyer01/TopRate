"""
wpr_rating_gap_qualitative_screen_test.py - tests a genuinely different
bet-selection approach: NO market-price comparison at all (no edge, no
"model prob vs market prob"). Instead, a pure rating + qualitative rules
screen:

  1. RATING-GAP SHORTLIST: runner is within N WPR points of the top-rated
     runner in its own race (N in {1, 2, 3}) - not just the single top
     pick, genuine other contenders too.
  2. GOOD JOCKEY (two definitions tested separately, per user request):
     (A) jockey_merit ADJ_TERM contribution is positive (the model's own
         population-fit read on this jockey's recent win rate).
     (B) jockey_rating (TopRate's own raw jockey quality number, NOT an
         ADJ_TERM - confirmed monotonic with real win rate: 8.2% -> 10.1%
         -> 10.3% -> 13.4% across quartiles, 95% coverage) ranks in the
         top third of today's field.
  3. FAVOURABLE PACE/SETTLING/DRAW (Sep 2026 update: speed_map, not
     pace_shape - this session found mid-analysis that the live model had
     moved 186 commits ahead on main without this branch, unifying the
     old pace_shape + track_barrier into one trained speed_map ADJ_TERM,
     plus 3 new validated signals: inside_threats (exposure to faster,
     more inside rivals in TODAY's actual field - the closest thing in
     this codebase to "will this horse get caught wide/boxed in"),
     track_barrier_slope (a properly-fitted per-track linear barrier
     effect, replacing a shallow-tree model that could not represent
     150+ distinct per-track slopes), and heat_interaction (own early
     speed vs race-wide pace pressure, train-only z-scored). speed_map
     contribution is positive = favourable combination of all of the
     above, not just settle/pace like the old pace_shape alone.
  4. PRICE FLOOR (user request): exclude anything under $2 / $3 - short
     favourites need an unrealistically high strike rate to break even,
     tested as a separate cut on top of the above.

DELIBERATELY NOT INCLUDED: a "fitness peaking" filter - no clean signal
for this exists in the codebase. pfm_score is a third-party "Form Factor"
rating (see backfill_pfm_score.py), not a fitness-peak indicator;
weight_trend is about weight CARRIED (handicap), not conditioning. Rather
than force an unreliable proxy, left out per user instruction ("might be
one to leave out").

WHY NO MARKET-PRICE FILTER: this is the whole point of the test - real
market price is still used to compute actual ROI (you always need a
price to know what betting actually returned), but it does NOT gate
WHICH runners get selected. Selection is 100% rating-gap + qualitative
rules; price only enters afterward, as the return you'd have gotten, and
as an optional floor (a sanity screen against silly short prices, not an
edge requirement).

METHODOLOGY: fresh wprp_proj/wprp_contrib via calibrate_price_beta.py's
_load_resulted() (real compute_wpr_projection() entry point, avoids the
stale-stored-column bug this session already worked around), real market
price (fixed_win_price falling back to starting_price_sp) for ROI only.
120-day window for a real sample size across every combination.

NO EM DASHES policy: hyphens only.
"""
import json
import numpy as np
import pandas as pd

from calibrate_price_beta import _load_resulted
from wpr_bet_selection_post_retrain import report

DAYS_BACK = 120
# Extended (user follow-up, Sep 2026): N<=1 came out clearly best of {1,2,3}
# in the first pass (tighter beats looser at every price floor) - this
# widens the grid to see whether the degradation continues smoothly past
# 3, or whether there's a local sweet spot the coarser {1,2,3} grid missed.
N_GRID = [1, 2, 3, 4, 5, 6, 8, 10]
PRICE_FLOORS = [1.0, 2.0, 3.0]  # 1.0 = no real floor (matches the >1.0 convention used all night)


def parse_contrib(x, key):
    try:
        return json.loads(x).get(key)
    except Exception:
        return None


def run():
    print(f"Loading resulted races (fresh wprp_proj/wprp_contrib via "
          f"compute_wpr_projection, {DAYS_BACK} days back)...")
    d = _load_resulted(days_back=DAYS_BACK)
    d = d.dropna(subset=["wprp_proj", "wprp_contrib", "won", "race_id", "date"])
    print(f"Loaded: {len(d):,} resulted rows, {d['race_id'].nunique():,} races, "
          f"{d['date'].min()} .. {d['date'].max()}")

    d["jockey_merit"] = pd.to_numeric(d["wprp_contrib"].apply(lambda x: parse_contrib(x, "jockey_merit")),
                                       errors="coerce")
    d["speed_map"] = pd.to_numeric(d["wprp_contrib"].apply(lambda x: parse_contrib(x, "speed_map")),
                                    errors="coerce")
    d["jockey_rating"] = pd.to_numeric(d["jockey_rating"], errors="coerce")

    sp = pd.to_numeric(d["fixed_win_price"], errors="coerce")
    sp_fb = pd.to_numeric(d["starting_price_sp"], errors="coerce")
    d["sp"] = sp.fillna(sp_fb)
    d = d.dropna(subset=["sp"])
    d = d[d["sp"] > 1.0]

    d["field_size"] = d.groupby("race_id")["race_id"].transform("size")
    d = d[d["field_size"] >= 4]
    d["top_wpr"] = d.groupby("race_id")["wprp_proj"].transform("max")
    d["gap_from_top"] = d["top_wpr"] - d["wprp_proj"]
    # jockey_rating rank within race, 1 = best (highest rating)
    d["jockey_rank_in_race"] = d.groupby("race_id")["jockey_rating"].rank(ascending=False, method="min")
    d["jockey_top_third"] = d["jockey_rank_in_race"] <= np.ceil(d["field_size"] / 3)

    print(f"\nScoped rows after price/field filters: {len(d):,} ({d['race_id'].nunique():,} races)")
    print(f"jockey_merit coverage: {d['jockey_merit'].notna().mean()*100:.1f}%   "
          f"speed_map coverage: {d['speed_map'].notna().mean()*100:.1f}%   "
          f"jockey_rating coverage: {d['jockey_rating'].notna().mean()*100:.1f}%")

    for floor in PRICE_FLOORS:
        floor_label = "no floor" if floor <= 1.0 else f"price>=${floor:.0f}"
        print("\n" + "=" * 78)
        print(f"PRICE FLOOR: {floor_label}")
        print("=" * 78)
        base = d[d["sp"] >= floor]

        print("\n--- reference: top pick only (gap=0) ---")
        report(base[base["gap_from_top"] <= 0.001], "top pick")

        for n in N_GRID:
            shortlist = base[base["gap_from_top"] <= n]
            print(f"\n--- rating-gap shortlist only, N<={n} (no jockey/pace filter) ---")
            report(shortlist, f"gap<={n}")

            for jname, jmask in [
                ("jockey_merit>0", shortlist["jockey_merit"] > 0),
                ("jockey top-third rating", shortlist["jockey_top_third"]),
            ]:
                full_screen = shortlist[jmask & (shortlist["speed_map"] > 0)]
                report(full_screen, f"gap<={n} + {jname} + speed_map>0")


if __name__ == "__main__":
    run()
