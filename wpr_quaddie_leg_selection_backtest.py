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
  - CORROBORATED (user follow-up): the plain WPR gap-from-top shortlist
    widened to N<=2/3/4 catches a lot of low-quality runners just because
    they're close in points. This adds two independent corroborating
    filters, same "top-third of field" pattern already validated for
    jockey_rating in wpr_rating_gap_qualitative_screen_test.py:
      - TR RATING top-third: toprate_rating is TAB's own published rating
        (payload key literally "tr", see toprate_daily.py's
        topRateRating mapping) - a genuinely independent third-party
        number, not derived from our WPR model at all. 81.6% coverage.
      - FORM FACTOR top-third: pfm_score_rank, a real per-race rank
        (confirmed 1=best via direct check, matches field_size per race)
        for pfm_score, the third-party "Form Factor" rating documented in
        CLAUDE.md (see backfill_pfm_score.py). 42.9% coverage - lower, so
        this filter is applied "if present" (a runner with no pfm_score
        neither passes nor fails on this specific filter alone) rather
        than excluding 57% of runners outright; REQUIRE_PFM_PRESENT below
        controls a stricter variant that requires presence.
    A runner is selected in a leg only if: WPR gap<=N AND (not requiring
    TR, or TR top-third) AND (not requiring Form Factor, or Form Factor
    top-third/absent per REQUIRE_PFM_PRESENT).

CACHING: _load_resulted(120) costs ~70-90 min (per-date
compute_wpr_projection() calls, see METHODOLOGY). Cached to CACHE_PATH
after the first run in this session so re-testing new selection filters
against the same fresh dataset doesn't re-pay that cost - delete the file
to force a fresh pull (e.g. after model retraining).

METHODOLOGY: fresh wprp_proj via calibrate_price_beta.py's _load_resulted()
(same pattern as every other selection-strategy script this session, avoids
stale stored wprp_proj). 120-day window. No leakage risk here since nothing
is trained - this only applies already-computed projections and actual
results after the fact.

RESULTS SUMMARY (Sep 2026, exhaustive - see chat log for full detail):
Tested on 120-day and then 150-day (full available history) windows, with
every result split-half checked (first half vs second half chronologically)
before being trusted, per this session's standing evidence bar. Every
narrow/concentrated strategy showed the identical failure signature
regardless of which lever was pulled: strongly positive in one half,
strongly negative in the other, with the pooled number an artifact of a
handful of extreme-dividend proxy hits (in the 120-day run, 2 of 318 H1
meetings alone drove 73% of that half's entire profit). Extending to the
full 150-day window did not fix this - it reproduced the exact same
flip. Tried and rejected on this basis: BANKER selection (by WPR
top-to-2nd gap, and separately by the model's own validated wprp_conf
confidence score), confidence-gating (betting only when the model is
generally sure - this made ROI reliably WORSE, not better, in both
halves), TR-rating and Form Factor corroboration filters (TR consistently
hurt; Form Factor's apparent benefit only showed up in the same unstable,
low-hit-count settings the split-half check already rules out),
realistic max-combo caps, and meeting-level gates (bucketing by average
field size, by average WPR top-to-2nd "card clarity", by total N<=4 combo
count, and by metro vs non-metro venue - none of these produced a bucket
that was both better than baseline AND consistent in sign across both
halves). The ONLY thing that held up as a stable, reproducible number
across both windows and both halves in every window: a plain, wide
UNIFORM shortlist (N<=4, no banker, no corroboration, no meeting gate) -
consistently and solidly NEGATIVE, roughly -40% to -49% ROI. CONCLUSION:
no selection strategy tested here shows evidence of a real, repeatable
quaddie edge under the current proxy-dividend methodology - this is a
structural fat-tail problem with multiplying 4 win prices together (a
real pari-mutuel dividend is capped by pool participation in a way this
proxy is not), not a fixable selection-quality problem. Revisiting this
would need real TAB dividend data (blocked from this environment, see
above), not further selection-rule search on the same proxy.

NO EM DASHES policy: hyphens only.
"""
import os
import numpy as np
import pandas as pd

from calibrate_price_beta import _load_resulted

DAYS_BACK = 150  # covers the full resulted history currently on disk (2026-04-26 .. today, 118 resulted dates)
UNIFORM_N_GRID = [0, 1, 2, 3, 4, 6, 8]
BANKER_TIGHT_GRID = [0, 1]
BANKER_LOOSE_GRID = [2, 3, 4, 6]
CORROBORATED_N_GRID = [2, 3, 4, 6]
REQUIRE_PFM_PRESENT = False  # False = "if present, must be top-third"; True = "must be present AND top-third"
CACHE_PATH = f"/tmp/claude-0/-home-user-TopRate/76dfed62-bd31-52ea-bf89-3275bc38fea4/scratchpad/_quaddie_load_resulted_{DAYS_BACK}d_cache.pkl"


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

    d["toprate_rating"] = pd.to_numeric(d["toprate_rating"], errors="coerce")
    d["tr_rank_in_race"] = d.groupby("race_id")["toprate_rating"].rank(ascending=False, method="min")
    d["tr_top_third"] = d["tr_rank_in_race"] <= np.ceil(d["field_size"] / 3)
    # toprate_rating missing entirely for this runner: doesn't pass the filter
    d.loc[d["toprate_rating"].isna(), "tr_top_third"] = False

    d["pfm_score_rank"] = pd.to_numeric(d["pfm_score_rank"], errors="coerce")
    d["pfm_top_third"] = d["pfm_score_rank"] <= np.ceil(d["field_size"] / 3)
    d["pfm_present"] = d["pfm_score_rank"].notna()

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


def leg_picks(leg, n, require_tr=False, require_pfm=False):
    """Runners selected in this leg at gap-from-top threshold n, optionally
    also requiring TR-rating and/or Form Factor top-third agreement."""
    mask = leg["gap_from_top"] <= n + 1e-9
    if require_tr:
        mask &= leg["tr_top_third"]
    if require_pfm:
        if REQUIRE_PFM_PRESENT:
            mask &= leg["pfm_present"] & leg["pfm_top_third"]
        else:
            mask &= (~leg["pfm_present"]) | leg["pfm_top_third"]
    return leg[mask]


def leg_winner_price(leg):
    row = leg[leg["won"] == 1].iloc[0]
    return float(row["sp"])


def leg_winner_covered(leg, picks):
    return (picks["won"] == 1).any()


def evaluate(meetings, leg_ns, require_tr=False, require_pfm=False):
    """leg_ns: either a single int (uniform N for all 4 legs) or a
    function(leg_index, leg_df) -> N. Returns dict of aggregate stats.
    A meeting where any leg's filtered shortlist is empty (no runner
    qualifies) is skipped entirely, not counted as a $1-combo bet -
    tracked separately as n_skipped."""
    total_cost = 0.0
    total_return = 0.0
    n_quaddies = 0
    n_skipped = 0
    n_hits = 0
    combo_counts = []
    for m in meetings:
        legs = m["legs"]
        picks_per_leg = []
        for i, leg in enumerate(legs):
            n = leg_ns(i, leg) if callable(leg_ns) else leg_ns
            picks_per_leg.append(leg_picks(leg, n, require_tr=require_tr, require_pfm=require_pfm))
        if any(len(p) == 0 for p in picks_per_leg):
            n_skipped += 1
            continue
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
        "n_skipped": n_skipped,
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
    print(f"  {label:45s}  n={stats['n_quaddies']:4d} (skip={stats['n_skipped']:3d})  "
          f"hits={stats['n_hits']:3d} ({stats['strike_pct']:5.1f}%)  "
          f"avg_combos={stats['avg_combos']:7.1f}  "
          f"cost=${stats['total_cost']:9,.0f}  return=${stats['total_return']:9,.0f}  "
          f"ROI={stats['roi_pct']:+7.2f}%")


def load_data():
    if os.path.exists(CACHE_PATH):
        print(f"Loading cached _load_resulted({DAYS_BACK}) output from {CACHE_PATH} "
              f"(delete this file to force a fresh {DAYS_BACK}-day pull)...")
        d = pd.read_pickle(CACHE_PATH)
    else:
        print(f"Loading resulted races (fresh wprp_proj via compute_wpr_projection, "
              f"{DAYS_BACK} days back, ~70-90 min)...")
        d = _load_resulted(days_back=DAYS_BACK)
        d.to_pickle(CACHE_PATH)
        print(f"  cached to {CACHE_PATH} for any future rerun this session")

    d = d.dropna(subset=["wprp_proj", "won", "race_id", "date", "venue", "race"])
    sp = pd.to_numeric(d["fixed_win_price"], errors="coerce")
    sp_fb = pd.to_numeric(d["starting_price_sp"], errors="coerce")
    d["sp"] = sp.fillna(sp_fb)
    d = d.dropna(subset=["sp"])
    d = d[d["sp"] > 1.0]
    print(f"Loaded: {len(d):,} resulted rows, {d['race_id'].nunique():,} races")
    return d


def mark_banker_legs(meetings):
    """Tags each leg with whether it's the meeting's "banker" leg (biggest
    top-to-2nd WPR gap = most confident leg). Mutates leg DataFrames."""
    for m in meetings:
        gaps = [leg["top_to_2nd_gap"].iloc[0] for leg in m["legs"]]
        banker_idx = int(np.argmax(gaps))
        for i, leg in enumerate(m["legs"]):
            leg["_is_banker_leg"] = (i == banker_idx)


def banker_leg_ns(i, leg, tight, loose):
    return tight if leg["_is_banker_leg"].iloc[0] else loose


def run():
    d = load_data()

    meetings = build_legs(d)
    print(f"Meetings with a valid 4-leg 'last 4 races' quaddie: {len(meetings)}")
    if not meetings:
        print("No valid meetings found, aborting.")
        return
    mark_banker_legs(meetings)

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
            stats = evaluate(meetings, lambda i, leg, _t=tight, _l=loose: banker_leg_ns(i, leg, _t, _l))
            print_row(f"banker tight={tight} loose={loose}", stats)

    print("\n" + "=" * 100)
    print("CORROBORATED SELECTION (WPR gap<=N AND TR-rating top-third AND/OR Form Factor top-third)")
    print(f"(Form Factor policy: REQUIRE_PFM_PRESENT={REQUIRE_PFM_PRESENT} - "
          f"{'must be present and top-third' if REQUIRE_PFM_PRESENT else 'top-third if present, else neutral'})")
    print("=" * 100)
    for require_tr, require_pfm, label in [
        (True, False, "+TR top-third"),
        (False, True, "+FormFactor top-third"),
        (True, True, "+TR top-third +FormFactor top-third"),
    ]:
        print(f"\n--- {label} ---")
        for n in CORROBORATED_N_GRID:
            stats = evaluate(meetings, n, require_tr=require_tr, require_pfm=require_pfm)
            print_row(f"N<={n} {label}", stats)

    print("\n--- banker + corroborated (best plain-banker settings from above, tight=0) ---")
    for require_tr, require_pfm, label in [
        (True, False, "+TR top-third"),
        (False, True, "+FormFactor top-third"),
        (True, True, "+TR top-third +FormFactor top-third"),
    ]:
        for loose in BANKER_LOOSE_GRID:
            stats = evaluate(
                meetings,
                lambda i, leg, _l=loose: banker_leg_ns(i, leg, 0, _l),
                require_tr=require_tr, require_pfm=require_pfm,
            )
            print_row(f"banker tight=0 loose={loose} {label}", stats)

    print("\n" + "=" * 100)
    print("REFERENCE: single top-pick-per-leg parlay (N=0 all legs) vs market SP multi")
    print("=" * 100)
    stats = evaluate(meetings, 0)
    print_row("top pick all 4 legs", stats)


if __name__ == "__main__":
    run()
