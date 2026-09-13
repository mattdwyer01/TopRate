import type { Runner } from '../types/domain'

export interface EffectiveRunner {
  effectiveProjectedWpr: number | null
  effectivePrice: number | null
  effectiveRank: number | null
  hasOverride: boolean
  scratched: boolean
  // WPR points behind the field's top-rated (effective) runner - null for a
  // scratched runner or one with no effective wpr. 0 for the top pick itself.
  gapFromTop: number | null
  // true when the market's own price is longer than our fair (effectivePrice)
  // price - i.e. wpr_projection.py's compute_edge_scores() "has_edge" case,
  // model_prob > market_prob. Mirrors that backend definition exactly rather
  // than reading its output, same reasoning as effectivePrice itself: this
  // needs to reflect manual overrides and live market price, not whatever
  // was true whenever the backend last computed it.
  isOverlay: boolean
  // true when this runner was a MATERIAL underlay at today's open price
  // (market shorter than our fair price by a real margin) and has since
  // drifted into being an overlay right now. Flagged, not excluded (user
  // decision, Sep 2026) - anecdotal and small-sample evidence (22 cases,
  // not yet statistically significant) suggests this specific pattern is a
  // bad sign, not a buying opportunity: the market often knows something
  // (gear, vet, stable mood) the model doesn't. See chat for the backing
  // analysis (price_drift_analysis.py).
  driftedToOverlay: boolean
  // The mirror case: a MATERIAL overlay at open that's since been backed
  // into an underlay right now - never shows up as an overlay itself (by
  // definition it's now priced shorter than our fair value), so it needs
  // its own flag to be visible at all. Informational, not a warning - the
  // one real example checked in chat (Headley Grange, Sep 2026) won.
  firmedToUnderlay: boolean
}

// The wpr_price cap in wpr_projection.py's project_race() - a no-hope
// runner's raw softmax price can blow out to 5-6 figures; capped at 999
// since beyond that the exact number is meaningless.
const PRICE_CAP = 999

// Backend's own fallback when config.json doesn't carry a beta (see
// wpr_projection.py's get_price_beta) - practically never hit once
// PRICE_BETA is always populated, kept only for defensiveness.
const DEFAULT_BETA = 0.4

// An overlay far behind the top-rated runner isn't a useful highlight - it's
// asking to back a horse the model itself doesn't rate as a real chance just
// because the market's price on it happens to be even longer. User decision
// (Sep 2026) to cap the highlight at the same 5-WPR marker line shown in the
// table, rather than surfacing every overlay regardless of how unlikely.
// Raised from 4 to 5 (Sep 2026) after a backtest showed the extra gap-4-to-5
// bets are statistically indistinguishable from the existing gap<=4 bucket
// (n=903, ROI -7.6%, p=0.35, vs the baseline's own -8.9%, p=0.10) - moving
// the line to 5 costs nothing and gains a modest amount of coverage. Beyond
// 5, strike rate keeps falling (5-6: 5.2% dropping to 12+: 1.1%) and a
// 75-vs-80 top-rated relaxation tested clearly worse (-16.5% on the added
// bets, p=0.001), so that threshold (MIN_TOP_RATED_WPR below) stayed put.
const OVERLAY_MAX_GAP_FROM_TOP = 5

// Overlays are suppressed race-wide when the field's own top-rated runner
// is below this WPR - a weak top pick (a modest horse that's merely the
// best of a bad bunch) makes the whole race's overlay signal less trustworthy
// than one where the top rated runner is a genuinely strong horse. Backed by
// a real (if not statistically airtight - see chat, Sep 2026) asymmetry: on
// the 67-day backtest, overlays in races with a sub-80 top pick were a
// confirmed loser (t-test vs zero, p=0.018); overlays where the top pick
// cleared 80 were not confirmed either way. A user decision to filter on
// that asymmetry despite it not being a fully robust threshold (a sweep of
// nearby values found the significance doesn't hold at 75 or 85, only in
// the 80-82 band) - kept here as one constant so it's easy to revisit once
// there's more data to actually fit this threshold properly.
const MIN_TOP_RATED_WPR = 80

// "Material" thresholds for the open-vs-now price-drift flags below: the
// open price has to be at least 15% away from our fair price in the
// relevant direction, not just noise-level movement. Chosen to comfortably
// catch the two real examples checked in chat (Private Eye: open $3.80 vs
// fair $4.71, ratio 0.807; Headley Grange: open $4.80 vs fair $4.06, ratio
// 1.182) without needing to match the Python backtest's probability-edge
// threshold exactly - this is a separate, price-based heuristic for a live
// UI flag, not the same computation.
const MATERIAL_UNDERLAY_AT_OPEN_RATIO = 0.85
const MATERIAL_OVERLAY_AT_OPEN_RATIO = 1.15

// Replicates wpr_projection.py's project_race() price/rank softmax
// EXACTLY (same formula, same beta), but over EFFECTIVE ratings: the
// model's own projectedWpr, or a manually entered base for a runner the
// model couldn't project, each with any manual delta added on top. This is
// what lets a manual override on one runner correctly shift every OTHER
// runner's price too - it's a field-relative softmax, not a per-runner
// calculation.
export function computeEffectiveRace(
  runners: Runner[],
  deltas: Record<string, number>,
  bases: Record<string, number>,
  priceBeta: number | null,
  scratched: Set<string> = new Set(),
): Record<string, EffectiveRunner> {
  const beta = priceBeta ?? DEFAULT_BETA

  const withEffectiveWpr = runners.map((r) => {
    const modelBase = r.projectedWpr ?? (r.runId in bases ? bases[r.runId] : null)
    const delta = deltas[r.runId] ?? 0
    const hasOverride = deltas[r.runId] != null || (r.projectedWpr == null && r.runId in bases)
    const isScratched = scratched.has(r.runId)
    return {
      runId: r.runId,
      // A scratched runner has no wpr for softmax purposes - excluded from
      // the field entirely (not just zeroed out), so the rest of the field
      // renormalizes as if it were never entered.
      wpr: !isScratched && modelBase != null ? modelBase + delta : null,
      hasOverride,
      scratched: isScratched,
    }
  })

  const rated = withEffectiveWpr.filter((r) => r.wpr != null) as { runId: string; wpr: number; hasOverride: boolean; scratched: boolean }[]

  const priceByRunId = new Map<string, number>()
  const rankByRunId = new Map<string, number>()
  const gapByRunId = new Map<string, number>()
  let topRatedWpr: number | null = null
  if (rated.length >= 2) {
    const maxWpr = Math.max(...rated.map((r) => r.wpr))
    topRatedWpr = maxWpr
    const exps = rated.map((r) => ({ runId: r.runId, e: Math.exp(beta * (r.wpr - maxWpr)) }))
    const sumE = exps.reduce((s, x) => s + x.e, 0)
    for (const x of exps) {
      priceByRunId.set(x.runId, Math.min(1 / (x.e / sumE), PRICE_CAP))
    }
    for (const r of rated) {
      gapByRunId.set(r.runId, maxWpr - r.wpr)
    }
    ;[...rated]
      .sort((a, b) => b.wpr - a.wpr)
      .forEach((r, i) => rankByRunId.set(r.runId, i + 1))
  }

  const marketPriceByRunId = new Map<string, number | null>(
    runners.map((r) => [r.runId, r.fixedWinPrice ?? r.startingPrice ?? null]),
  )
  const openPriceByRunId = new Map<string, number | null>(runners.map((r) => [r.runId, r.openFixedPrice ?? null]))

  const result: Record<string, EffectiveRunner> = {}
  for (const r of withEffectiveWpr) {
    const effectivePrice = r.wpr != null ? (priceByRunId.get(r.runId) ?? null) : null
    const marketPrice = marketPriceByRunId.get(r.runId) ?? null
    const openPrice = openPriceByRunId.get(r.runId) ?? null
    const gapFromTop = r.wpr != null ? (gapByRunId.get(r.runId) ?? null) : null
    const isOverlay =
      !r.scratched &&
      effectivePrice != null &&
      marketPrice != null &&
      marketPrice > 1 &&
      marketPrice > effectivePrice &&
      gapFromTop != null &&
      gapFromTop <= OVERLAY_MAX_GAP_FROM_TOP &&
      topRatedWpr != null &&
      topRatedWpr > MIN_TOP_RATED_WPR
    result[r.runId] = {
      effectiveProjectedWpr: r.wpr,
      effectivePrice,
      effectiveRank: r.wpr != null ? (rankByRunId.get(r.runId) ?? null) : null,
      hasOverride: r.hasOverride,
      scratched: r.scratched,
      gapFromTop,
      isOverlay,
      driftedToOverlay:
        isOverlay &&
        openPrice != null &&
        effectivePrice != null &&
        openPrice <= effectivePrice * MATERIAL_UNDERLAY_AT_OPEN_RATIO,
      firmedToUnderlay:
        !r.scratched &&
        openPrice != null &&
        effectivePrice != null &&
        marketPrice != null &&
        openPrice >= effectivePrice * MATERIAL_OVERLAY_AT_OPEN_RATIO &&
        marketPrice < effectivePrice,
    }
  }
  return result
}
