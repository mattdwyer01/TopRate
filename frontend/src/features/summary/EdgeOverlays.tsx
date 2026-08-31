import { useMemo, useState } from 'react'
import type { Race, Runner } from '../../types/domain'
import { EmptyState } from '../../components/EmptyState'
import { Pill } from '../../components/Pill'
import { bushMeetingKeys, meetingKey } from '../../lib/meetings'
import { formatTimeOfDay } from '../../lib/countdown'
import { qualifiesForEdgeTier, type EdgeTier } from '../../lib/edgeOverlay'
import { useStrategyPicks } from '../../lib/strategyPicks'
import { EdgeScoreboard } from './EdgeScoreboard'

interface EdgeOverlaysProps {
  races: Race[]
  date: string
  showBush: boolean
  onSelectRace: (raceId: string, date: string, runId?: string) => void
}

// 1 unit = $50, matching the dashboard-wide staking convention.
const UNIT_VALUE_DOLLARS = 50

interface StakingResult {
  profitUnits: number
  roi: number
}

// Proportional stakes are normalized so total units staked matches flat
// staking's total (one unit per bet) - keeps the two $ P&L figures on the
// same total-risk basis for a fair side-by-side comparison.
function computeStaking(rows: OverlayRow[]): { flat: StakingResult; proportional: StakingResult } | null {
  const priced = rows.filter((r) => (r.startingPrice ?? r.fixedPrice) != null)
  if (priced.length === 0) return null
  const avgPrice = priced.reduce((sum, r) => sum + (r.startingPrice ?? r.fixedPrice)!, 0) / priced.length

  let flatProfit = 0
  let propProfit = 0
  let propStakeTotal = 0
  for (const r of priced) {
    const price = (r.startingPrice ?? r.fixedPrice)!
    const propStake = price / avgPrice
    propStakeTotal += propStake
    if (r.won) {
      flatProfit += price - 1
      propProfit += propStake * (price - 1)
    } else {
      flatProfit -= 1
      propProfit -= propStake
    }
  }
  return {
    flat: { profitUnits: flatProfit, roi: (flatProfit / priced.length) * 100 },
    proportional: { profitUnits: propProfit, roi: (propProfit / propStakeTotal) * 100 },
  }
}

interface OverlayRow {
  raceId: string
  runId: string
  venue: string
  raceNumber: number
  startTime: string
  allResulted: boolean
  horse: string
  tabNumber: number
  jockey: string
  trainer: string
  edgeScore: number
  edgeModelProb: number
  edgeMarketProb: number
  blendPrice: number | null
  fixedPrice: number | null
  startingPrice: number | null
  won: boolean
}

const TIER_INFO: Record<EdgeTier, { label: string; blurb: string }> = {
  'edge-8': {
    label: '8%+ edge',
    blurb:
      "Model win probability exceeds the market's implied probability by ≥8 points. A held-out backtest (calibrate_edge_score.py, unseen dates) found this roughly where ROI turns positive - not where it's already been proven best, so treat this as the floor, not a guarantee.",
  },
  'edge-10': {
    label: '10%+ edge',
    blurb: 'The same signal, tighter cut - fewer, higher-edge qualifiers. Not confirmed stronger than 8%+ (see Scoreboard above for real forward performance at each cut).',
  },
  'edge-13': {
    label: '13%+ edge',
    blurb: "Tightest cut. Caution: the held-out backtest found this band noisier, not cleanly better, than 8-13% - a very large edge can also mean the model is confidently wrong (e.g. imputed inputs for a lightly-raced runner), so don't read 'higher edge' as 'safer bet'.",
  },
}

function buildRows(races: Race[], date: string, showBush: boolean, tier: EdgeTier): OverlayRow[] {
  const bushKeys = showBush ? null : bushMeetingKeys(races)
  const out: OverlayRow[] = []
  for (const race of races) {
    if (race.date !== date) continue
    if (bushKeys && bushKeys.has(meetingKey(race))) continue
    for (const r of race.runners as Runner[]) {
      if (!qualifiesForEdgeTier(r, tier)) continue
      out.push({
        raceId: race.raceId,
        runId: r.runId,
        venue: race.venue,
        raceNumber: race.raceNumber,
        startTime: race.startTime,
        allResulted: race.allResulted,
        horse: r.horse,
        tabNumber: r.tabNumber,
        jockey: r.jockey,
        trainer: r.trainer,
        edgeScore: r.edgeScore!,
        edgeModelProb: r.edgeModelProb!,
        edgeMarketProb: r.edgeMarketProb!,
        blendPrice: r.blendPrice,
        fixedPrice: r.fixedWinPrice,
        startingPrice: r.startingPrice,
        won: r.won,
      })
    }
  }
  return out.sort((a, b) => b.edgeScore - a.edgeScore)
}

// Replaces StrategyBets.tsx (Aug 2026) - that tab's qualifiers were gated
// on the leaky jtComboWinPct (see edgeOverlay.ts). This lists runners where
// the validated blend/edge score (wpr_projection.compute_edge_scores) finds
// the market underpricing them, at an adjustable sensitivity.
export function EdgeOverlays({ races, date, showBush, onSelectRace }: EdgeOverlaysProps) {
  const [tier, setTier] = useState<EdgeTier>('edge-8')
  const { picks, toggleTaken } = useStrategyPicks()

  const rows = useMemo(() => buildRows(races, date, showBush, tier), [races, date, showBush, tier])

  const info = TIER_INFO[tier]
  const dayResulted = rows.length > 0 && rows.every((r) => r.allResulted)
  const wins = rows.filter((r) => r.won).length
  const staking = dayResulted ? computeStaking(rows) : null

  return (
    <div className="flex flex-col gap-4">
      <EdgeScoreboard races={races} picks={picks} />
      <div className="flex flex-wrap items-center gap-2">
        <Pill active={tier === 'edge-8'} onClick={() => setTier('edge-8')}>
          8%+ edge
        </Pill>
        <Pill active={tier === 'edge-10'} onClick={() => setTier('edge-10')}>
          10%+ edge
        </Pill>
        <Pill active={tier === 'edge-13'} onClick={() => setTier('edge-13')}>
          13%+ edge
        </Pill>
      </div>
      <p className="text-xs text-ink-mute">{info.blurb}</p>

      {rows.length === 0 ? (
        <EmptyState message={`No ${info.label} qualifiers on ${date}.`} />
      ) : (
        <>
          {dayResulted && (
            <div className="text-sm text-ink-mute">
              {rows.length} qualifying bet{rows.length === 1 ? '' : 's'},{' '}
              <span className="font-mono font-semibold text-emerald-deep">{wins}</span> winner{wins === 1 ? '' : 's'} (
              {((wins / rows.length) * 100).toFixed(1)}% strike)
            </div>
          )}
          {staking && (
            <div className="flex flex-wrap gap-x-6 gap-y-1 text-sm">
              {(
                [
                  ['Flat staking', staking.flat],
                  ['Proportional staking (by price)', staking.proportional],
                ] as const
              ).map(([label, s]) => (
                <div key={label}>
                  <span className="text-ink-mute">{label}: </span>
                  <span className={`font-mono font-semibold ${s.profitUnits >= 0 ? 'text-emerald-deep' : 'text-rose'}`}>
                    {s.profitUnits >= 0 ? '+' : ''}${(s.profitUnits * UNIT_VALUE_DOLLARS).toFixed(0)} (
                    {s.roi >= 0 ? '+' : ''}
                    {s.roi.toFixed(1)}%)
                  </span>
                </div>
              ))}
            </div>
          )}
          {/* Cards, not a table - too much per-runner detail (jockey+trainer,
              model/market probability, edge) to fit a table's fixed columns
              without wrapping into unreadably tall cells on a narrow screen. */}
          <div className="flex flex-col gap-2">
            {rows.map((r) => {
              const priceLabel = dayResulted ? 'SP' : 'Fixed'
              const priceValue = dayResulted ? r.startingPrice : r.fixedPrice
              const taken = Boolean(picks[r.runId])
              return (
                <div
                  key={r.runId}
                  role="button"
                  tabIndex={0}
                  onClick={() => onSelectRace(r.raceId, date, r.runId)}
                  onKeyDown={(e) => {
                    if (e.key === 'Enter' || e.key === ' ') {
                      e.preventDefault()
                      onSelectRace(r.raceId, date, r.runId)
                    }
                  }}
                  className={`cursor-pointer rounded-lg border px-3 py-2.5 text-sm transition-colors hover:bg-bg ${
                    r.won ? 'border-emerald-line bg-emerald-bg/40' : 'border-line bg-panel'
                  } ${taken ? 'ring-1 ring-emerald' : ''}`}
                >
                  <div className="flex flex-wrap items-baseline justify-between gap-x-3">
                    <span className="font-medium text-ink">
                      {r.venue} R{r.raceNumber}
                    </span>
                    <span className="flex items-center gap-2">
                      <span className="text-xs text-ink-mute">
                        {r.allResulted ? (r.won ? 'Won' : 'Resulted') : formatTimeOfDay(r.startTime)}
                      </span>
                      <button
                        type="button"
                        onClick={(e) => {
                          e.stopPropagation()
                          toggleTaken(r.runId, r.raceId, date, tier)
                        }}
                        title={taken ? 'Remove from your tracked bets' : 'Mark as taken - track it in your forward performance'}
                        className={`rounded-full border px-2 py-0.5 text-[11px] font-medium transition-colors ${
                          taken
                            ? 'border-emerald bg-emerald text-white'
                            : 'border-line text-ink-mute hover:border-emerald hover:text-emerald'
                        }`}
                      >
                        {taken ? '✓ Taken' : 'Track'}
                      </button>
                    </span>
                  </div>
                  <div className="mt-1 text-ink">
                    <span className="font-mono text-ink-mute">{r.tabNumber}.</span>{' '}
                    <span className="font-medium">{r.horse}</span>
                  </div>
                  <div className="mt-0.5 text-xs text-ink-mute">
                    {r.jockey} / {r.trainer}
                  </div>
                  <div className="mt-1.5 flex flex-wrap items-center gap-x-4 gap-y-1 text-xs">
                    <span className="font-mono font-semibold text-emerald-deep">
                      +{(r.edgeScore * 100).toFixed(1)}% edge
                    </span>
                    <span className="font-mono text-ink-mute">
                      {(r.edgeModelProb * 100).toFixed(0)}% model vs {(r.edgeMarketProb * 100).toFixed(0)}% market
                    </span>
                    <span className="ml-auto font-mono font-semibold text-ink">
                      Model {r.blendPrice != null ? `$${r.blendPrice.toFixed(2)}` : '—'}
                    </span>
                    <span className="font-mono text-ink-mute">
                      {priceLabel} {priceValue != null ? `$${priceValue.toFixed(2)}` : '—'}
                    </span>
                  </div>
                </div>
              )
            })}
          </div>
        </>
      )}
    </div>
  )
}
