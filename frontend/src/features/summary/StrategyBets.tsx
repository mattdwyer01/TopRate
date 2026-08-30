import { useMemo, useState } from 'react'
import type { Race, Runner } from '../../types/domain'
import { Pill } from '../../components/Pill'
import { EmptyState } from '../../components/EmptyState'
import { bushMeetingKeys, meetingKey } from '../../lib/meetings'
import { formatTimeOfDay } from '../../lib/countdown'
import { qualifiesForTier, recentTop3Rate, type StrategyTier } from '../../lib/jtComboStrategy'
import { useStrategyPicks } from '../../lib/strategyPicks'
import { StrategyScoreboard } from './StrategyScoreboard'

interface StrategyBetsProps {
  races: Race[]
  date: string
  showBush: boolean
  onSelectRace: (raceId: string, date: string, runId?: string) => void
}

interface StrategyRow {
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
  jtComboWinPct: number
  jtComboRides: number
  wprRank: number
  fieldSize: number
  formString: string | null
  wprPrice: number | null
  fixedPrice: number | null
  startingPrice: number | null
  won: boolean
}

const TIER_INFO: Record<StrategyTier, { label: string; blurb: string }> = {
  'high-volume': {
    label: 'High volume',
    blurb: 'WPR rank ≤3, jockey/trainer combo ≥25% (5+ rides together), field ≤10. Backtested 1,220 bets: 37.9% strike, +30.1% ROI.',
  },
  'low-volume': {
    label: 'Low volume',
    blurb: 'The above, plus a quiet recent form line (<40% top-3 finishes lately). Backtested 347 bets: 37.5% strike, +53.2% ROI - fewer bets, stronger edge.',
  },
}

function buildRows(races: Race[], date: string, showBush: boolean, tier: StrategyTier): StrategyRow[] {
  const bushKeys = showBush ? null : bushMeetingKeys(races)
  const out: StrategyRow[] = []
  for (const race of races) {
    if (race.date !== date) continue
    if (bushKeys && bushKeys.has(meetingKey(race))) continue
    for (const r of race.runners as Runner[]) {
      if (!qualifiesForTier(r, tier)) continue
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
        jtComboWinPct: r.jtComboWinPct!,
        jtComboRides: r.jtComboRides!,
        wprRank: r.wprRank!,
        fieldSize: r.fieldSize,
        formString: r.formString,
        wprPrice: r.wprPrice,
        fixedPrice: r.fixedWinPrice,
        startingPrice: r.startingPrice,
        won: r.won,
      })
    }
  }
  return out.sort((a, b) => a.startTime.localeCompare(b.startTime))
}

export function StrategyBets({ races, date, showBush, onSelectRace }: StrategyBetsProps) {
  const [tier, setTier] = useState<StrategyTier>('high-volume')
  const { picks, toggleTaken } = useStrategyPicks()

  const rows = useMemo(() => buildRows(races, date, showBush, tier), [races, date, showBush, tier])

  const info = TIER_INFO[tier]
  const dayResulted = rows.length > 0 && rows.every((r) => r.allResulted)
  const wins = rows.filter((r) => r.won).length

  return (
    <div className="flex flex-col gap-4">
      <StrategyScoreboard races={races} picks={picks} />
      <div className="flex flex-wrap items-center gap-2">
        <Pill active={tier === 'high-volume'} onClick={() => setTier('high-volume')}>
          High volume
        </Pill>
        <Pill active={tier === 'low-volume'} onClick={() => setTier('low-volume')}>
          Low volume
        </Pill>
      </div>
      <p className="text-xs text-ink-mute">{info.blurb}</p>

      {rows.length === 0 ? (
        <EmptyState message={`No ${info.label.toLowerCase()} qualifiers on ${date}.`} />
      ) : (
        <>
          {dayResulted && (
            <div className="text-sm text-ink-mute">
              {rows.length} qualifying bet{rows.length === 1 ? '' : 's'},{' '}
              <span className="font-mono font-semibold text-emerald-deep">{wins}</span> winner{wins === 1 ? '' : 's'} (
              {((wins / rows.length) * 100).toFixed(1)}% strike)
            </div>
          )}
          {/* Cards, not a table - this row has too much per-runner detail
              (jockey+trainer, combo%+rides, form string+top-3%) to fit a
              table's fixed columns without wrapping into unreadably tall
              cells on a narrow screen. A card reflows naturally at any
              width instead of needing horizontal scroll to reach the
              price columns. */}
          <div className="flex flex-col gap-2">
            {rows.map((r) => {
              const top3 = recentTop3Rate(r.formString)
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
                    <span className="font-medium">{r.horse}</span>{' '}
                    <span className="text-xs text-ink-mute">
                      WPR rank {r.wprRank} · field {r.fieldSize}
                    </span>
                  </div>
                  <div className="mt-0.5 text-xs text-ink-mute">
                    {r.jockey} / {r.trainer}
                  </div>
                  <div className="mt-1.5 flex flex-wrap items-center gap-x-4 gap-y-1 text-xs">
                    <span className="font-mono text-ink-mute">
                      Combo {r.jtComboWinPct.toFixed(0)}% ({r.jtComboRides} rides)
                    </span>
                    <span className="font-mono text-ink-mute">
                      Form {r.formString ?? '—'}
                      {top3 != null && ` (${(top3 * 100).toFixed(0)}% top-3)`}
                    </span>
                    <span className="ml-auto font-mono font-semibold text-ink">
                      WPR {r.wprPrice != null ? `$${r.wprPrice.toFixed(2)}` : '—'}
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
