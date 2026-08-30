import { useMemo, useState } from 'react'
import type { Race, Runner } from '../../types/domain'
import { Pill } from '../../components/Pill'
import { EmptyState } from '../../components/EmptyState'
import { bushMeetingKeys, meetingKey } from '../../lib/meetings'
import { formatTimeOfDay } from '../../lib/countdown'
import { qualifiesForTier, recentTop3Rate, type StrategyTier } from '../../lib/jtComboStrategy'

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

  const rows = useMemo(() => buildRows(races, date, showBush, tier), [races, date, showBush, tier])

  const info = TIER_INFO[tier]
  const dayResulted = rows.length > 0 && rows.every((r) => r.allResulted)
  const wins = rows.filter((r) => r.won).length

  return (
    <div className="flex flex-col gap-4">
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
          <div className="overflow-x-auto rounded-lg border border-line bg-panel">
            <table className="w-full border-collapse text-sm">
              <thead>
                <tr className="border-b border-line bg-bg text-xs font-medium text-ink-mute">
                  <th className="px-3 py-2 text-left">Race</th>
                  <th className="px-3 py-2 text-left">Runner</th>
                  <th className="px-3 py-2 text-left">Jockey / Trainer</th>
                  <th className="px-3 py-2 text-right">Combo</th>
                  <th className="px-3 py-2 text-right">Form</th>
                  <th className="px-3 py-2 text-right">WPR $</th>
                  <th className="px-3 py-2 text-right">{dayResulted ? 'SP' : 'Fixed $'}</th>
                </tr>
              </thead>
              <tbody>
                {rows.map((r) => {
                  const top3 = recentTop3Rate(r.formString)
                  return (
                    <tr
                      key={r.runId}
                      onClick={() => onSelectRace(r.raceId, date, r.runId)}
                      className={`cursor-pointer border-b border-line-soft transition-colors last:border-b-0 hover:bg-bg ${
                        r.won ? 'bg-emerald-bg/40' : ''
                      }`}
                    >
                      <td className="px-3 py-2">
                        <div className="font-medium text-ink">
                          {r.venue} R{r.raceNumber}
                        </div>
                        <div className="text-xs text-ink-mute">
                          {r.allResulted ? (r.won ? 'Won' : 'Resulted') : formatTimeOfDay(r.startTime)}
                        </div>
                      </td>
                      <td className="px-3 py-2 text-ink">
                        <span className="font-mono text-ink-mute">{r.tabNumber}.</span> {r.horse}
                        <div className="text-xs text-ink-mute">WPR rank {r.wprRank} · field {r.fieldSize}</div>
                      </td>
                      <td className="px-3 py-2 text-ink-mute">
                        <div>{r.jockey}</div>
                        <div className="text-xs">{r.trainer}</div>
                      </td>
                      <td className="px-3 py-2 text-right font-mono text-ink-mute">
                        {r.jtComboWinPct.toFixed(0)}%
                        <div className="text-xs">{r.jtComboRides} rides</div>
                      </td>
                      <td className="px-3 py-2 text-right font-mono text-ink-mute">
                        {r.formString ?? '—'}
                        {top3 != null && <div className="text-xs">{(top3 * 100).toFixed(0)}% top-3</div>}
                      </td>
                      <td className="px-3 py-2 text-right font-mono text-ink-mute">
                        {r.wprPrice != null ? `$${r.wprPrice.toFixed(2)}` : '—'}
                      </td>
                      <td className="px-3 py-2 text-right font-mono text-ink-mute">
                        {dayResulted
                          ? r.startingPrice != null
                            ? `$${r.startingPrice.toFixed(2)}`
                            : '—'
                          : r.fixedPrice != null
                            ? `$${r.fixedPrice.toFixed(2)}`
                            : '—'}
                      </td>
                    </tr>
                  )
                })}
              </tbody>
            </table>
          </div>
        </>
      )}
    </div>
  )
}
