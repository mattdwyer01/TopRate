import { useMemo, useState } from 'react'
import type { Race } from '../../types/domain'
import { Pill } from '../../components/Pill'
import { EmptyState } from '../../components/EmptyState'
import { todayIso, bushMeetingKeys, meetingKey } from '../../lib/meetings'
import { formatTimeOfDay } from '../../lib/countdown'
import { EdgeOverlays } from './EdgeOverlays'

type SummaryMode = 'margins' | 'overlays'

interface SummaryTabProps {
  races: Race[]
  showBush: boolean
  onSelectRace: (raceId: string, date: string, runId?: string) => void
}

interface MarginRow {
  raceId: string
  date: string
  venue: string
  raceNumber: number
  startTime: string
  allResulted: boolean
  runId: string
  horse: string
  tabNumber: number
  secondHorse: string
  margin: number
  wprPrice: number | null
  fixedPrice: number | null
  // A first starter, or any active runner with no base rating (wprNett) to
  // anchor the projection on, makes the projection less reliable - flagged
  // rather than excluded, since these races still sort by the same margin.
  unreliable: boolean
}

const DATE_QUICK_BUTTONS: { label: string; offset: number }[] = [
  { label: 'Yesterday', offset: -1 },
  { label: 'Today', offset: 0 },
  { label: 'Tomorrow', offset: 1 },
]

// Backtest (Aug 2026, ~5,000 resulted races): the model's top pick's win
// rate scales with its projected-WPR gap over the 2nd pick - ~18% under a
// 0.5 gap, up to ~42% at 6.0+. This tab surfaces that gap directly (in race
// order, with a min-margin threshold filter) rather than folding it into a
// per-race badge (see git history for the badge version this replaced).
export function SummaryTab({ races, showBush, onSelectRace }: SummaryTabProps) {
  const [date, setDate] = useState(() => todayIso())
  const [minMargin, setMinMargin] = useState(3)
  const [mode, setMode] = useState<SummaryMode>('overlays')

  const rows = useMemo<MarginRow[]>(() => {
    const bushKeys = showBush ? null : bushMeetingKeys(races)
    const out: MarginRow[] = []
    for (const race of races) {
      if (race.date !== date) continue
      if (bushKeys && bushKeys.has(meetingKey(race))) continue
      const ranked = race.runners
        .filter((r) => !r.dataScratched && r.projectedWpr != null && r.wprRank != null)
        .sort((a, b) => a.wprRank! - b.wprRank!)
      if (ranked.length < 2 || ranked[0].wprRank !== 1 || ranked[1].wprRank !== 2) continue
      const unreliable =
        race.hasFirstStarter || race.runners.some((r) => !r.dataScratched && r.wprNett == null)
      out.push({
        raceId: race.raceId,
        date: race.date,
        venue: race.venue,
        raceNumber: race.raceNumber,
        startTime: race.startTime,
        allResulted: race.allResulted,
        runId: ranked[0].runId,
        horse: ranked[0].horse,
        tabNumber: ranked[0].tabNumber,
        secondHorse: ranked[1].horse,
        margin: ranked[0].projectedWpr! - ranked[1].projectedWpr!,
        wprPrice: ranked[0].wprPrice,
        fixedPrice: ranked[0].fixedWinPrice,
        unreliable,
      })
    }
    return out.sort((a, b) => a.startTime.localeCompare(b.startTime))
  }, [races, date, showBush])

  const filtered = useMemo(() => rows.filter((r) => r.margin >= minMargin), [rows, minMargin])

  return (
    <div className="flex flex-col gap-4">
      <div className="flex rounded-md border border-line bg-bg p-0.5" style={{ width: 'fit-content' }}>
        <Pill active={mode === 'overlays'} onClick={() => setMode('overlays')}>
          Overlays
        </Pill>
        <Pill active={mode === 'margins'} onClick={() => setMode('margins')}>
          Margins
        </Pill>
      </div>

      <div className="flex flex-wrap items-center gap-2">
        {DATE_QUICK_BUTTONS.map((btn) => {
          const btnDate = todayIso(btn.offset)
          return (
            <Pill key={btn.label} active={date === btnDate} onClick={() => setDate(btnDate)}>
              {btn.label}
            </Pill>
          )
        })}
        <input
          type="date"
          value={date}
          onChange={(e) => setDate(e.target.value)}
          className="rounded-md border border-line bg-panel px-2 py-1 text-sm font-mono"
        />
        {mode === 'margins' && (
          <label className="ml-2 flex items-center gap-1.5 text-sm text-ink-mute">
            Min margin to 2nd
            <input
              type="number"
              step="0.5"
              min="0"
              value={minMargin}
              onChange={(e) => setMinMargin(Math.max(0, Number(e.target.value) || 0))}
              className="w-16 rounded-md border border-line bg-panel px-2 py-1 text-sm font-mono"
            />
          </label>
        )}
      </div>

      {mode === 'overlays' && (
        <EdgeOverlays races={races} date={date} showBush={showBush} onSelectRace={onSelectRace} />
      )}

      {mode === 'margins' && (filtered.length === 0 ? (
        <EmptyState
          message={
            rows.length === 0
              ? `No projected races on ${date}.`
              : `No races with a margin ≥ ${minMargin} on ${date}.`
          }
        />
      ) : (
        <div className="overflow-x-auto rounded-lg border border-line bg-panel">
          <table className="w-full border-collapse text-sm">
            <thead>
              <tr className="border-b border-line bg-bg text-xs font-medium text-ink-mute">
                <th className="px-3 py-2 text-left">Race</th>
                <th className="px-3 py-2 text-left">Predicted 1st</th>
                <th className="px-3 py-2 text-left">2nd pick</th>
                <th className="px-3 py-2 text-right">Margin</th>
                <th className="px-3 py-2 text-right">WPR $</th>
                <th className="px-3 py-2 text-right">Fixed $</th>
              </tr>
            </thead>
            <tbody>
              {filtered.map((r) => (
                <tr
                  key={r.raceId}
                  onClick={() => onSelectRace(r.raceId, r.date, r.runId)}
                  className="cursor-pointer border-b border-line-soft transition-colors last:border-b-0 hover:bg-bg"
                >
                  <td className="px-3 py-2">
                    <div className="flex items-center gap-1.5 font-medium text-ink">
                      {r.venue} R{r.raceNumber}
                      {r.unreliable && (
                        <span
                          title="Race includes a first starter or a runner with no base rating - projection less reliable"
                          className="text-amber"
                        >
                          ⚠
                        </span>
                      )}
                    </div>
                    <div className="text-xs text-ink-mute">
                      {r.allResulted ? 'Resulted' : formatTimeOfDay(r.startTime)}
                    </div>
                  </td>
                  <td className="px-3 py-2 text-ink">
                    <span className="font-mono text-ink-mute">{r.tabNumber}.</span> {r.horse}
                  </td>
                  <td className="px-3 py-2 text-ink-mute">{r.secondHorse}</td>
                  <td className="px-3 py-2 text-right font-mono font-semibold text-emerald-deep">
                    +{r.margin.toFixed(1)}
                  </td>
                  <td className="px-3 py-2 text-right font-mono text-ink-mute">
                    {r.wprPrice != null ? `$${r.wprPrice.toFixed(2)}` : '—'}
                  </td>
                  <td className="px-3 py-2 text-right font-mono text-ink-mute">
                    {r.fixedPrice != null ? `$${r.fixedPrice.toFixed(2)}` : '—'}
                  </td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      ))}
    </div>
  )
}
