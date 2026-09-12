import { useMemo, useState } from 'react'
import type { Race, Runner } from '../../types/domain'
import { Pill } from '../../components/Pill'
import { EmptyState } from '../../components/EmptyState'
import { computeEffectiveRace } from '../../lib/raceModel'
import { todayIso } from '../../lib/meetings'
import { formatTimeOfDay } from '../../lib/countdown'
import { fmtPrice } from '../../lib/format'

interface OverlaysTabProps {
  races: Race[]
  priceBeta: number | null
  deltas: Record<string, number>
  bases: Record<string, number>
  scratched: Set<string>
  initialDate?: string | null
  onSelectRace: (raceId: string, date: string, runId?: string) => void
}

const DATE_QUICK_BUTTONS: { label: string; offset: number }[] = [
  { label: 'Yesterday', offset: -1 },
  { label: 'Today', offset: 0 },
  { label: 'Tomorrow', offset: 1 },
]

interface OverlayRow {
  race: Race
  runner: Runner
  effectivePrice: number
  gapFromTop: number
  marketPrice: number
}

// Same proportional-staking formula used throughout this session's backtests
// (stake sized so a win always profits exactly 1 unit) - kept identical here
// so this tab's numbers are directly comparable to anything discussed in
// chat, not a different convention.
function stakeFor(price: number, returnUnits = 1): number {
  return returnUnits / (price - 1)
}

// All overlays on one date, across every race - not filtered to a strategy
// threshold beyond the same 4-WPR-from-top cap the race table's own overlay
// highlight uses (see raceModel.ts's OVERLAY_MAX_GAP_FROM_TOP), so this tab
// and a highlighted race table always agree on what counts as an overlay.
export function OverlaysTab({
  races,
  priceBeta,
  deltas,
  bases,
  scratched,
  initialDate,
  onSelectRace,
}: OverlaysTabProps) {
  const [date, setDate] = useState(() => initialDate ?? todayIso())

  const dayRaces = useMemo(
    () =>
      races
        .filter((r) => r.date === date)
        .sort((a, b) => new Date(a.startTime).getTime() - new Date(b.startTime).getTime()),
    [races, date],
  )

  const overlays = useMemo(() => {
    const rows: OverlayRow[] = []
    for (const race of dayRaces) {
      // Same data-scratch + manual-scratch merge RaceDetail does - a real
      // scratch still needs to exclude that runner from the softmax here,
      // not just visually.
      const effectiveScratched = new Set(scratched)
      for (const r of race.runners) {
        if (r.dataScratched) effectiveScratched.add(r.runId)
      }
      const effectiveByRunId = computeEffectiveRace(race.runners, deltas, bases, priceBeta, effectiveScratched)
      for (const runner of race.runners) {
        const eff = effectiveByRunId[runner.runId]
        if (!eff?.isOverlay || eff.effectivePrice == null || eff.gapFromTop == null) continue
        const marketPrice = runner.fixedWinPrice ?? runner.startingPrice
        if (marketPrice == null) continue
        rows.push({ race, runner, effectivePrice: eff.effectivePrice, gapFromTop: eff.gapFromTop, marketPrice })
      }
    }
    return rows
  }, [dayRaces, deltas, bases, priceBeta, scratched])

  const resulted = overlays.filter((o) => o.runner.finishPosition != null)
  const summary = useMemo(() => {
    if (resulted.length === 0) return null
    let staked = 0
    let profit = 0
    let wins = 0
    for (const o of resulted) {
      const stake = stakeFor(o.marketPrice)
      staked += stake
      if (o.runner.won) {
        profit += stake * (o.marketPrice - 1)
        wins += 1
      } else {
        profit -= stake
      }
    }
    return { n: resulted.length, strike: wins / resulted.length, roi: staked > 0 ? profit / staked : 0, profit }
  }, [resulted])

  return (
    <div className="flex flex-col gap-4">
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
      </div>

      <div className="rounded-lg border border-line bg-panel p-3 text-sm text-ink-mute">
        <p>
          <span className="font-semibold text-ink">{overlays.length}</span> overlay
          {overlays.length === 1 ? '' : 's'} on {date} - market price longer than our fair WPR $ price, within 4 WPR
          points of the top-rated runner in its race, and only in races where that top-rated runner is itself rated
          over 80.
        </p>
        {summary && (
          <p className="mt-1">
            <span className="font-semibold text-ink">{summary.n}</span> resulted so far &middot; strike{' '}
            <span className="font-semibold text-ink">{(summary.strike * 100).toFixed(1)}%</span> &middot; ROI{' '}
            <span className={`font-semibold ${summary.roi >= 0 ? 'text-emerald-deep' : 'text-rose'}`}>
              {summary.roi >= 0 ? '+' : ''}
              {(summary.roi * 100).toFixed(1)}%
            </span>{' '}
            ({summary.profit >= 0 ? '+' : ''}
            {summary.profit.toFixed(2)}u, proportional staking)
          </p>
        )}
        <p className="mt-1 text-xs text-ink-faint">
          One day's numbers are noise, not a signal - the ~67-day backtest behind this feature found "bet every
          overlay" loses money on average. Useful for tracking outcomes over time, not for judging any single day.
        </p>
      </div>

      {overlays.length === 0 ? (
        <EmptyState message={`No overlays within 4 WPR of the top pick on ${date}.`} />
      ) : (
        <div className="overflow-x-auto rounded-lg border border-line bg-panel">
          <table className="w-full min-w-[640px] border-collapse text-sm">
            <thead>
              <tr className="border-b border-line bg-bg text-xs font-medium text-ink-mute">
                <th className="px-3 py-2 text-left">Time</th>
                <th className="px-3 py-2 text-left">Race</th>
                <th className="px-3 py-2 text-left">Horse</th>
                <th className="px-3 py-2 text-right">Gap</th>
                <th className="px-3 py-2 text-right">WPR $</th>
                <th className="px-3 py-2 text-right">Fixed $</th>
                <th className="px-3 py-2 text-right">FP</th>
              </tr>
            </thead>
            <tbody>
              {overlays.map((o) => (
                <tr
                  key={o.runner.runId}
                  role="button"
                  tabIndex={0}
                  onClick={() => onSelectRace(o.race.raceId, o.race.date, o.runner.runId)}
                  onKeyDown={(e) => {
                    if (e.key === 'Enter' || e.key === ' ') {
                      e.preventDefault()
                      onSelectRace(o.race.raceId, o.race.date, o.runner.runId)
                    }
                  }}
                  className="cursor-pointer border-b border-line-soft last:border-b-0 hover:bg-emerald-bg/30"
                >
                  <td className="px-3 py-2 font-mono text-ink-mute">{formatTimeOfDay(o.race.startTime)}</td>
                  <td className="px-3 py-2 text-ink-mute">
                    {o.race.venue} R{o.race.raceNumber}
                  </td>
                  <td className="px-3 py-2 font-medium text-ink">
                    {o.runner.tabNumber}. {o.runner.horse}
                  </td>
                  <td className="px-3 py-2 text-right font-mono text-ink-mute">{o.gapFromTop.toFixed(1)}</td>
                  <td className="px-3 py-2 text-right font-mono text-ink-mute">{fmtPrice(o.effectivePrice)}</td>
                  <td className="px-3 py-2 text-right font-mono text-ink-mute">{fmtPrice(o.marketPrice)}</td>
                  <td className="px-3 py-2 text-right font-mono text-ink-mute">
                    {o.runner.finishPosition != null ? (o.runner.won ? `${o.runner.finishPosition} ✓` : o.runner.finishPosition) : ''}
                  </td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      )}
    </div>
  )
}
