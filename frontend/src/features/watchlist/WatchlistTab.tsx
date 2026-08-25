import { useMemo } from 'react'
import type { Race } from '../../types/domain'
import { StatTile } from '../../components/StatTile'
import { Pill } from '../../components/Pill'
import { fmtWpr, fmtPrice } from '../../lib/format'
import { formatTimeOfDay } from '../../lib/countdown'
import {
  computeWatchlist,
  hasKnownOutcome,
  tallyWatchlist,
  type WatchlistEntry,
} from '../../lib/watchlist'
import type { WatchlistThresholds } from '../../lib/watchlistSettings'

interface WatchlistTabProps {
  races: Race[]
  thresholds: WatchlistThresholds
  onSelectRace: (raceId: string, date: string) => void
}

function pct(v: number): string {
  return `${(v * 100).toFixed(1)}%`
}

function signedPct(v: number): string {
  const s = `${(v * 100).toFixed(1)}%`
  return v > 0 ? `+${s}` : s
}

function ordinal(n: number): string {
  const mod100 = n % 100
  if (mod100 >= 11 && mod100 <= 13) return `${n}th`
  switch (n % 10) {
    case 1:
      return `${n}st`
    case 2:
      return `${n}nd`
    case 3:
      return `${n}rd`
    default:
      return `${n}th`
  }
}

function formatRaceDate(date: string): string {
  const d = new Date(`${date}T00:00:00`)
  if (Number.isNaN(d.getTime())) return date
  return d.toLocaleDateString('en-AU', { day: 'numeric', month: 'short' })
}

function EntryRow({ entry, onSelectRace }: { entry: WatchlistEntry; onSelectRace: (raceId: string, date: string) => void }) {
  const { race, runner, gap } = entry
  const settled = hasKnownOutcome(entry)
  const won = settled && runner.won
  return (
    <button
      type="button"
      onClick={() => onSelectRace(race.raceId, race.date)}
      className="flex w-full items-center justify-between gap-3 border-b border-line-soft px-3 py-2.5 text-left text-sm transition-colors last:border-b-0 hover:bg-bg"
    >
      <div className="min-w-0">
        <div className="flex items-center gap-1.5">
          <span className="font-medium text-ink">{runner.horse}</span>
          <span className="text-xs text-ink-faint">
            {race.venue} R{race.raceNumber}
          </span>
        </div>
        <div className="mt-0.5 flex items-center gap-2 text-xs text-ink-faint">
          <span>
            {formatRaceDate(race.date)} {formatTimeOfDay(race.startTime)}
          </span>
          <span>gap +{fmtWpr(gap)}</span>
          <span>{fmtPrice(runner.fixedWinPrice)}</span>
        </div>
      </div>
      <div className="flex-none text-right">
        {settled ? (
          won ? (
            <span className="rounded-full border border-emerald-line bg-emerald-bg px-2 py-0.5 font-mono text-xs font-semibold text-emerald-deep">
              WON
            </span>
          ) : (
            <span className="rounded-full border border-line bg-bg px-2 py-0.5 font-mono text-xs text-ink-mute">
              {runner.finishPosition != null ? ordinal(Math.round(runner.finishPosition)) : 'LOST'}
            </span>
          )
        ) : (
          <span className="rounded-full border border-amber-line bg-amber-bg px-2 py-0.5 font-mono text-xs font-semibold text-amber">
            PENDING
          </span>
        )}
      </div>
    </button>
  )
}

// Paper-tracking view for the one "back the top-rated runner" pattern from
// the Aug 2026 backtesting session that survived a chronological split-half
// check (see lib/watchlist.ts). Not a proven edge - this exists to
// accumulate real, live, out-of-sample results before any staking decision,
// not to recommend bets. Thresholds are user-editable in Settings.
export function WatchlistTab({ races, thresholds, onSelectRace }: WatchlistTabProps) {
  const entries = useMemo(
    () => computeWatchlist(races, thresholds.minGap, thresholds.minPrice),
    [races, thresholds],
  )
  // Upcoming: soonest-to-jump first. Settled: most recently run first. Both
  // orderings are by the race's actual date+time (startTime is a full
  // timestamp, not just a time-of-day), not just insertion order.
  const upcoming = useMemo(
    () => entries.filter((e) => !hasKnownOutcome(e)).sort((a, b) => a.race.startTime.localeCompare(b.race.startTime)),
    [entries],
  )
  const settled = useMemo(
    () => entries.filter(hasKnownOutcome).sort((a, b) => b.race.startTime.localeCompare(a.race.startTime)),
    [entries],
  )
  const tally = useMemo(() => tallyWatchlist(entries), [entries])

  return (
    <div className="flex flex-col gap-3">
      <div className="rounded-lg border border-line bg-panel p-3 shadow-[var(--shadow-1)]">
        <h2 className="text-sm font-semibold text-ink">Watchlist</h2>
        <p className="mt-1 text-xs text-ink-mute">
          Flags the #1 WPR-ranked runner when it leads #2 by {thresholds.minGap.toFixed(1)}+ WPR points, the
          market still has it at ${thresholds.minPrice.toFixed(2)}+ fixed, and there's no first starter anywhere
          in the field. This pattern held up in a chronological split-half backtest, but the sample behind it is
          still thin - this is paper-tracking to build real evidence before any staking decision, not a bet
          recommendation. Thresholds are editable in Settings.
        </p>
      </div>

      <div className="grid grid-cols-2 gap-2 sm:grid-cols-4">
        <StatTile label="Settled bets" value={String(tally.n)} />
        <StatTile
          label="Strike rate"
          value={tally.n > 0 ? pct(tally.strikeRate) : '-'}
          sublabel={tally.n > 0 ? `${tally.wins}/${tally.n}` : undefined}
        />
        <StatTile
          label="Flat ROI"
          value={tally.n > 0 ? signedPct(tally.flatRoi) : '-'}
          tone={tally.n === 0 ? 'muted' : tally.flatRoi >= 0 ? 'positive' : 'negative'}
        />
        <StatTile
          label="Prop. ROI"
          value={tally.n > 0 ? signedPct(tally.propRoi) : '-'}
          tone={tally.n === 0 ? 'muted' : tally.propRoi >= 0 ? 'positive' : 'negative'}
        />
      </div>

      <div className="rounded-lg border border-line bg-panel">
        <div className="flex items-center justify-between border-b border-line px-3 py-2">
          <h3 className="text-sm font-semibold text-ink">Upcoming ({upcoming.length})</h3>
          <Pill tone="amber">Pending</Pill>
        </div>
        {upcoming.length === 0 ? (
          <div className="px-3 py-4 text-sm text-ink-faint">No flagged runners in the currently loaded races.</div>
        ) : (
          upcoming.map((e) => <EntryRow key={e.runner.runId} entry={e} onSelectRace={onSelectRace} />)
        )}
      </div>

      <div className="rounded-lg border border-line bg-panel">
        <div className="border-b border-line px-3 py-2">
          <h3 className="text-sm font-semibold text-ink">Track record ({settled.length})</h3>
        </div>
        {settled.length === 0 ? (
          <div className="px-3 py-4 text-sm text-ink-faint">No settled flagged bets yet.</div>
        ) : (
          settled.map((e) => <EntryRow key={e.runner.runId} entry={e} onSelectRace={onSelectRace} />)
        )}
      </div>
    </div>
  )
}
