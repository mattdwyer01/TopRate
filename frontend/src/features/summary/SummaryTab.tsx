import { useMemo, useState } from 'react'
import type { Race } from '../../types/domain'
import {
  RANK_SCREEN_JOCKEY_CUT,
  RANK_SCREEN_TIERS,
  RANK_SCREEN_TRAINER_CUT,
  collectRankScreenRows,
  computeRankScreenStats,
  lastNWeekdayDates,
  type RankScreenDateFilter,
  type RankScreenTierId,
} from '../../lib/rankScreens'
import { StatTile } from '../../components/StatTile'
import type { Period } from '../../lib/accuracyStats'

interface SummaryTabProps {
  races: Race[]
  onSelectRace: (raceId: string, date: string, runId?: string) => void
}

const PERIODS: { value: Period; label: string }[] = [
  { value: '30', label: 'Last 30 days' },
  { value: '90', label: 'Last 90 days' },
  { value: 'all', label: 'All time' },
]

const WEEKDAY_LABELS = ['Sunday', 'Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday']

const MAX_DETAIL_ROWS = 100

function fmtDateShort(iso: string): string {
  const [y, m, d] = iso.split('-').map(Number)
  return new Date(Date.UTC(y, m - 1, d)).toLocaleDateString('en-AU', {
    day: 'numeric',
    month: 'short',
    timeZone: 'UTC',
  })
}

function fmtSigned(v: number | null, digits = 1): string {
  if (v == null || Number.isNaN(v)) return '-'
  return `${v > 0 ? '+' : ''}${v.toFixed(digits)}%`
}

function fmtPct(v: number | null): string {
  if (v == null || Number.isNaN(v)) return '-'
  return `${v.toFixed(1)}%`
}

// Three toggleable volume tiers of one validated rank-conjunction betting
// rule (see lib/rankScreens.ts for the full backtest history/caveats):
// within-race form (ewm5) rank AND jockey_win_pct_90d>=15% AND
// trainer_win_pct_365d>=15%, with only the form-rank cutoff varying across
// tiers to trade selectivity for volume. Deliberately its own tab, not
// folded into Review's Signal Watch panel - this is 3 candidate rules at
// once, not one, and the user asked for a dedicated place to flip between
// them.
export function SummaryTab({ races, onSelectRace }: SummaryTabProps) {
  const [dateMode, setDateMode] = useState<'period' | 'weekday'>('period')
  const [period, setPeriod] = useState<Period>('90')
  const [weekday, setWeekday] = useState(6) // Saturday
  const [weekdayCount, setWeekdayCount] = useState(4)
  const [excludeBush, setExcludeBush] = useState(true)
  const [tierId, setTierId] = useState<RankScreenTierId>('targeted')

  const tier = RANK_SCREEN_TIERS.find((t) => t.id === tierId) ?? RANK_SCREEN_TIERS[0]

  const dateFilter: RankScreenDateFilter =
    dateMode === 'period' ? { mode: 'period', period } : { mode: 'weekday', weekday, count: weekdayCount }

  const rows = useMemo(
    () => collectRankScreenRows(races, tierId, { dateFilter, excludeBush }),
    // dateFilter is rebuilt every render from primitives below - listing those
    // primitives (not the object itself) keeps this memo from recomputing on
    // every render.
    // eslint-disable-next-line react-hooks/exhaustive-deps
    [races, tierId, dateMode, period, weekday, weekdayCount, excludeBush]
  )
  const stats = useMemo(() => computeRankScreenStats(rows), [rows])

  // Shown under the weekday picker so "last 4 Saturdays" is reproducible
  // rather than a black box - names exactly which calendar dates qualified.
  const weekdayDates = useMemo(
    () => (dateMode === 'weekday' ? [...lastNWeekdayDates(weekday, weekdayCount)].sort().reverse() : []),
    [dateMode, weekday, weekdayCount]
  )

  return (
    <div className="flex flex-col gap-4">
      <div className="flex flex-wrap items-center gap-3">
        <div className="flex rounded-md border border-line bg-panel p-0.5">
          <button
            type="button"
            onClick={() => setDateMode('period')}
            className={
              'rounded px-2.5 py-1 text-xs font-medium transition-colors ' +
              (dateMode === 'period' ? 'bg-emerald text-white' : 'text-ink-mute hover:text-ink')
            }
          >
            Rolling window
          </button>
          <button
            type="button"
            onClick={() => setDateMode('weekday')}
            className={
              'rounded px-2.5 py-1 text-xs font-medium transition-colors ' +
              (dateMode === 'weekday' ? 'bg-emerald text-white' : 'text-ink-mute hover:text-ink')
            }
          >
            Day of week
          </button>
        </div>

        {dateMode === 'period' ? (
          <div className="flex rounded-md border border-line bg-panel p-0.5">
            {PERIODS.map((p) => (
              <button
                key={p.value}
                type="button"
                onClick={() => setPeriod(p.value)}
                className={
                  'rounded px-2.5 py-1 text-xs font-medium transition-colors ' +
                  (period === p.value ? 'bg-emerald text-white' : 'text-ink-mute hover:text-ink')
                }
              >
                {p.label}
              </button>
            ))}
          </div>
        ) : (
          <div className="flex flex-wrap items-center gap-1.5 text-xs text-ink-soft">
            <span>Last</span>
            <input
              type="number"
              min={1}
              max={52}
              value={weekdayCount}
              onChange={(e) => setWeekdayCount(Math.min(52, Math.max(1, Number(e.target.value) || 1)))}
              className="w-14 rounded-md border border-line bg-panel px-2 py-1 text-xs text-ink"
            />
            <select
              value={weekday}
              onChange={(e) => setWeekday(Number(e.target.value))}
              className="rounded-md border border-line bg-panel px-2 py-1 text-xs text-ink"
            >
              {WEEKDAY_LABELS.map((label, i) => (
                <option key={i} value={i}>
                  {label}
                  {weekdayCount !== 1 ? 's' : ''}
                </option>
              ))}
            </select>
          </div>
        )}

        <label className="flex items-center gap-1.5 text-xs text-ink-soft">
          <input
            type="checkbox"
            checked={excludeBush}
            onChange={(e) => setExcludeBush(e.target.checked)}
            className="accent-emerald"
          />
          Exclude bush/picnic tracks
        </label>
      </div>

      {dateMode === 'weekday' && weekdayDates.length > 0 && (
        <p className="text-xs text-ink-faint">
          Selected dates: {weekdayDates.map(fmtDateShort).join(', ')}
        </p>
      )}

      <div className="rounded-lg border border-amber-line bg-amber-bg p-3 text-xs text-ink-soft sm:p-4">
        <span className="font-semibold text-ink">Experimental, not a proven edge.</span> These three tiers are
        one backtested rule (form/ewm5 rank AND jockey 90-day win% &ge; {RANK_SCREEN_JOCKEY_CUT}% AND trainer
        365-day win% &ge; {RANK_SCREEN_TRAINER_CUT}%), varying only how many top-ranked-by-form runners per
        race qualify. It came from a wide offline search across dozens of signal combinations, checked across
        chronological halves, the real last 30 days, and the last 4 actual Saturdays - direction held positive
        every time, but magnitude shrank on the more recent, smaller checks. Track it here against real
        results; it is not a bet recommendation.
      </div>

      <div className="flex flex-wrap gap-2">
        {RANK_SCREEN_TIERS.map((t) => (
          <button
            key={t.id}
            type="button"
            onClick={() => setTierId(t.id)}
            className={
              'flex-1 min-w-[180px] rounded-lg border px-3 py-2 text-left transition-colors ' +
              (tierId === t.id
                ? 'border-emerald-line bg-emerald-bg'
                : 'border-line bg-panel hover:bg-bg')
            }
          >
            <div className={'text-sm font-semibold ' + (tierId === t.id ? 'text-emerald-deep' : 'text-ink')}>
              {t.label}
            </div>
            <div className="mt-0.5 text-xs text-ink-faint">Form rank top-{t.formRankMax}</div>
          </button>
        ))}
      </div>

      <p className="text-xs text-ink-faint">{tier.description}</p>

      {stats.n === 0 ? (
        <div className="rounded-lg border border-line bg-panel p-6 text-center text-sm text-ink-mute">
          No runners have matched this rule in this window yet.
        </div>
      ) : (
        <>
          <div className="grid grid-cols-2 gap-2 sm:grid-cols-4">
            <StatTile label="Matches" value={String(stats.n)} />
            <StatTile label="Win strike rate" value={fmtPct(stats.strikePct)} />
            <StatTile label="Place strike rate" value={fmtPct(stats.placeStrikePct)} sublabel="top-3 finish" />
            <StatTile
              label="ROI"
              value={fmtSigned(stats.roiPct, 1)}
              tone={stats.roiPct != null && stats.roiPct > 0 ? 'positive' : 'negative'}
            />
          </div>
          <div className="text-xs text-ink-faint">
            Avg price {stats.avgPrice != null ? `$${stats.avgPrice.toFixed(2)}` : '-'}. ROI/win strike rate use
            win price only (no place-price data is captured); place strike rate has no associated ROI.
          </div>

          <div className="max-h-[560px] overflow-y-auto rounded-lg border border-line bg-panel">
            <table className="w-full text-sm">
              <thead className="sticky top-0 z-10 bg-panel">
                <tr className="border-b border-line text-left text-xs text-ink-mute">
                  <th className="px-3 py-2 font-medium">Date</th>
                  <th className="px-3 py-2 font-medium">Track</th>
                  <th className="px-3 py-2 font-medium">Horse</th>
                  <th className="px-3 py-2 text-right font-medium">Form rank</th>
                  <th className="px-3 py-2 text-right font-medium">Price</th>
                  <th className="px-3 py-2 text-right font-medium">Result</th>
                </tr>
              </thead>
              <tbody className="divide-y divide-line-soft">
                {[...rows]
                  .sort((a, b) => b.date.localeCompare(a.date))
                  .slice(0, MAX_DETAIL_ROWS)
                  .map((r, i) => (
                    <tr
                      key={`${r.raceId}-${r.horse}-${i}`}
                      onClick={() => onSelectRace(r.raceId, r.date, r.runId)}
                      className="cursor-pointer hover:bg-bg"
                    >
                      <td className="whitespace-nowrap px-3 py-1.5 text-ink-mute">{r.date}</td>
                      <td className="whitespace-nowrap px-3 py-1.5">{r.venue}</td>
                      <td className="px-3 py-1.5 font-medium">{r.horse}</td>
                      <td className="px-3 py-1.5 text-right text-ink-mute">#{r.formRank}</td>
                      <td className="px-3 py-1.5 text-right font-mono">${r.price.toFixed(2)}</td>
                      <td className="px-3 py-1.5 text-right">
                        {r.won ? (
                          <span className="font-semibold text-emerald-deep">Won</span>
                        ) : r.placed ? (
                          <span className="text-amber">Placed</span>
                        ) : (
                          <span className="text-ink-mute">Lost</span>
                        )}
                      </td>
                    </tr>
                  ))}
              </tbody>
            </table>
          </div>
          {rows.length > MAX_DETAIL_ROWS && (
            <p className="text-xs text-ink-faint">Showing the most recent {MAX_DETAIL_ROWS} of {rows.length}.</p>
          )}
        </>
      )}
    </div>
  )
}
