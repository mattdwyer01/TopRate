import { useMemo, useState } from 'react'
import type { Race } from '../../types/domain'
import { EmptyState } from '../../components/EmptyState'
import { groupIntoMeetings, isBushMeeting } from '../../lib/meetings'
import { formatTimeOfDay } from '../../lib/countdown'

interface QuaddieHelperProps {
  races: Race[]
  date: string
  showBush: boolean
  onSelectRace: (raceId: string, date: string, runId?: string) => void
}

interface LegPick {
  runId: string
  tabNumber: number
  horse: string
  projectedWpr: number
  wprPrice: number | null
}

type Tier = 'standout' | 'clear' | 'tight'

interface Leg {
  raceId: string
  raceNumber: number
  startTime: string
  allResulted: boolean
  picks: LegPick[]
  margin: number | null
  tier: Tier | null
}

// Backtest (toprate_runners.csv, 4,669 resulted races, non-scratched
// runners ranked by projected WPR): cumulative probability the actual
// winner is among the top N picks, by tier - i.e. the leg's hit rate if
// you cover that many runners. Index 0 = top1, index i = top(i+1).
const COVERAGE_TABLE: Record<Tier, number[]> = {
  standout: [0.4118, 0.5667, 0.6882, 0.7912, 0.852, 0.9, 0.9441, 0.9706], // n=1020
  clear: [0.2542, 0.437, 0.591, 0.6945, 0.7803, 0.8451, 0.8923, 0.9338], // n=2144
  tight: [0.2047, 0.3887, 0.5395, 0.6698, 0.7767, 0.8346, 0.8831, 0.9256], // n=1505
}

function probabilityFor(tier: Tier | null, cover: number): number | null {
  if (tier == null) return null
  const table = COVERAGE_TABLE[tier]
  return table[Math.min(cover, table.length) - 1]
}

// Defaults chosen as the smallest cover count that clears a ~60% leg hit
// rate (see COVERAGE_TABLE) - a single top pick, even in a standout race,
// misses more often than it hits (~41%), so no tier defaults to 1.
const TIER_INFO: Record<Tier, { label: string; defaultCover: number; className: string }> = {
  standout: { label: 'Standout', defaultCover: 3, className: 'border-emerald-line bg-emerald-bg text-emerald-deep' },
  clear: { label: 'Clear', defaultCover: 4, className: 'border-amber-line bg-amber-bg text-amber' },
  tight: { label: 'Tight', defaultCover: 4, className: 'border-line text-ink-mute' },
}

function tierFor(margin: number | null): Tier | null {
  if (margin == null) return null
  if (margin >= 3.5) return 'standout'
  if (margin >= 1.0) return 'clear'
  return 'tight'
}

export function QuaddieHelper({ races, date, showBush, onSelectRace }: QuaddieHelperProps) {
  const meetings = useMemo(() => {
    const all = groupIntoMeetings(races, date)
    return showBush ? all : all.filter((m) => !isBushMeeting(m))
  }, [races, date, showBush])

  const [venueChoice, setVenueChoice] = useState<string | null>(null)
  const activeVenue = venueChoice && meetings.some((m) => m.venue === venueChoice) ? venueChoice : (meetings[0]?.venue ?? null)

  const legs = useMemo<Leg[]>(() => {
    const meeting = meetings.find((m) => m.venue === activeVenue)
    if (!meeting) return []
    return meeting.races.map((race) => {
      const ranked = race.runners
        .filter((r) => !r.dataScratched && r.projectedWpr != null)
        .sort((a, b) => b.projectedWpr! - a.projectedWpr!)
      const picks: LegPick[] = ranked.map((r) => ({
        runId: r.runId,
        tabNumber: r.tabNumber,
        horse: r.horse,
        projectedWpr: r.projectedWpr!,
        wprPrice: r.wprPrice,
      }))
      const margin = picks.length >= 2 ? picks[0].projectedWpr - picks[1].projectedWpr : null
      return {
        raceId: race.raceId,
        raceNumber: race.raceNumber,
        startTime: race.startTime,
        allResulted: race.allResulted,
        picks,
        margin,
        tier: tierFor(margin),
      }
    })
  }, [meetings, activeVenue])

  // Keyed by raceId, so a venue switch just stops applying (stale keys for
  // the old venue's races never match the new venue's leg IDs) rather than
  // needing an explicit reset. Starts empty - a real quaddie is a handful
  // of nominated legs (check the TAB card), not every race at the meeting,
  // so the user opts individual races in rather than opting the rest out.
  const [selectedLegs, setSelectedLegs] = useState<Set<string>>(() => new Set())
  const [coverOverrides, setCoverOverrides] = useState<Record<string, number>>({})

  function toggleLeg(raceId: string) {
    setSelectedLegs((prev) => {
      const next = new Set(prev)
      if (next.has(raceId)) next.delete(raceId)
      else next.add(raceId)
      return next
    })
  }

  function setCover(raceId: string, count: number, max: number) {
    setCoverOverrides((prev) => ({ ...prev, [raceId]: Math.max(1, Math.min(count, max)) }))
  }

  function coverFor(leg: Leg): number {
    const fallback = leg.tier ? TIER_INFO[leg.tier].defaultCover : 1
    const override = coverOverrides[leg.raceId]
    return Math.max(1, Math.min(override ?? fallback, leg.picks.length))
  }

  function isIncludable(leg: Leg): boolean {
    return !leg.allResulted && leg.picks.length > 0
  }

  function isIncluded(leg: Leg): boolean {
    return isIncludable(leg) && selectedLegs.has(leg.raceId)
  }

  const includedLegs = legs.filter(isIncluded)
  const combinations = includedLegs.length > 0 ? includedLegs.reduce((acc, leg) => acc * coverFor(leg), 1) : 0
  // Product of each leg's own hit rate - assumes leg outcomes are
  // independent, which is a simplification (they share the same day's
  // track/weather) but a reasonable estimate for an overall quaddie read.
  const legProbabilities = includedLegs.map((leg) => probabilityFor(leg.tier, coverFor(leg)))
  const combinedProbability = legProbabilities.every((p) => p != null)
    ? legProbabilities.reduce((acc, p) => acc * (p as number), 1)
    : null

  if (meetings.length === 0) {
    return <EmptyState message={`No meetings on ${date}.`} />
  }

  return (
    <div className="flex flex-col gap-4">
      <div className="flex flex-wrap items-center gap-2">
        <label className="flex items-center gap-1.5 text-sm text-ink-mute">
          Meeting
          <select
            value={activeVenue ?? ''}
            onChange={(e) => setVenueChoice(e.target.value)}
            className="rounded-md border border-line bg-panel px-2 py-1 text-sm"
          >
            {meetings.map((m) => (
              <option key={m.venue} value={m.venue}>
                {m.venue}
              </option>
            ))}
          </select>
        </label>
        <p className="text-xs text-ink-mute">
          Tick the races that make up your quaddie legs (check your TAB card for the exact races), then adjust how many runners to cover per leg.
        </p>
      </div>

      <div className="flex flex-col gap-2">
        {legs.map((leg) => {
          const includable = isIncludable(leg)
          const included = isIncluded(leg)
          const cover = coverFor(leg)
          const tierInfo = leg.tier ? TIER_INFO[leg.tier] : null
          const probability = probabilityFor(leg.tier, cover)
          return (
            <div
              key={leg.raceId}
              className={`rounded-lg border bg-panel px-3 py-2.5 ${included ? 'border-line' : 'border-line-soft opacity-60'}`}
            >
              <div className="flex flex-wrap items-center gap-2">
                <input
                  type="checkbox"
                  checked={included}
                  disabled={!includable}
                  onChange={() => toggleLeg(leg.raceId)}
                  className="h-4 w-4 accent-emerald"
                />
                <button
                  type="button"
                  onClick={() => onSelectRace(leg.raceId, date)}
                  className="font-medium text-ink hover:underline"
                >
                  R{leg.raceNumber}
                </button>
                <span className="text-xs text-ink-mute">
                  {leg.allResulted ? 'Resulted' : formatTimeOfDay(leg.startTime)}
                </span>
                {tierInfo && (
                  <span className={`rounded-full border px-2 py-0.5 font-mono text-[11px] font-semibold ${tierInfo.className}`}>
                    {tierInfo.label} (+{leg.margin!.toFixed(1)})
                  </span>
                )}
                {leg.picks.length === 0 && <span className="text-xs text-ink-mute">No projection</span>}
                {includable && (
                  <div className="ml-auto flex items-center gap-3">
                    {included && probability != null && (
                      <span
                        title="Backtested probability the actual winner is among the covered runners"
                        className="font-mono text-xs font-semibold text-emerald-deep"
                      >
                        {(probability * 100).toFixed(1)}% to land
                      </span>
                    )}
                    <label className="flex items-center gap-1.5 text-xs text-ink-mute">
                      Cover top
                      <input
                        type="number"
                        min={1}
                        max={leg.picks.length}
                        value={cover}
                        disabled={!included}
                        onChange={(e) => setCover(leg.raceId, Number(e.target.value) || 1, leg.picks.length)}
                        className="w-12 rounded-md border border-line bg-bg px-1.5 py-0.5 text-xs font-mono disabled:opacity-50"
                      />
                    </label>
                  </div>
                )}
              </div>
              {included && leg.picks.length > 0 && (
                <div className="mt-2 flex flex-wrap gap-x-4 gap-y-1 pl-6 text-sm">
                  {leg.picks.slice(0, cover).map((p) => (
                    <span key={p.runId} className="text-ink-mute">
                      <span className="font-mono text-ink">{p.tabNumber}.</span> {p.horse}
                      {p.wprPrice != null && <span className="font-mono"> ${p.wprPrice.toFixed(2)}</span>}
                    </span>
                  ))}
                </div>
              )}
            </div>
          )
        })}
      </div>

      <div className="rounded-lg border border-line bg-panel px-3 py-2.5 text-sm">
        {includedLegs.length === 0 ? (
          <span className="text-ink-mute">Tick at least one leg to see the combination count.</span>
        ) : (
          <div className="flex flex-col gap-1">
            <span>
              <span className="font-mono font-semibold text-emerald-deep">{combinations}</span>{' '}
              <span className="text-ink-mute">
                combination{combinations === 1 ? '' : 's'} across {includedLegs.length} leg{includedLegs.length === 1 ? '' : 's'}
              </span>
            </span>
            {combinedProbability != null && (
              <span>
                <span className="font-mono font-semibold text-emerald-deep">{(combinedProbability * 100).toFixed(1)}%</span>{' '}
                <span className="text-ink-mute">
                  estimated chance of landing all {includedLegs.length} legs (assumes legs are independent)
                </span>
              </span>
            )}
          </div>
        )}
      </div>
    </div>
  )
}
