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
  // This runner's share of the leg's win probability, normalized so the
  // leg's picks sum to 1 - derived from wprPrice (1/price), not looked up
  // from a tier bucket, so it works for any subset the user builds by
  // hand, not just a contiguous top-N.
  probability: number
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

const TIER_INFO: Record<Tier, { label: string; className: string }> = {
  standout: { label: 'Standout', className: 'border-emerald-line bg-emerald-bg text-emerald-deep' },
  clear: { label: 'Clear', className: 'border-amber-line bg-amber-bg text-amber' },
  tight: { label: 'Tight', className: 'border-line text-ink-mute' },
}

function tierFor(margin: number | null): Tier | null {
  if (margin == null) return null
  if (margin >= 3.5) return 'standout'
  if (margin >= 1.0) return 'clear'
  return 'tight'
}

// The smallest prefix (by descending win probability) whose cumulative
// probability reaches the target - i.e. "how many, and which, runners do
// I need to cover to have roughly a targetPct% chance of landing this leg."
function defaultSelection(leg: Leg, targetFraction: number): Set<string> {
  const ids = new Set<string>()
  let cumulative = 0
  for (const pick of leg.picks) {
    ids.add(pick.runId)
    cumulative += pick.probability
    if (cumulative >= targetFraction) break
  }
  return ids
}

export function QuaddieHelper({ races, date, showBush, onSelectRace }: QuaddieHelperProps) {
  const meetings = useMemo(() => {
    const all = groupIntoMeetings(races, date)
    return showBush ? all : all.filter((m) => !isBushMeeting(m))
  }, [races, date, showBush])

  const [venueChoice, setVenueChoice] = useState<string | null>(null)
  const activeVenue = venueChoice && meetings.some((m) => m.venue === venueChoice) ? venueChoice : (meetings[0]?.venue ?? null)

  const [targetPct, setTargetPct] = useState(70)

  const legs = useMemo<Leg[]>(() => {
    const meeting = meetings.find((m) => m.venue === activeVenue)
    if (!meeting) return []
    return meeting.races.map((race) => {
      const ranked = race.runners
        .filter((r) => !r.dataScratched && r.projectedWpr != null)
        .sort((a, b) => b.projectedWpr! - a.projectedWpr!)
      const weights = ranked.map((r) => (r.wprPrice != null && r.wprPrice > 0 ? 1 / r.wprPrice : 0))
      const totalWeight = weights.reduce((a, b) => a + b, 0)
      const picks: LegPick[] = ranked.map((r, i) => ({
        runId: r.runId,
        tabNumber: r.tabNumber,
        horse: r.horse,
        projectedWpr: r.projectedWpr!,
        wprPrice: r.wprPrice,
        probability: totalWeight > 0 ? weights[i] / totalWeight : 0,
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

  // Which races are quaddie legs at all - keyed by raceId, so a venue
  // switch just stops applying (stale keys for the old venue's races never
  // match the new venue's leg IDs) rather than needing an explicit reset.
  // Starts empty - a real quaddie is a handful of nominated legs (check
  // the TAB card), not every race at the meeting.
  const [selectedLegs, setSelectedLegs] = useState<Set<string>>(() => new Set())
  // Per-runner overrides on top of each leg's target-probability default -
  // keyed by runId (globally unique), true = forced in, false = forced
  // out. Untouched runners keep following the live target-probability
  // default, so changing the target still moves them.
  const [runnerOverrides, setRunnerOverrides] = useState<Record<string, boolean>>({})

  function toggleLeg(raceId: string) {
    setSelectedLegs((prev) => {
      const next = new Set(prev)
      if (next.has(raceId)) next.delete(raceId)
      else next.add(raceId)
      return next
    })
  }

  function toggleRunner(runId: string, currentlySelected: boolean) {
    setRunnerOverrides((prev) => ({ ...prev, [runId]: !currentlySelected }))
  }

  function isIncludable(leg: Leg): boolean {
    return !leg.allResulted && leg.picks.length > 0
  }

  function isIncluded(leg: Leg): boolean {
    return isIncludable(leg) && selectedLegs.has(leg.raceId)
  }

  function selectedRunnersFor(leg: Leg): Set<string> {
    const base = defaultSelection(leg, targetPct / 100)
    const result = new Set<string>()
    for (const pick of leg.picks) {
      const selected = runnerOverrides[pick.runId] ?? base.has(pick.runId)
      if (selected) result.add(pick.runId)
    }
    return result
  }

  function probabilityFor(leg: Leg, selected: Set<string>): number {
    return leg.picks.filter((p) => selected.has(p.runId)).reduce((acc, p) => acc + p.probability, 0)
  }

  const includedLegs = legs.filter(isIncluded)
  const legSelections = includedLegs.map((leg) => ({ leg, selected: selectedRunnersFor(leg) }))
  const combinations = legSelections.length > 0 ? legSelections.reduce((acc, { selected }) => acc * Math.max(1, selected.size), 1) : 0
  // Product of each leg's own hit rate - assumes leg outcomes are
  // independent, which is a simplification (they share the same day's
  // track/weather) but a reasonable estimate for an overall quaddie read.
  const combinedProbability =
    legSelections.length > 0
      ? legSelections.reduce((acc, { leg, selected }) => acc * probabilityFor(leg, selected), 1)
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
        <label className="flex items-center gap-1.5 text-sm text-ink-mute">
          Target win % per leg
          <input
            type="number"
            min={1}
            max={99}
            value={targetPct}
            onChange={(e) => setTargetPct(Math.min(99, Math.max(1, Number(e.target.value) || 1)))}
            className="w-14 rounded-md border border-line bg-panel px-2 py-1 text-sm font-mono"
          />
        </label>
        <p className="text-xs text-ink-mute">
          Tick the races that make up your quaddie legs (check your TAB card for the exact races). Runners are pre-selected up to the target, then use +/- to build your own coverage per leg.
        </p>
      </div>

      <div className="flex flex-col gap-2">
        {legs.map((leg) => {
          const includable = isIncludable(leg)
          const included = isIncluded(leg)
          const selected = included ? selectedRunnersFor(leg) : new Set<string>()
          const probability = included ? probabilityFor(leg, selected) : null
          const tierInfo = leg.tier ? TIER_INFO[leg.tier] : null
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
                {included && probability != null && (
                  <span
                    title="Sum of the selected runners' implied win probability (from WPR $)"
                    className="ml-auto font-mono text-xs font-semibold text-emerald-deep"
                  >
                    {(probability * 100).toFixed(1)}% to land
                  </span>
                )}
              </div>
              {included && leg.picks.length > 0 && (
                <div className="mt-2 flex flex-col gap-0.5 pl-6">
                  {leg.picks.map((p) => {
                    const isSelected = selected.has(p.runId)
                    return (
                      <div key={p.runId} className="flex items-center gap-2 text-sm">
                        <button
                          type="button"
                          onClick={() => toggleRunner(p.runId, isSelected)}
                          title={isSelected ? 'Remove from coverage' : 'Add to coverage'}
                          className={`flex h-4 w-4 shrink-0 items-center justify-center rounded-full border font-mono text-[11px] leading-none transition-colors ${
                            isSelected
                              ? 'border-emerald bg-emerald text-white hover:opacity-80'
                              : 'border-line text-ink-mute hover:border-emerald hover:text-emerald'
                          }`}
                        >
                          {isSelected ? '−' : '+'}
                        </button>
                        <span className={`font-mono ${isSelected ? 'text-ink' : 'text-ink-mute'}`}>{p.tabNumber}.</span>
                        <span className={isSelected ? 'text-ink' : 'text-ink-mute'}>{p.horse}</span>
                        <span className="ml-auto font-mono text-xs text-ink-mute">
                          {(p.probability * 100).toFixed(1)}%{p.wprPrice != null && ` · $${p.wprPrice.toFixed(2)}`}
                        </span>
                      </div>
                    )
                  })}
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
