import { useEffect, useMemo, useState } from 'react'
import type { Race } from '../../types/domain'
import { Pill } from '../../components/Pill'
import { INNER_GAP_FROM_TOP, OUTER_GAP_FROM_TOP, SPEED_MAP_TINT_THRESHOLD } from '../../lib/raceModel'
import { formatTimeOfDay } from '../../lib/countdown'
import { raceStatus, STATUS_PILL_TONE } from '../../lib/raceStatus'
import {
  firstFourBox,
  firstFourKey,
  fmtMoney,
  hasEarlyQuaddie,
  product,
  quaddieRaces,
  quinellaBox,
  trifectaBox,
  trifectaKey,
  type QuaddieKind,
} from '../../lib/quaddie'
import { Ladder } from './RaceGlance'
import { inPool, POOL_LABEL, poolMembers, rankRace, type PoolKey } from './quaddiePools'

interface QuaddieProps {
  meeting: Race[] // the meeting's races, in race order
  deltas: Record<string, number>
  bases: Record<string, number>
  scratched: Set<string>
  priceBeta: number | null
  onSelectRace: (raceId: string, date: string, runId?: string) => void
  onBack: () => void
}

const WINDOW = 4
const PICKS_KEY = 'toprate_quaddie_picks_v1'
const UNIT_KEY = 'toprate_quaddie_unit_v1'

function readPicks(): Record<string, string[]> {
  try {
    const raw = window.localStorage.getItem(PICKS_KEY)
    return raw ? (JSON.parse(raw) as Record<string, string[]>) : {}
  } catch {
    return {}
  }
}

function readUnit(): number {
  try {
    const v = Number(window.localStorage.getItem(UNIT_KEY))
    return Number.isFinite(v) && v > 0 ? v : 0.5
  } catch {
    return 0.5
  }
}

// A meeting's late (last four races) or early (the four before) quaddie side by side: each race's projection ladder with the inside-4 and
// inside-6 lines and the speed map adjustment. Counts and costs are plain arithmetic on the pools or on the runners you tick, not tips.
export function Quaddie({ meeting, deltas, bases, scratched, priceBeta, onSelectRace, onBack }: QuaddieProps) {
  const [kind, setKind] = useState<QuaddieKind>('late')
  const hasEarly = hasEarlyQuaddie(meeting)
  const races = useMemo(() => quaddieRaces(meeting, kind), [meeting, kind])

  const [pickMode, setPickMode] = useState(false)
  const [picks, setPicks] = useState<Record<string, string[]>>(readPicks)
  const [unit, setUnit] = useState<number>(readUnit)
  useEffect(() => {
    try {
      window.localStorage.setItem(PICKS_KEY, JSON.stringify(picks))
    } catch {
      // Storage can be blocked; picks just will not survive a reload.
    }
  }, [picks])
  useEffect(() => {
    try {
      window.localStorage.setItem(UNIT_KEY, String(unit))
    } catch {
      // As above.
    }
  }, [unit])

  const ranked = useMemo(() => races.map((r) => rankRace(r, deltas, bases, scratched, priceBeta)), [races, deltas, bases, scratched, priceBeta])
  const inner = ranked.map((rk) => rk.filter((x) => x.inner).length)
  const outer = ranked.map((rk) => rk.filter((x) => x.inner || x.outer).length)
  const pool = ranked.map((rk) => rk.filter(inPool).length)
  const full = races.length === WINDOW

  // Only ticks that still point at a runner in the field count (a scratching drops out of the picks).
  const pickedIds = races.map((r, i) => new Set((picks[r.raceId] ?? []).filter((id) => ranked[i].some((x) => x.runner.runId === id))))
  const pickCounts = pickedIds.map((s) => s.size)
  const myCombos = full && pickCounts.every((n) => n > 0) ? product(pickCounts) : 0

  function toggle(raceId: string, runId: string) {
    setPicks((prev) => {
      const cur = new Set(prev[raceId] ?? [])
      if (cur.has(runId)) cur.delete(runId)
      else cur.add(runId)
      return { ...prev, [raceId]: [...cur] }
    })
  }
  function fill(poolKey: PoolKey) {
    setPicks((prev) => {
      const next = { ...prev }
      races.forEach((r, i) => {
        next[r.raceId] = poolMembers(ranked[i], poolKey).map((x) => x.runner.runId)
      })
      return next
    })
  }
  function clear() {
    setPicks((prev) => {
      const next = { ...prev }
      for (const r of races) delete next[r.raceId]
      return next
    })
  }

  if (races.length === 0) {
    return (
      <div className="flex flex-col gap-3">
        <button type="button" onClick={onBack} className="w-fit text-sm text-emerald hover:underline">
          &larr; Back to meetings
        </button>
        <p className="text-sm text-ink-mute">No quaddie found for this meeting and date.</p>
      </div>
    )
  }

  const unitInput = (
    <label className="flex items-center gap-1.5 text-xs text-ink-soft">
      Unit stake $
      <input
        type="number"
        min={0.01}
        step={0.05}
        value={unit}
        onChange={(e) => {
          const v = Number(e.target.value)
          if (Number.isFinite(v) && v > 0) setUnit(v)
        }}
        className="w-20 rounded-md border border-line bg-panel px-2 py-1 font-mono text-xs"
      />
    </label>
  )

  return (
    <div className="flex flex-col gap-4">
      <div className="flex flex-wrap items-center justify-between gap-2">
        <button type="button" onClick={onBack} className="w-fit text-sm text-emerald hover:underline">
          &larr; Back to meetings
        </button>
        <div className="flex items-center gap-1.5">
          <Pill active={kind === 'late'} onClick={() => setKind('late')}>
            Late quaddie
          </Pill>
          {hasEarly && (
            <Pill active={kind === 'early'} onClick={() => setKind('early')}>
              Early quaddie
            </Pill>
          )}
          <span className="font-mono text-xs text-ink-soft">{races[0] ? `R${races[0].raceNumber} to R${races[races.length - 1].raceNumber}` : ''}</span>
        </div>
      </div>

      <section className="rounded-lg border border-line bg-panel p-3 sm:p-4">
        <h2 className="text-sm font-semibold text-ink">
          {races[0]?.venue} {kind} quaddie
        </h2>
        <p className="mb-2 text-xs text-ink-faint">
          {kind === 'early' && meeting.length < 8 ? 'With seven races or fewer the early quaddie overlaps the late one. ' : ''}Runners inside the {INNER_GAP_FROM_TOP} and {OUTER_GAP_FROM_TOP} WPR lines of each race&apos;s top projection. Inside {OUTER_GAP_FROM_TOP} held about 78% of winners in testing, so a leg
          is rarely safe with fewer. Runners outside the {OUTER_GAP_FROM_TOP} line are added back when their speed map adjustment is +{SPEED_MAP_TINT_THRESHOLD} or better (the green figure in the race table); they show a green ring on the ladder. Counts only, not tips.
        </p>
        <div className="overflow-x-auto">
          <table className="w-full min-w-[320px] text-xs">
            <thead className="text-left text-ink-mute">
              <tr>
                <th className="py-1 font-medium" />
                {races.map((r) => (
                  <th key={r.raceId} className="py-1 text-right font-medium">R{r.raceNumber}</th>
                ))}
                <th className="py-1 text-right font-medium">Combos</th>
                <th className="py-1 text-right font-medium">Cost</th>
              </tr>
            </thead>
            <tbody className="divide-y divide-line-soft">
              {(
                [
                  ['inner', inner],
                  ['outer', outer],
                  ['map', pool],
                ] as [PoolKey, number[]][]
              ).map(([key, counts]) => {
                const ok = full && counts.every((n) => n > 0)
                const combos = ok ? product(counts) : 0
                return (
                  <tr key={key}>
                    <td className="py-1">{POOL_LABEL[key]}</td>
                    {counts.map((n, i) => (
                      <td key={i} className="py-1 text-right font-mono">{n}</td>
                    ))}
                    <td className="py-1 text-right font-mono font-semibold">{ok ? combos.toLocaleString() : '-'}</td>
                    <td className="py-1 text-right font-mono text-ink-mute">{ok ? fmtMoney(combos * unit) : '-'}</td>
                  </tr>
                )
              })}
              {pickCounts.some((n) => n > 0) && (
                <tr>
                  <td className="py-1 font-medium text-emerald-deep">My ticks</td>
                  {pickCounts.map((n, i) => (
                    <td key={i} className="py-1 text-right font-mono">{n}</td>
                  ))}
                  <td className="py-1 text-right font-mono font-semibold">{myCombos ? myCombos.toLocaleString() : '-'}</td>
                  <td className="py-1 text-right font-mono text-ink-mute">{myCombos ? fmtMoney(myCombos * unit) : '-'}</td>
                </tr>
              )}
            </tbody>
          </table>
        </div>
        <div className="mt-3 flex flex-wrap items-center gap-x-4 gap-y-2 border-t border-line-soft pt-3">
          {unitInput}
          <span className="text-[11px] text-ink-faint">Cost is combinations times unit stake. Flexi payouts scale with the stake percentage, not shown here.</span>
        </div>
        <div className="mt-2 flex flex-wrap items-center gap-1.5">
          <Pill active={pickMode} onClick={() => setPickMode(!pickMode)}>
            {pickMode ? 'Ticking runners' : 'Tick my runners'}
          </Pill>
          {pickMode && (
            <>
              <span className="text-xs text-ink-faint">Tap runners on the ladders. Fill from:</span>
              <Pill active={false} onClick={() => fill('inner')}>Inside {INNER_GAP_FROM_TOP}</Pill>
              <Pill active={false} onClick={() => fill('outer')}>Inside {OUTER_GAP_FROM_TOP}</Pill>
              <Pill active={false} onClick={() => fill('map')}>+ favoured map</Pill>
              <Pill active={false} onClick={clear}>Clear</Pill>
            </>
          )}
        </div>
      </section>

      <div className="grid grid-cols-1 gap-4 lg:grid-cols-2">
        {races.map((race, i) => {
          const status = raceStatus(race, Date.now())
          const n = outer[i]
          const a = inner[i]
          return (
            <section key={race.raceId} className="rounded-lg border border-line bg-panel p-3 shadow-[var(--shadow-1)]">
              <div className="mb-1 flex flex-wrap items-center justify-between gap-2">
                <button type="button" onClick={() => onSelectRace(race.raceId, race.date)} className="text-left text-sm font-semibold text-ink hover:text-emerald-deep">
                  R{race.raceNumber} {race.raceName}
                </button>
                <Pill active={false} tone={STATUS_PILL_TONE[status]} onClick={() => onSelectRace(race.raceId, race.date)}>
                  {status === 'resulted' || status === 'interim' ? 'Resulted' : formatTimeOfDay(race.startTime)}
                </Pill>
              </div>
              <div className="mb-1 text-[11px] text-ink-faint">
                {race.distance}m · {race.going || 'going n/a'} · {ranked[i].length} runners · inside {INNER_GAP_FROM_TOP}: {inner[i]} · inside {OUTER_GAP_FROM_TOP}: {outer[i]} · with map: {pool[i]}
              </div>
              {ranked[i].length >= 2 ? (
                <Ladder
                  showSm
                  ranked={ranked[i]}
                  innerGap={INNER_GAP_FROM_TOP}
                  outerGap={OUTER_GAP_FROM_TOP}
                  selected={pickMode || pickedIds[i].size > 0 ? pickedIds[i] : undefined}
                  onSelect={(runId) => (pickMode ? toggle(race.raceId, runId) : onSelectRace(race.raceId, race.date, runId))}
                />
              ) : (
                <p className="py-4 text-center text-xs text-ink-faint">No projections yet for this race.</p>
              )}
              {ranked[i].length >= 3 && (
                <details className="mt-2 border-t border-line-soft pt-2 text-xs">
                  <summary className="cursor-pointer text-ink-mute">Exotics counts and cost for this race</summary>
                  <table className="mt-1.5 w-full">
                    <thead className="text-left text-ink-mute">
                      <tr>
                        <th className="py-0.5 font-medium">Structure</th>
                        <th className="py-0.5 text-right font-medium">Combos</th>
                        <th className="py-0.5 text-right font-medium">Cost</th>
                      </tr>
                    </thead>
                    <tbody className="divide-y divide-line-soft">
                      {[
                        [`Quinella box, inside ${OUTER_GAP_FROM_TOP}`, quinellaBox(n)],
                        [`Trifecta box, inside ${OUTER_GAP_FROM_TOP}`, trifectaBox(n)],
                        [`Trifecta: 1st inside ${INNER_GAP_FROM_TOP}, 2nd and 3rd inside ${OUTER_GAP_FROM_TOP}`, trifectaKey(a, n)],
                        [`First four box, inside ${OUTER_GAP_FROM_TOP}`, firstFourBox(n)],
                        [`First four: 1st inside ${INNER_GAP_FROM_TOP}, rest inside ${OUTER_GAP_FROM_TOP}`, firstFourKey(a, n)],
                      ].map(([label, combos]) => (
                        <tr key={label as string}>
                          <td className="py-0.5">{label}</td>
                          <td className="py-0.5 text-right font-mono">{combos ? (combos as number).toLocaleString() : '-'}</td>
                          <td className="py-0.5 text-right font-mono text-ink-mute">{combos ? fmtMoney((combos as number) * unit) : '-'}</td>
                        </tr>
                      ))}
                    </tbody>
                  </table>
                  <p className="mt-1 text-[11px] text-ink-faint">Unit stake from above. Keying the first-place runner to the tighter pool cuts the combinations against a full box. The capture trade-off was tested on an earlier scoring, not on these exact lines.</p>
                </details>
              )}
            </section>
          )
        })}
      </div>
    </div>
  )
}
