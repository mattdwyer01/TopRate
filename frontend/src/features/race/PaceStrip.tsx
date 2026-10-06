import type { Race, Runner } from '../../types/domain'
import { estimatePace } from '../../lib/pace'
import type { TripRace } from '../../lib/tripMap'
import type { Ranked } from './raceFacts'

const POS: Record<string, number> = { Slow: 14, Even: 50, Fast: 80, Hot: 92 }

function names(rs: Runner[]): string {
  return rs.map((r) => `${r.tabNumber}. ${r.horse}`).join(', ')
}

// Pace pressure at a glance: where the expected early speed sits, and three plain sentences about who it helps and hurts.
export function PaceStrip({ race, ranked, active, trip }: { race: Race; ranked: Ranked[]; active: Runner[]; trip: TripRace | null }) {
  const pace = estimatePace(race, active)
  const key = race.paceEstimateLabel === 'Hot' && !pace.fromShape ? 'Hot' : pace.tempoBucket
  const pos = POS[key] ?? 50
  const withSettle = active.filter((r) => r.predictedRelSettle != null)
  const gapOf = new Map((trip?.runners ?? []).filter((t) => t.gap != null).map((t) => [t.rid, t.gap as number]))
  const order = (r: Runner) => (gapOf.size ? (gapOf.get(r.runId) ?? 99) : (r.predictedRelSettle as number))
  const leaders = [...(gapOf.size ? active : withSettle)].sort((a, b) => order(a) - order(b)).slice(0, pace.tempoBucket === 'Fast' ? 3 : 2)
  const n = active.length
  const hurt =
    pace.tempoBucket === 'Fast'
      ? withSettle.filter((r) => r.barrier != null && n > 0 && r.barrier / n >= 0.5 && (r.predictedRelSettle as number) < 0.4)
      : []
  const inner = new Set(ranked.filter((r) => r.inner || r.outer).map((r) => r.runner.runId))
  const suits =
    pace.tempoBucket === 'Fast'
      ? withSettle.filter((r) => inner.has(r.runId) && (r.predictedRelSettle as number) >= 0.6).slice(0, 3)
      : pace.tempoBucket === 'Slow'
        ? withSettle.filter((r) => inner.has(r.runId) && (r.predictedRelSettle as number) < 0.3).slice(0, 3)
        : []
  const tone = pace.tempoBucket === 'Fast' ? 'bg-amber-bg text-amber' : pace.tempoBucket === 'Slow' ? 'bg-bg text-ink-mute' : 'bg-emerald-bg text-emerald-deep'
  return (
    <div className="rounded-lg border border-line bg-panel p-2.5 shadow-[var(--shadow-1)] sm:p-3">
      <div className="flex items-center gap-3">
        <span className="w-10 flex-none text-xs font-semibold uppercase tracking-wide text-ink-faint sm:w-24">
          <span className="sm:hidden">Pace</span>
          <span className="hidden sm:inline">Early speed</span>
        </span>
        <div className="relative h-3.5 flex-1 rounded-full" style={{ background: 'linear-gradient(90deg, var(--color-emerald-bg), var(--color-amber-bg), var(--color-rose-bg))' }}>
          <span className="absolute top-[-3px] h-5 w-[3px] rounded bg-ink" style={{ left: `calc(${pos}% - 1.5px)` }} />
        </div>
        <span className={`flex-none rounded-full px-2.5 py-0.5 text-xs font-semibold ${tone}`}>{pace.display.replace(' (predicted)', '')}</span>
      </div>
      <div className="mt-1.5 flex flex-col gap-0.5 text-xs leading-snug text-ink-soft sm:hidden">
        {leaders.length > 0 && (
          <div>
            <span className="font-semibold text-ink">Lead </span>
            {names(leaders)}
          </div>
        )}
        {hurt.length > 0 && (
          <div>
            <span className="font-semibold text-ink">Hurt </span>
            {names(hurt)}
          </div>
        )}
        {suits.length > 0 && (
          <div>
            <span className="font-semibold text-ink">Suits </span>
            {names(suits)}
          </div>
        )}
        {leaders.length === 0 && <div className="text-ink-mute">Not enough settling data for this field.</div>}
      </div>
      <dl className="mt-2.5 hidden gap-x-4 gap-y-1 text-sm sm:grid sm:grid-cols-[auto_1fr]">
        {leaders.length > 0 && (
          <>
            <dt className="font-semibold text-ink">Likely to lead</dt>
            <dd className="text-ink-soft">{names(leaders)}</dd>
          </>
        )}
        {hurt.length > 0 && (
          <>
            <dt className="font-semibold text-ink">Hurt by the pace</dt>
            <dd className="text-ink-soft">
              {names(hurt)} <span className="text-xs text-ink-mute">(wide gate, has to go forward in a fast race)</span>
            </dd>
          </>
        )}
        {suits.length > 0 && (
          <>
            <dt className="font-semibold text-ink">{pace.tempoBucket === 'Fast' ? 'Suits a fast pace' : 'Suits a slow pace'}</dt>
            <dd className="text-ink-soft">
              {names(suits)} <span className="text-xs text-ink-mute">({pace.tempoBucket === 'Fast' ? 'settles back, in the top group' : 'on speed, in the top group'})</span>
            </dd>
          </>
        )}
        {leaders.length === 0 && <dd className="text-ink-mute sm:col-span-2">Not enough settling data for this field.</dd>}
      </dl>
    </div>
  )
}
