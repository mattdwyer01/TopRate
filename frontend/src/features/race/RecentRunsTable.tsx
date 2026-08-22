import type { FormRun } from '../../types/domain'

interface RecentRunsTableProps {
  runs: FormRun[]
  peakRun: FormRun | null
}

function fmtSect(v: number | null): string {
  if (v == null) return '—'
  return `${v > 0 ? '+' : ''}${v.toFixed(1)}`
}

// Colour reflects the horse's sectional figure against the race-wide shape
// for the same checkpoint: green where the horse ran faster than the shape
// (against-shape running, a form-strength signal), red where slower.
function sectClass(horse: number | null, race: number | null): string {
  if (horse == null || race == null) return 'text-ink-mute'
  if (horse > race) return 'text-emerald-deep font-medium'
  if (horse < race) return 'text-rose font-medium'
  return 'text-ink-mute'
}

function goingClass(going: string | null): string {
  if (!going) return 'bg-bg text-ink-faint'
  const g = going.toLowerCase()
  if (g.startsWith('good')) return 'bg-emerald-bg text-emerald-deep'
  if (g.startsWith('soft')) return 'bg-amber/15 text-amber'
  if (g.startsWith('heavy')) return 'bg-rose/15 text-rose'
  if (g.startsWith('firm')) return 'bg-slate/15 text-slate'
  return 'bg-bg text-ink-faint'
}

function parseISO(s: string | undefined): Date | null {
  if (!s) return null
  const t = Date.parse(s)
  return Number.isNaN(t) ? null : new Date(t)
}

function daysBetween(a: Date | null, b: Date | null): number | null {
  if (!a || !b) return null
  return Math.round((a.getTime() - b.getTime()) / 86_400_000)
}

function runningLine(r: FormRun): string {
  const parts = [r.positionSettled, r.position800m, r.position400m, r.finishPosition]
  if (parts.every((p) => p == null)) return '—'
  return parts.map((p) => (p != null ? p : '-')).join('-')
}

function RunRow({ run, isPeak }: { run: FormRun; isPeak: boolean }) {
  return (
    <tr className={`transition-colors ${isPeak ? 'bg-amber/10 hover:bg-amber/20' : 'hover:bg-bg'}`}>
      <td className="px-2 py-1 whitespace-nowrap">{run.date ?? ''}</td>
      <td className="px-2 py-1 whitespace-nowrap">
        {run.track}
        {isPeak && (
          <span className="ml-1 rounded-full bg-amber/20 px-1.5 py-0.5 text-[10px] font-medium text-amber">
            peak
          </span>
        )}
      </td>
      <td className="px-2 py-1 text-right font-mono">{run.distance}m</td>
      <td className="px-2 py-1">
        <span className={`rounded-full px-1.5 py-0.5 text-xs ${goingClass(run.going)}`}>
          {run.going || '—'}
        </span>
      </td>
      <td className="px-2 py-1 text-right font-mono">{run.barrier ?? '—'}</td>
      <td className="px-2 py-1 whitespace-nowrap">{run.raceClass ?? '—'}</td>
      <td className="max-w-[8rem] truncate px-2 py-1" title={run.jockey ?? ''}>
        {run.jockey ?? '—'}
      </td>
      <td className="px-2 py-1 text-right font-mono">{run.finishPosition ?? '—'}</td>
      <td className="px-2 py-1 text-right font-mono">
        {run.margin != null ? run.margin.toFixed(1) : '—'}
      </td>
      <td className="px-2 py-1 text-right font-mono text-xs text-ink-faint">{runningLine(run)}</td>
      <td className="px-2 py-1 text-right font-mono text-ink-faint">{fmtSect(run.raceShapeEarly)}</td>
      <td className="px-2 py-1 text-right font-mono text-ink-faint">{fmtSect(run.raceShapeMid)}</td>
      <td className="px-2 py-1 text-right font-mono text-ink-faint">{fmtSect(run.raceShapeLate)}</td>
      <td className={`px-2 py-1 text-right font-mono ${sectClass(run.sectionalEarly, run.raceShapeEarly)}`}>
        {fmtSect(run.sectionalEarly)}
      </td>
      <td className={`px-2 py-1 text-right font-mono ${sectClass(run.sectionalTo800, run.raceShapeMid)}`}>
        {fmtSect(run.sectionalTo800)}
      </td>
      <td className={`px-2 py-1 text-right font-mono ${sectClass(run.sectionalLate600, run.raceShapeLate)}`}>
        {fmtSect(run.sectionalLate600)}
      </td>
      <td className="px-2 py-1 text-right font-mono font-semibold text-ink">
        {run.wpr != null ? run.wpr.toFixed(1) : '—'}
      </td>
    </tr>
  )
}

function SeparatorRow({ label }: { label: string }) {
  return (
    <tr>
      <td colSpan={17} className="px-2 py-1 text-center text-xs text-ink-faint">
        &mdash; {label} &mdash;
      </td>
    </tr>
  )
}

function MobileRunCard({ run, isPeak }: { run: FormRun; isPeak: boolean }) {
  return (
    <div className={`flex items-center justify-between gap-2 px-2 py-1.5 ${isPeak ? 'bg-amber/10' : ''}`}>
      <div className="min-w-0">
        <div className="truncate text-xs font-medium text-ink">
          {run.date ?? ''} &middot; {run.track}
          {isPeak && (
            <span className="ml-1 rounded-full bg-amber/20 px-1.5 py-0.5 text-[10px] font-medium text-amber">
              peak
            </span>
          )}
        </div>
        <div className="truncate text-[11px] text-ink-faint">
          {run.distance}m &middot; {run.going || '—'} &middot; Fin {run.finishPosition ?? '—'}
          {run.margin != null ? ` (${run.margin.toFixed(1)})` : ''}
        </div>
      </div>
      <div className="shrink-0 font-mono text-sm font-semibold text-ink">
        {run.wpr != null ? run.wpr.toFixed(1) : '—'}
      </div>
    </div>
  )
}

function MobileSeparator({ label }: { label: string }) {
  return <div className="px-2 py-1 text-center text-xs text-ink-faint">&mdash; {label} &mdash;</div>
}

type Entry =
  | { kind: 'separator'; key: string; label: string }
  | { kind: 'run'; key: string; run: FormRun; isPeak: boolean }

// Shared between the desktop table and the mobile card list below - same
// days-since/spell-gap/career-peak logic, just rendered two different ways,
// so the two layouts can't silently drift apart.
function buildEntries(runs: FormRun[], peakRun: FormRun | null): Entry[] {
  const runDates = runs.map((r) => parseISO(r.date))
  const daysSinceLast = daysBetween(new Date(), runDates[0] ?? null)

  const entries: Entry[] = []
  if (daysSinceLast != null) {
    entries.push({
      kind: 'separator',
      key: 'days-since',
      label: `${daysSinceLast} day${daysSinceLast === 1 ? '' : 's'} since last run`,
    })
  }
  runs.forEach((run, i) => {
    entries.push({ kind: 'run', key: `run-${i}`, run, isPeak: run.isPeakRun })
    if (i + 1 < runs.length) {
      const gap = daysBetween(runDates[i], runDates[i + 1])
      if (gap != null && gap >= 84) {
        const weeks = Math.round(gap / 7)
        entries.push({
          kind: 'separator',
          key: `spell-${i}`,
          label: `spell — ${weeks} weeks (${gap} days) between runs`,
        })
      }
    }
  })

  if (peakRun && !runs.some((r) => r.isPeakRun)) {
    const oldest = runDates[runDates.length - 1] ?? null
    const peakDate = parseISO(peakRun.date)
    const gapToPeak = daysBetween(oldest, peakDate)
    const label =
      gapToPeak != null && gapToPeak > 0
        ? `career peak — ${Math.round(gapToPeak / 7)} weeks (${gapToPeak} days) earlier`
        : 'career peak'
    entries.push({ kind: 'separator', key: 'peak-sep', label })
    entries.push({ kind: 'run', key: 'peak-run', run: peakRun, isPeak: true })
  }

  return entries
}

// Centrepiece evidence table for a runner: last 6 runs newest-first, each
// showing the race-wide sectional shape alongside the horse's own sectionals
// (coloured by whether the horse beat the shape), plus spell/days-since
// separators and the career-peak run appended at the bottom when it falls
// outside the visible window. The full table is desktop-only (17 columns
// doesn't work below sm) - mobile gets a simplified stacked card list with
// just the headline fields, sharing the same entry list so neither layout
// can silently drift from the other.
export function RecentRunsTable({ runs, peakRun }: RecentRunsTableProps) {
  if (!runs.length) return null

  const entries = buildEntries(runs, peakRun)

  return (
    <div>
      <div className="mb-1 flex items-baseline justify-between">
        <span className="text-sm font-semibold text-ink">Recent runs</span>
        <span className="hidden text-xs text-ink-faint sm:inline">
          last {runs.length}, newest first &middot; Pos = settle/800/400/finish &middot; green/red
          sectionals = horse vs race shape
        </span>
        <span className="text-xs text-ink-faint sm:hidden">last {runs.length}, newest first</span>
      </div>

      <div className="hidden overflow-x-auto rounded-lg border border-line sm:block">
        <table className="w-full min-w-[860px] border-collapse text-xs">
          <thead>
            <tr className="border-b border-line bg-bg text-ink-mute">
              <th rowSpan={2} className="px-2 py-1 text-left font-medium">Date</th>
              <th rowSpan={2} className="px-2 py-1 text-left font-medium">Track</th>
              <th rowSpan={2} className="px-2 py-1 text-right font-medium">Dist</th>
              <th rowSpan={2} className="px-2 py-1 text-left font-medium">Going</th>
              <th rowSpan={2} className="px-2 py-1 text-right font-medium">Bar</th>
              <th rowSpan={2} className="px-2 py-1 text-left font-medium">Class</th>
              <th rowSpan={2} className="px-2 py-1 text-left font-medium">Jockey</th>
              <th rowSpan={2} className="px-2 py-1 text-right font-medium">Fin</th>
              <th rowSpan={2} className="px-2 py-1 text-right font-medium">Mgn</th>
              <th rowSpan={2} className="px-2 py-1 text-right font-medium">Pos</th>
              <th colSpan={3} className="border-l border-line-soft px-2 py-1 text-center font-medium">Race</th>
              <th colSpan={3} className="border-l border-line-soft px-2 py-1 text-center font-medium">Individual</th>
              <th rowSpan={2} className="px-2 py-1 text-right font-medium">WPR</th>
            </tr>
            <tr className="border-b border-line bg-bg text-ink-faint">
              <th className="border-l border-line-soft px-2 py-0.5 text-right font-normal">Early</th>
              <th className="px-2 py-0.5 text-right font-normal">Mid</th>
              <th className="px-2 py-0.5 text-right font-normal">Late</th>
              <th className="border-l border-line-soft px-2 py-0.5 text-right font-normal">Early</th>
              <th className="px-2 py-0.5 text-right font-normal">Mid</th>
              <th className="px-2 py-0.5 text-right font-normal">Late</th>
            </tr>
          </thead>
          <tbody className="divide-y divide-line-soft">
            {entries.map((e) =>
              e.kind === 'separator' ? (
                <SeparatorRow key={e.key} label={e.label} />
              ) : (
                <RunRow key={e.key} run={e.run} isPeak={e.isPeak} />
              ),
            )}
          </tbody>
        </table>
      </div>

      <div className="divide-y divide-line-soft rounded-lg border border-line sm:hidden">
        {entries.map((e) =>
          e.kind === 'separator' ? (
            <MobileSeparator key={e.key} label={e.label} />
          ) : (
            <MobileRunCard key={e.key} run={e.run} isPeak={e.isPeak} />
          ),
        )}
      </div>
    </div>
  )
}
