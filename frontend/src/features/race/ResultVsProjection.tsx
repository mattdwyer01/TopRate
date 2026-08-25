import type { Runner } from '../../types/domain'
import { useMissNotes } from '../../lib/missNotes'

function fmt(v: number | null): string {
  return v == null ? '—' : v.toFixed(1)
}

function ordinal(n: number): string {
  const v = n % 100
  if (v >= 11 && v <= 13) return `${n}th`
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

interface ResultVsProjectionProps {
  runner: Runner
}

// Shown beside CareerStats regardless of whether the runner has raced yet
// (always rendered now, not conditionally - see RunnerDetailModal) so the
// layout doesn't reflow between pre-race and post-race: same card, same
// slot, just an empty Actual side and a placeholder note until there's a
// real result to show. Rebuilt (Aug 2026, second pass) to keep the WPR
// predicted-vs-actual comparison and the race RESULT (finish position,
// margin) visually separate - they're different kinds of fact (a rating
// vs a placing) that a WPR-rank number and a finish-position number
// happening to coincide (e.g. both landing on "8") made read as one
// repeated figure in an earlier layout.
export function ResultVsProjection({ runner }: ResultVsProjectionProps) {
  // Two independent facts, not one: the race RESULT (finish position, won)
  // is known the moment the race resolves, but the settled actual WPR
  // (actualWpr) can lag a day or more behind that - TopRate revises it
  // after the fact, and the pipeline now deliberately waits for that
  // revision rather than writing a same-day placeholder (see
  // update_results()'s race_date < today gate, Aug 2026 - the previous
  // version wrote whatever the feed returned immediately, which turned out
  // to be the horse's PRIOR rating, not this run's, on race day itself).
  // Gating the whole card on actualWpr alone would show "not run yet" for
  // a horse that demonstrably won - hasRun and hasActual are checked
  // separately so the WON badge appears as soon as it's true, independent
  // of whether the WPR comparison is ready yet.
  const hasRun = runner.finishPosition != null
  const hasActual = runner.actualWpr != null
  const { notes, setNote } = useMissNotes()

  const miss = hasActual && runner.projectedWpr != null ? runner.actualWpr! - runner.projectedWpr : null
  const missAbs = miss != null ? Math.abs(miss) : null
  const missClass =
    missAbs == null ? 'text-ink-mute' : missAbs >= 8 ? 'text-rose' : missAbs >= 4 ? 'text-amber' : 'text-emerald-deep'

  let rankText: string | null = null
  if (runner.wprRank != null && runner.actualWprRank != null) {
    const rd = runner.actualWprRank - runner.wprRank
    rankText = rd === 0 ? 'exact' : rd > 0 ? `${rd} lower` : `${-rd} higher`
  }

  return (
    <div className="rounded-lg border border-line bg-panel p-2.5">
      <div className="mb-1.5 text-xs font-semibold text-ink">Result vs projection</div>
      <div className="grid grid-cols-2 gap-3">
        <div>
          <div className="text-[11px] text-ink-faint">Predicted</div>
          <div className="font-mono text-lg font-semibold text-ink">{fmt(runner.projectedWpr)}</div>
          <div className="text-xs text-ink-mute">WPR rank {runner.wprRank ?? '—'}</div>
        </div>
        <div>
          <div className="text-[11px] text-ink-faint">Actual</div>
          <div className={`font-mono text-lg font-semibold ${hasActual ? 'text-ink' : 'text-ink-faint'}`}>
            {hasActual ? fmt(runner.actualWpr) : '—'}
          </div>
          <div className="text-xs text-ink-mute">
            {hasActual ? `WPR rank ${runner.actualWprRank ?? '—'}` : hasRun ? 'settling' : 'not run yet'}
          </div>
        </div>
      </div>

      {hasRun && (
        <div className="mt-2 flex items-center gap-1.5 border-t border-line-soft pt-1.5 text-xs">
          <span
            className={`rounded-full px-1.5 py-0.5 font-mono font-semibold ${
              runner.won ? 'bg-amber-bg text-amber' : 'bg-bg text-ink-mute'
            }`}
          >
            {runner.won ? 'WON' : ordinal(runner.finishPosition!)}
          </span>
          {runner.marginFinish != null && !runner.won && (
            <span className="text-ink-mute">beaten {runner.marginFinish.toFixed(1)}L</span>
          )}
        </div>
      )}

      {hasActual ? (
        <>
          {miss != null && (
            <div className="mt-1.5 flex items-baseline gap-1.5 text-xs">
              <span className="text-ink-mute">Missed by</span>
              <span className={`font-mono font-semibold ${missClass}`}>
                {miss > 0 ? '+' : ''}
                {miss.toFixed(1)}
              </span>
              {rankText && <span className="text-ink-mute">&middot; WPR rank {rankText} than predicted</span>}
            </div>
          )}

          {runner.missReason && (
            <div className="mt-1.5 border-t border-line-soft pt-1.5 text-xs text-ink-mute">
              {runner.missReason}
            </div>
          )}

          {runner.missCategory === 'unexplained' && (
            <div className="mt-1.5">
              <label className="mb-0.5 block text-[11px] text-ink-faint" htmlFor={`miss-note-${runner.runId}`}>
                Your note (why it might have missed)
              </label>
              <textarea
                id={`miss-note-${runner.runId}`}
                className="w-full rounded-md border border-line bg-bg px-2 py-1 text-xs text-ink placeholder:text-ink-faint focus:border-emerald-line focus:outline-none"
                rows={2}
                placeholder="e.g. track bias, gear change, personal read on the run..."
                defaultValue={notes[runner.runId] ?? ''}
                onBlur={(e) => setNote(runner.runId, e.target.value)}
              />
            </div>
          )}
        </>
      ) : hasRun ? (
        <div className="mt-1.5 border-t border-line-soft pt-1.5 text-xs text-ink-faint">
          Actual WPR still settling - usually lands within a day or two.
        </div>
      ) : (
        <div className="mt-2 border-t border-line-soft pt-1.5 text-xs text-ink-faint">Check back after the race.</div>
      )}
    </div>
  )
}
