import type { Runner } from '../../types/domain'

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
  const hasResult = runner.actualWpr != null

  const miss = hasResult && runner.projectedWpr != null ? runner.actualWpr! - runner.projectedWpr : null
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
          <div className={`font-mono text-lg font-semibold ${hasResult ? 'text-ink' : 'text-ink-faint'}`}>
            {hasResult ? fmt(runner.actualWpr) : '—'}
          </div>
          <div className="text-xs text-ink-mute">
            {hasResult ? `WPR rank ${runner.actualWprRank ?? '—'}` : 'not run yet'}
          </div>
        </div>
      </div>

      {hasResult ? (
        <>
          {miss != null && (
            <div className="mt-2 flex items-baseline gap-1.5 border-t border-line-soft pt-1.5 text-xs">
              <span className="text-ink-mute">Missed by</span>
              <span className={`font-mono font-semibold ${missClass}`}>
                {miss > 0 ? '+' : ''}
                {miss.toFixed(1)}
              </span>
              {rankText && <span className="text-ink-mute">&middot; WPR rank {rankText} than predicted</span>}
            </div>
          )}

          {runner.finishPosition != null && (
            <div className="mt-1.5 flex items-center gap-1.5 text-xs">
              <span
                className={`rounded-full px-1.5 py-0.5 font-mono font-semibold ${
                  runner.won ? 'bg-amber-bg text-amber' : 'bg-bg text-ink-mute'
                }`}
              >
                {runner.won ? 'WON' : ordinal(runner.finishPosition)}
              </span>
              {runner.marginFinish != null && !runner.won && (
                <span className="text-ink-mute">beaten {runner.marginFinish.toFixed(1)}L</span>
              )}
            </div>
          )}
        </>
      ) : (
        <div className="mt-2 border-t border-line-soft pt-1.5 text-xs text-ink-faint">Check back after the race.</div>
      )}
    </div>
  )
}
