import type { Race, Runner } from '../../types/domain'
import type { CombinedRank } from '../../lib/combinedRank'
import { fmtPrice } from '../../lib/format'
import { FinishBadge } from './rowParts'

interface RaceResultProps {
  race: Race
  combo: Map<string, CombinedRank>
  scratched: Set<string>
  onSelectRunner: (runId: string) => void
}

const ORDINAL = ['', '1st', '2nd', '3rd', '4th']

// Placings for a race that has run. TAB's fast feed gives the order of the first four (and last fixed prices); margins and starting
// prices arrive with the official result, so each column fills in when it exists. Next to each placing is where the dashboard had the
// runner (combined Rank), so a result reads as "what the table said vs what happened" without scanning the FP column.
export function RaceResult({ race, combo, scratched, onSelectRunner }: RaceResultProps) {
  const placed = race.runners
    .filter((r): r is Runner & { finishPosition: number } => r.finishPosition != null && !scratched.has(r.runId))
    .sort((a, b) => a.finishPosition - b.finishPosition)
    .slice(0, 4)
  if (placed.length === 0) return null

  const official = race.allResulted && !race.provisional
  const hasMargin = placed.some((r) => r.marginFinish != null)
  const hasSp = placed.some((r) => r.startingPrice != null)
  const winner = placed[0]
  const winnerRank = combo.get(winner.runId)?.rank ?? null
  const topPick = [...combo.entries()].filter(([, c]) => c.rank === 1).map(([id]) => race.runners.find((r) => r.runId === id)).filter((r): r is Runner => r != null)
  const topPickResult = topPick.length === 0 ? null : topPick.map((r) => (r.finishPosition != null ? `${r.horse} ${ORDINAL[r.finishPosition] ?? `${r.finishPosition}th`}` : `${r.horse} unplaced`)).join(', ')

  return (
    <section className="rounded-lg border border-line bg-panel px-3 py-2.5 shadow-[var(--shadow-1)] sm:px-4" aria-label="Race result">
      <div className="mb-1.5 flex items-center justify-between gap-2">
        <h3 className="text-sm font-semibold text-ink">Result</h3>
        <span className="text-[11px] text-ink-faint">{official ? 'Official' : 'Provisional, from TAB'}</span>
      </div>
      <ol className="flex flex-col divide-y divide-line-soft">
        {placed.map((r) => {
          const c = combo.get(r.runId)
          const price = r.startingPrice ?? r.fixedWinPrice
          return (
            <li key={r.runId}>
              <button type="button" onClick={() => onSelectRunner(r.runId)} className="grid w-full grid-cols-[22px_22px_minmax(0,1fr)_auto] items-center gap-x-2 py-1 text-left text-sm hover:bg-bg sm:py-1.5 sm:grid-cols-[22px_28px_minmax(0,1fr)_auto]">
                <FinishBadge pos={r.finishPosition} />
                <span className="font-mono text-ink-mute">{r.tabNumber}</span>
                <span className="min-w-0">
                  <span className={`block truncate ${r.finishPosition === 1 ? 'font-semibold' : 'font-medium'} text-ink`}>{r.horse}</span>
                  <span className="hidden truncate text-[11px] text-ink-faint sm:block">
                    {r.jockey} / {r.trainer}
                  </span>
                </span>
                <span className="flex items-baseline gap-3 font-mono text-xs text-ink-mute">
                  {hasMargin && <span title="Margin to the horse in front (lengths)">{r.finishPosition === 1 ? '' : r.marginFinish != null ? `${Math.abs(r.marginFinish).toFixed(1)}L` : ''}</span>}
                  <span title={r.startingPrice != null ? 'Starting price' : 'Last fixed price (starting price not in yet)'}>
                    {price != null ? fmtPrice(price) : ''}
                    {price != null && !hasSp ? <span className="ml-0.5 text-[9px] text-ink-faint">fx</span> : null}
                  </span>
                  <span className="w-14 text-right" title="Combined rank before the race">
                    {c ? <>Rank {c.tied ? '=' : ''}{c.rank}</> : ''}
                  </span>
                </span>
              </button>
            </li>
          )
        })}
      </ol>
      {(winnerRank != null || topPickResult) && (
        <p className="mt-1.5 border-t border-line-soft pt-1.5 text-xs text-ink-mute">
          {winnerRank != null && (
            <>
              Winner was Rank {winnerRank}
              {topPickResult ? '. ' : '.'}
            </>
          )}
          {topPickResult && <>Rank 1: {topPickResult}.</>}
        </p>
      )}
    </section>
  )
}
