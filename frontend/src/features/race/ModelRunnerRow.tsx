import { fmtInt, fmtPrice, fmtWpr } from '../../lib/format'
import { spellPosition } from '../../lib/spellPosition'
import { MODEL_GRID, type ModelRow } from '../../lib/modelTable'

// Racing Model view of the ratings table (RaceDetail's "Racing Model" source, see lib/racingModel.ts):
// same row shape and styling as RunnerRow (silk and name pinned on mobile, jockey / trainer line in Full,
// mono figures, the headline figure bold emerald) with the Racing Model's columns in place of TopRate's
// (lib/modelTable.ts).

function signed(v: number | null | undefined): string {
  if (v == null) return '—'
  const f = v.toFixed(1)
  return v > 0 ? `+${f}` : f
}

function tone(v: number | null | undefined, threshold = 0): string {
  if (v == null) return 'text-ink-mute'
  if (v > threshold) return 'text-emerald-deep'
  if (v < -threshold) return 'text-rose'
  return 'text-ink-mute'
}

interface ModelRunnerRowProps {
  row: ModelRow
  raceDate: string
  compact: boolean
  selected: boolean
  scratched: boolean
  onClick: () => void
}

export function ModelRunnerRow({ row, raceDate, compact, selected, scratched, onClick }: ModelRunnerRowProps) {
  const { runner, m, b, settleRank } = row
  const rowPadding = compact ? 'py-1.5' : 'py-2.5'
  const spell = spellPosition(runner.formHistory, raceDate)
  const rtsColorClass =
    spell.label === 'FU' ? 'font-semibold text-amber' : spell.label === 'FS' ? 'font-semibold text-indigo' : 'text-ink-mute'
  const stickyBg = selected ? 'bg-emerald-bg' : 'bg-panel group-hover:bg-bg'
  const edge = scratched ? null : (b?.edge ?? null)
  const dash = (v: string) => (scratched ? 'SCR' : v)
  const onlyFull = compact ? 'hidden sm:inline' : ''

  return (
    <div
      role="button"
      tabIndex={0}
      onClick={onClick}
      onKeyDown={(e) => {
        if (e.key === 'Enter' || e.key === ' ') {
          e.preventDefault()
          onClick()
        }
      }}
      title={edge != null && edge > 0 ? 'Value: the blend price is shorter than the fixed price' : undefined}
      className={`group grid min-w-full cursor-pointer items-center gap-y-0.5 border-b border-line-soft px-2 text-left text-sm transition-colors sm:gap-x-2 ${
        MODEL_GRID.desktop
      } ${compact ? MODEL_GRID.compact : `${MODEL_GRID.full} max-sm:text-xs`} ${rowPadding} ${
        scratched ? 'opacity-50' : selected ? 'bg-emerald-bg' : 'hover:bg-bg'
      }`}
    >
      <span className={`sticky left-0 z-10 -ml-2 pl-2 sm:static sm:z-auto sm:m-0 sm:p-0 ${stickyBg}`}>
        {runner.silkUrl ? (
          <img src={runner.silkUrl} alt="" className="h-9 w-9 flex-none rounded-sm object-contain" />
        ) : (
          <span className="block h-9 w-9 flex-none sm:h-auto sm:w-auto" />
        )}
      </span>
      <span className="hidden font-mono text-ink-mute sm:inline">{runner.tabNumber}</span>
      <span className={`sticky left-12 z-10 min-w-0 sm:static sm:z-auto ${stickyBg}`}>
        <span className="flex items-center gap-1">
          <span className={`truncate font-medium text-ink ${scratched ? 'line-through' : ''}`}>
            <span className="font-mono text-ink-mute sm:hidden">{runner.tabNumber}. </span>
            {runner.horse}
          </span>
          <span className="hidden flex-none font-mono text-[11px] text-ink-faint sm:inline">({runner.barrier ?? '-'})</span>
          {!scratched && m?.pf === 1 && (
            <span className="flex-none text-[11px] text-indigo" title="Position value in the top 10%">
              ◆
            </span>
          )}
        </span>
        {!compact && (
          <span className="block truncate text-xs text-ink-faint">
            <span className="sm:hidden">
              <span className={`font-mono ${rtsColorClass}`}>{spell.label}</span>
              {` · b${runner.barrier ?? '-'} · `}
            </span>
            {runner.jockey} / {runner.trainer}
          </span>
        )}
      </span>
      <span className={`hidden text-right font-mono sm:inline ${rtsColorClass}`}>{spell.label}</span>
      <span className="text-right font-mono font-semibold text-emerald-deep">{dash(fmtWpr(m?.r))}</span>
      <span className={`hidden text-right font-mono sm:inline ${tone(m?.v)}`}>{dash(signed(m?.v))}</span>
      <span className={`text-right font-mono text-ink-mute ${onlyFull}`}>{dash(settleRank == null ? '—' : String(settleRank))}</span>
      <span className="hidden text-right font-mono text-ink-mute sm:inline">
        {dash(m?.l == null ? '—' : `${Math.round(m.l * 100)}%`)}
      </span>
      <span className={`text-right font-mono ${onlyFull} ${m?.pf ? 'font-semibold text-indigo' : tone(m?.pv, 0.5)}`}>
        {dash(signed(m?.pv))}
      </span>
      <span className="hidden text-right font-mono text-ink-mute sm:inline">{dash(fmtPrice(m?.p ? 1 / m.p : null))}</span>
      <span className="text-right font-mono text-ink">{dash(fmtPrice(b?.blendPrice))}</span>
      <span className="text-right font-mono text-ink-mute">{dash(fmtPrice(runner.fixedWinPrice))}</span>
      <span className={`text-right font-mono ${edge != null && edge > 0 ? 'font-semibold text-emerald-deep' : 'text-ink-faint'}`}>
        {edge == null ? (scratched ? 'SCR' : '—') : `${edge > 0 ? '+' : ''}${Math.round(edge * 100)}%`}
      </span>
      <span className="text-right">
        <span
          className={`inline-flex h-5 w-5 items-center justify-center rounded-full font-mono text-ink-mute ${
            runner.finishPosition === 1 ? 'border border-amber-line bg-amber-bg font-semibold text-amber' : ''
          }`}
        >
          {runner.finishPosition !== null ? fmtInt(runner.finishPosition) : ''}
        </span>
      </span>
    </div>
  )
}
