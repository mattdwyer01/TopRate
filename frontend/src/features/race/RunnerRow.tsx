import type { Runner } from '../../types/domain'
import type { EffectiveRunner } from '../../lib/raceModel'
import { fmtPrice, fmtWpr } from '../../lib/format'
import { adjClass, BAND_BORDER, fmtAdj, FinishBadge, PriceCell, ratingSuffix, smClass, useRowFacts } from './rowParts'

interface RunnerRowProps {
  runner: Runner
  raceDate: string
  selected: boolean
  effective?: EffectiveRunner
  band: 'inner' | 'outer' | 'none'
  showFp: boolean
  onClick: () => void
}

// Table row, same columns on every screen. Below lg the RTS, Base and Rated $ columns drop out (their tracks collapse to nothing via
// `hidden`) so Horse, Adj, Proj, SM, Fixed $ and FP fit a phone without sideways scrolling; RTS moves into the detail line instead.
const DESKTOP_GRID = 'lg:grid-cols-[36px_28px_minmax(190px,1fr)_44px_52px_52px_58px_52px_64px_84px_30px]'
// The FP column only takes room on a phone once there is a result to show.
export const rowGrid = (showFp: boolean) =>
  `${showFp ? 'grid-cols-[22px_16px_minmax(0,1fr)_28px_36px_28px_60px_20px]' : 'grid-cols-[22px_16px_minmax(0,1fr)_28px_36px_28px_60px]'} ${DESKTOP_GRID}`
const LG_ONLY = 'hidden lg:block'

export function RunnerRow({ runner, raceDate, selected, effective, band, showFp, onClick }: RunnerRowProps) {
  const f = useRowFacts(runner, raceDate, effective)
  const sd = runner.projectionSd
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
      title={f.marketNote}
      className={`group grid min-w-full cursor-pointer items-center gap-x-1.5 border-b border-l-4 border-line-soft px-2 py-1 text-left text-sm lg:gap-x-2 transition-colors ${rowGrid(showFp)} ${BAND_BORDER[band]} ${
        f.scratched ? 'opacity-50' : selected ? 'bg-emerald-bg' : 'hover:bg-bg'
      }`}
    >
      {runner.silkUrl ? <img src={runner.silkUrl} alt="" className="h-[22px] w-[22px] rounded-sm object-contain lg:h-6 lg:w-6" /> : <span className="h-6 w-6" />}
      <span className="font-mono text-ink-mute">{runner.tabNumber}</span>
      <span className="min-w-0">
        <span className="flex items-center gap-1.5">
          <span className={`truncate font-medium text-ink ${f.scratched ? 'line-through' : ''}`}>{runner.horse}</span>
          {runner.dataScratched && <span className="flex-none rounded bg-rose px-1 text-[10px] font-semibold text-white">SCR</span>}
          {runner.projectionModel === 'light' && !f.scratched && (
            <span className="flex-none rounded border border-line px-1 text-[10px] text-ink-faint" title="Light-history model (0-2 prior runs): wider error">
              light
            </span>
          )}
        </span>
        <span className="block truncate text-[11px] leading-snug text-ink-faint" title={`${runner.jockey}${ratingSuffix(runner.jockeyRating)} / ${runner.trainer}${ratingSuffix(runner.trainerRating)}`}>
          <span className={`font-mono lg:hidden ${f.rtsClass}`}>{f.spell.label} · </span>
          {runner.jockey} / {runner.trainer}
          {runner.barrier != null && <> &middot; barrier {runner.barrier}</>}
        </span>
      </span>
      <span className={`text-right font-mono ${f.rtsClass} ${LG_ONLY}`} title={f.rtsTitle}>
        {f.spell.label}
      </span>
      <span className={`text-right font-mono text-ink-mute ${LG_ONLY}`}>{fmtWpr(runner.baseWpr)}</span>
      <span className={`text-right font-mono ${adjClass(runner.wprAdjustment)}`}>{fmtAdj(runner.wprAdjustment)}</span>
      <span className="text-right">
        {f.scratched ? (
          <span className="font-mono font-semibold text-ink-faint">SCR</span>
        ) : (
          <span title={`Projected WPR ${fmtWpr(f.proj)}${sd != null ? ` ± ${Math.round(sd)}` : ''}${runner.projectionModel === 'light' ? ' (light-history model)' : ''}`}>
            <span className="font-mono text-sm font-semibold leading-tight lg:text-[15px] text-emerald-deep">{fmtWpr(f.proj)}</span>
            {f.overridden && <span className="ml-0.5 text-amber" title="Manually adjusted">*</span>}
          </span>
        )}
      </span>
      <span className={`text-right font-mono ${smClass(effective?.speedMapAdj)}`}>{f.scratched ? '' : fmtAdj(effective?.speedMapAdj)}</span>
      <span className={`text-right font-mono text-ink-mute ${LG_ONLY}`} title="Fair price from the projection (softmax over the field)">
        {f.scratched ? '' : fmtPrice(effective?.effectivePrice ?? runner.wprPrice)}
      </span>
      <span className="text-right text-ink-mute">
        <PriceCell runner={runner} scratched={f.scratched} move={f.move} showMove={f.showMove} />
      </span>
      <span className={`text-right ${showFp ? '' : LG_ONLY}`}>
        <FinishBadge pos={runner.finishPosition} />
      </span>
    </div>
  )
}
