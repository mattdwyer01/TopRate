import type { Runner } from '../../types/domain'
import type { EffectiveRunner } from '../../lib/raceModel'
import { fmtInt, fmtWpr } from '../../lib/format'
import { spellWord, adjClass, BAND_BORDER, fmtAdj, FinishBadge, PriceCell, ratingSuffix, smClass, useRowFacts } from './rowParts'

interface RunnerRowProps {
  runner: Runner
  raceDate: string
  selected: boolean
  effective?: EffectiveRunner
  band: 'inner' | 'outer' | 'none'
  onClick: () => void
}

// Desktop table row (lg and up). Phones and tablets use RunnerCard instead, so nothing here has to squeeze into a narrow screen.
export const ROW_GRID = 'grid-cols-[36px_28px_minmax(190px,1fr)_44px_52px_52px_100px_50px_46px_46px_52px_84px_30px]'

export function RunnerRow({ runner, raceDate, selected, effective, band, onClick }: RunnerRowProps) {
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
      className={`group grid min-w-full cursor-pointer items-center gap-x-2 border-b border-l-4 border-line-soft px-2 py-1 text-left text-sm transition-colors ${ROW_GRID} ${BAND_BORDER[band]} ${
        f.scratched ? 'opacity-50' : selected ? 'bg-emerald-bg' : 'hover:bg-bg'
      }`}
    >
      {runner.silkUrl ? <img src={runner.silkUrl} alt="" className="h-6 w-6 rounded-sm object-contain" /> : <span className="h-6 w-6" />}
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
          {[
            `${runner.jockey} / ${runner.trainer}`,
            runner.barrier != null ? `barrier ${runner.barrier}` : null,
            runner.weightCarried != null ? `${runner.weightCarried}kg` : null,
            f.spell.daysSince != null || f.spell.label === 'FS' ? spellWord(f.spell.label) : null,
            runner.predictedSettlingBand ? runner.predictedSettlingBand.toLowerCase() : null,
          ]
            .filter(Boolean)
            .join(' · ')}
        </span>
      </span>
      <span className={`text-right font-mono ${f.rtsClass}`} title={f.rtsTitle}>
        {f.spell.label}
      </span>
      <span className="text-right font-mono text-ink-mute">{fmtWpr(runner.baseWpr)}</span>
      <span className={`text-right font-mono ${adjClass(runner.wprAdjustment)}`}>{fmtAdj(runner.wprAdjustment)}</span>
      <span className="text-right">
        {f.scratched ? (
          <span className="font-mono font-semibold text-ink-faint">SCR</span>
        ) : (
          <span title={`Projected WPR ${fmtWpr(f.proj)}${sd != null ? ` ± ${Math.round(sd)}` : ''}${runner.projectionModel === 'light' ? ' (light-history model)' : ''}`}>
            <span className="font-mono text-[15px] font-semibold leading-tight text-emerald-deep">{fmtWpr(f.proj)}</span>
            {f.overridden && <span className="ml-0.5 text-amber" title="Manually adjusted">*</span>}
          </span>
        )}
      </span>
      <span className="text-right font-mono text-ink-mute">{f.scratched ? '' : fmtInt(runner.toprateRating)}</span>
      <span className="text-right font-mono text-ink-mute">{f.scratched ? '' : fmtInt(runner.wprNett)}</span>
      <span className="text-right font-mono text-ink-mute">{f.scratched ? '' : fmtInt(runner.formFactor)}</span>
      <span className={`text-right font-mono ${smClass(effective?.speedMapAdj)}`}>{f.scratched ? '' : fmtAdj(effective?.speedMapAdj)}</span>
      <span className="text-right text-ink-mute">
        <PriceCell runner={runner} scratched={f.scratched} move={f.move} showMove={f.showMove} />
      </span>
      <span className="text-right">
        <FinishBadge pos={runner.finishPosition} />
      </span>
    </div>
  )
}
