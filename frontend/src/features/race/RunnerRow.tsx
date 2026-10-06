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
  barFrac: number | null // 0..1 position of the projection between the field's lowest and highest
  onClick: () => void
}

// Desktop table row (lg and up). Phones and tablets use RunnerCard instead, so nothing here has to squeeze into a narrow screen.
export const ROW_GRID = 'grid-cols-[36px_28px_minmax(190px,1fr)_44px_52px_52px_100px_50px_46px_46px_52px_84px_30px]'

export function RunnerRow({ runner, raceDate, selected, effective, band, barFrac, onClick }: RunnerRowProps) {
  const f = useRowFacts(runner, raceDate, effective)
  const sd = runner.projectionSd
  const overlayPct =
    effective?.isOverlay && runner.fixedWinPrice != null && effective.effectivePrice != null
      ? Math.round((runner.fixedWinPrice / effective.effectivePrice - 1) * 100)
      : null
  const barTone = band === 'inner' ? 'bg-emerald' : band === 'outer' ? 'bg-amber' : 'bg-line'
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
      className={`group grid min-w-full cursor-pointer items-center gap-x-2 border-b border-l-4 border-line-soft px-2 py-2 text-left text-sm transition-colors ${ROW_GRID} ${BAND_BORDER[band]} ${
        f.scratched ? 'opacity-50' : selected ? 'bg-emerald-bg' : 'hover:bg-bg'
      }`}
    >
      {runner.silkUrl ? <img src={runner.silkUrl} alt="" className="h-8 w-8 rounded-sm object-contain" /> : <span className="h-8 w-8" />}
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
          {effective?.isOverlay && !f.scratched && !effective.driftedToOverlay && (
            <span className="flex-none rounded bg-emerald-bg px-1 text-[10px] font-semibold text-emerald-deep" title="Market price vs the model's fair price">
              OVERLAY{overlayPct != null ? ` +${overlayPct}%` : ''}
            </span>
          )}
          {effective?.driftedToOverlay && !f.scratched && <span className="flex-none text-[10px] font-semibold text-amber">DRIFTED</span>}
        </span>
        <span className="block truncate text-xs text-ink-faint">
          {runner.jockey}
          {ratingSuffix(runner.jockeyRating)} / {runner.trainer}
          {ratingSuffix(runner.trainerRating)}
        </span>
        <span className="block truncate text-xs text-ink-mute">
          {[
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
            <span className="font-mono text-base font-semibold text-emerald-deep">{fmtWpr(f.proj)}</span>
            {f.overridden && <span className="ml-0.5 text-amber" title="Manually adjusted">*</span>}
            {barFrac != null && (
              <span className="mt-1 block h-1 w-full overflow-hidden rounded-full bg-line-soft">
                <span className={`block h-full rounded-full ${barTone}`} style={{ width: `${Math.max(6, barFrac * 100)}%` }} />
              </span>
            )}
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
