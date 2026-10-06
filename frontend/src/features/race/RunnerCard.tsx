import type { Runner } from '../../types/domain'
import type { EffectiveRunner } from '../../lib/raceModel'
import { fmtInt, fmtWpr } from '../../lib/format'
import { adjClass, BAND_BORDER, fmtAdj, FinishBadge, PriceCell, ratingSuffix, smClass, useRowFacts } from './rowParts'

interface RunnerCardProps {
  runner: Runner
  raceDate: string
  selected: boolean
  effective?: EffectiveRunner
  band: 'inner' | 'outer' | 'none'
  barFrac: number | null
  onClick: () => void
}

function Stat({ label, value, className = 'text-ink-soft' }: { label: string; value: string; className?: string }) {
  return (
    <span className="inline-flex items-baseline gap-1 rounded-md bg-bg px-1.5 py-0.5 text-[11px]">
      <span className="text-ink-faint">{label}</span>
      <span className={`font-mono font-medium ${className}`}>{value}</span>
    </span>
  )
}

// Phone and tablet card for one runner: the projection and price lead, everything else is a small labelled chip, nothing scrolls sideways.
export function RunnerCard({ runner, raceDate, selected, effective, band, barFrac, onClick }: RunnerCardProps) {
  const f = useRowFacts(runner, raceDate, effective)
  const sd = runner.projectionSd
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
      className={`flex cursor-pointer flex-col gap-1.5 rounded-lg border border-l-4 border-line bg-panel px-3 py-2.5 text-left transition-colors ${BAND_BORDER[band]} ${
        f.scratched ? 'opacity-50' : selected ? 'bg-emerald-bg' : 'hover:bg-bg'
      }`}
    >
      <div className="flex items-center gap-2.5">
        {runner.silkUrl ? <img src={runner.silkUrl} alt="" className="h-9 w-9 flex-none rounded-sm object-contain" /> : <span className="h-9 w-9 flex-none" />}
        <div className="min-w-0 flex-1">
          <div className="flex items-center gap-1.5">
            <span className="font-mono text-sm text-ink-mute">{runner.tabNumber}.</span>
            <span className={`truncate font-semibold text-ink ${f.scratched ? 'line-through' : ''}`}>{runner.horse}</span>
            {runner.dataScratched && <span className="flex-none rounded bg-rose px-1 text-[10px] font-semibold text-white">SCR</span>}
          </div>
          <div className="truncate text-xs text-ink-faint">
            {runner.jockey}
            {ratingSuffix(runner.jockeyRating)} / {runner.trainer}
            {ratingSuffix(runner.trainerRating)}
          </div>
        </div>
        <div className="flex-none text-right">
          {f.scratched ? (
            <div className="font-mono text-lg font-semibold text-ink-faint">SCR</div>
          ) : (
            <>
              <div className="font-mono text-xl font-semibold leading-none text-emerald-deep">
                {fmtWpr(f.proj)}
                {f.overridden && <span className="text-amber">*</span>}
              </div>
              <div className="mt-0.5 text-[10px] text-ink-faint">{sd != null ? `±${Math.round(sd)}` : 'proj'}</div>
            </>
          )}
        </div>
        <div className="w-16 flex-none text-right text-sm text-ink-soft">
          <PriceCell runner={runner} scratched={f.scratched} move={f.move} showMove={f.showMove} />
        </div>
        <div className="w-5 flex-none text-right">
          <FinishBadge pos={runner.finishPosition} />
        </div>
      </div>
      {!f.scratched && barFrac != null && (
        <span className="block h-1 w-full overflow-hidden rounded-full bg-line-soft">
          <span className={`block h-full rounded-full ${barTone}`} style={{ width: `${Math.max(4, barFrac * 100)}%` }} />
        </span>
      )}
      <div className="flex flex-wrap items-center gap-1">
        <span className={`rounded-md bg-bg px-1.5 py-0.5 font-mono text-[11px] ${f.rtsClass}`} title={f.rtsTitle}>
          {f.spell.label}
        </span>
        {runner.barrier != null && <Stat label="Bar" value={String(runner.barrier)} />}
        {runner.wprAdjustment != null && <Stat label="Adj" value={fmtAdj(runner.wprAdjustment)} className={adjClass(runner.wprAdjustment)} />}
        {effective?.speedMapAdj != null && <Stat label="SM" value={fmtAdj(effective.speedMapAdj)} className={smClass(effective.speedMapAdj)} />}
        {runner.toprateRating != null && <Stat label="TR" value={fmtInt(runner.toprateRating)} />}
        {runner.formFactor != null && <Stat label="Form" value={fmtInt(runner.formFactor)} />}
        {runner.projectionModel === 'light' && <span className="rounded-md border border-line px-1.5 py-0.5 text-[11px] text-ink-faint">light model</span>}
        {effective?.isOverlay && !effective.driftedToOverlay && <span className="rounded-md bg-emerald-bg px-1.5 py-0.5 text-[11px] font-semibold text-emerald-deep">Overlay</span>}
        {effective?.driftedToOverlay && <span className="rounded-md bg-amber-bg px-1.5 py-0.5 text-[11px] font-semibold text-amber">Drifted</span>}
      </div>
    </div>
  )
}
