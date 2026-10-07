import type { Runner } from '../../types/domain'
import type { EffectiveRunner } from '../../lib/raceModel'
import { fmtInt, fmtWpr } from '../../lib/format'
import { adjClass, BAND_BORDER, fmtAdj, FinishBadge, PriceCell, smClass, useRowFacts } from './rowParts'

interface RunnerCardProps {
  runner: Runner
  raceDate: string
  selected: boolean
  effective?: EffectiveRunner
  band: 'inner' | 'outer' | 'none'
  onClick: () => void
}

function Kv({ k, v, className = 'text-ink-soft' }: { k: string; v: string; className?: string }) {
  return (
    <span className="whitespace-nowrap">
      <span className="text-ink-faint">{k} </span>
      <span className={`font-mono font-medium ${className}`}>{v}</span>
    </span>
  )
}

// Phone and tablet card for one runner, kept to three short lines: name with projection and price, then connections, then the small stats
// on one line. Nothing scrolls sideways.
export function RunnerCard({ runner, raceDate, selected, effective, band, onClick }: RunnerCardProps) {
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
      className={`flex cursor-pointer gap-2 overflow-hidden rounded-lg border border-l-4 border-line bg-panel px-2.5 py-1.5 text-left transition-colors ${BAND_BORDER[band]} ${
        f.scratched ? 'opacity-50' : selected ? 'bg-emerald-bg' : 'hover:bg-bg'
      }`}
    >
      {runner.silkUrl ? <img src={runner.silkUrl} alt="" className="mt-0.5 h-7 w-7 flex-none rounded-sm object-contain" /> : <span className="h-7 w-7 flex-none" />}
      <div className="min-w-0 flex-1">
        <div className="flex items-center gap-1.5">
          <span className="font-mono text-xs text-ink-mute">{runner.tabNumber}.</span>
          <span className={`truncate text-[15px] font-semibold leading-tight text-ink ${f.scratched ? 'line-through' : ''}`}>{runner.horse}</span>
          {runner.dataScratched && <span className="flex-none rounded bg-rose px-1 text-[10px] font-semibold text-white">SCR</span>}
          {runner.projectionModel === 'light' && !f.scratched && (
            <span className="flex-none rounded border border-line px-1 text-[9px] leading-4 text-ink-faint" title="Light-history model: wider error">
              light
            </span>
          )}
        </div>
        <div className="truncate text-[11px] leading-snug text-ink-faint">
          {runner.jockey} / {runner.trainer}
        </div>
        <div className="mt-0.5 flex items-center gap-x-2 overflow-hidden whitespace-nowrap text-[11px] leading-snug">
          <span className={`font-mono font-semibold ${f.rtsClass}`} title={f.rtsTitle}>
            {f.spell.label}
          </span>
          {runner.barrier != null && (
            <>
              <Kv k="Bar" v={String(runner.barrier)} />
            </>
          )}
          {runner.wprAdjustment != null && (
            <>
              <Kv k="Adj" v={fmtAdj(runner.wprAdjustment)} className={adjClass(runner.wprAdjustment)} />
            </>
          )}
          {effective?.speedMapAdj != null && (
            <>
              <Kv k="SM" v={fmtAdj(effective.speedMapAdj)} className={smClass(effective.speedMapAdj)} />
            </>
          )}
          {runner.toprateRating != null && (
            <>
              <Kv k="TR" v={fmtInt(runner.toprateRating)} />
            </>
          )}
          {runner.formFactor != null && (
            <span className="max-[379px]:hidden">
              <Kv k="F" v={fmtInt(runner.formFactor)} />
            </span>
          )}
        </div>
      </div>
      <div className="flex flex-none items-start gap-1.5">
        <div className="text-right" title={sd != null ? `Typical error about ${Math.round(sd)}` : undefined}>
          {f.scratched ? (
            <div className="font-mono text-base font-semibold text-ink-faint">SCR</div>
          ) : (
            <>
              <div className="font-mono text-xl font-semibold leading-none text-emerald-deep">
                {fmtWpr(f.proj)}
                {f.overridden && <span className="text-amber">*</span>}
              </div>
              <div className="mt-1 text-[13px] leading-none text-ink-soft">
                <PriceCell runner={runner} scratched={false} move={f.move} showMove={f.showMove} />
              </div>
            </>
          )}
        </div>
        {runner.finishPosition != null && (
          <div className="w-5 flex-none text-right">
            <FinishBadge pos={runner.finishPosition} />
          </div>
        )}
      </div>
    </div>
  )
}
