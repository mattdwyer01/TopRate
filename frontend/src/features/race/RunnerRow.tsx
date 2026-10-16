import type { Runner } from '../../types/domain'
import type { EffectiveRunner } from '../../lib/raceModel'
import { fmtPrice, fmtWpr } from '../../lib/format'
import { lastRunsRating } from '../../lib/formRatings'
import { fmtBias, hasRunnerBias, runnerBias } from '../../lib/bias'
import { BAND_BORDER, FinishBadge, PriceCell, useRowFacts } from './rowParts'
import type { CombinedRank } from '../../lib/combinedRank'

interface RunnerRowProps {
  runner: Runner
  raceDate: string
  selected: boolean
  effective?: EffectiveRunner
  band: 'core' | 'inner' | 'outer' | 'none'
  showFp: boolean
  // Bias chip only once enough earlier races have run at the meeting (lib/bias MIN_BIAS_RACES).
  showBias?: boolean
  combo?: CombinedRank
  onClick: () => void
}

// Table row, same columns on every screen. Below lg the RTS column drops out (their tracks collapse to nothing via
// `hidden`) so Horse, Proj, SM, Rated $, Fixed $ and FP fit a phone without sideways scrolling; RTS moves into the detail line instead.
const DESKTOP_GRID = 'lg:grid-cols-[36px_28px_minmax(190px,1fr)_44px_46px_46px_52px_58px_84px_30px]'
// The FP column only takes room on a phone once there is a result to show.
export const rowGrid = (showFp: boolean) =>
  // Phone: [silk] | # | Horse | Nett | L3 | Rank | Proj | Fixed $ (| FP), everything on screen at once. The silk column joins from 380px up.
  // (Full class names on purpose: Tailwind only generates classes it can read literally.)
  `${
    showFp
      ? 'grid-cols-[16px_minmax(0,1fr)_30px_30px_28px_36px_60px_20px] min-[380px]:grid-cols-[18px_16px_minmax(0,1fr)_30px_30px_28px_36px_60px_20px]'
      : 'grid-cols-[16px_minmax(0,1fr)_30px_30px_28px_36px_60px] min-[380px]:grid-cols-[18px_16px_minmax(0,1fr)_30px_30px_28px_36px_60px]'
  } ${DESKTOP_GRID}`
const LG_ONLY = 'hidden lg:block'

export function RunnerRow({ runner, raceDate, selected, effective, band, showFp, showBias = true, combo, onClick }: RunnerRowProps) {
  const f = useRowFacts(runner, raceDate, effective)
  const sd = runner.projectionSd
  const l3 = f.scratched ? null : lastRunsRating(runner.formHistory, raceDate, 3)
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
      className={`group grid min-w-full cursor-pointer items-center gap-x-1 border-b border-l-4 border-line-soft px-2 py-1 text-left text-sm lg:gap-x-2 transition-colors ${rowGrid(showFp)} ${BAND_BORDER[band]} ${
        f.scratched ? 'opacity-50' : selected ? 'bg-emerald-bg' : 'hover:bg-bg'
      }`}
    >
      {runner.silkUrl ? <img src={runner.silkUrl} alt="" className="hidden h-[18px] w-[18px] rounded-sm object-contain min-[380px]:block lg:h-6 lg:w-6" /> : <span className="hidden h-[18px] w-[18px] min-[380px]:block lg:h-6 lg:w-6" />}
      <span className="font-mono text-ink-mute">{runner.tabNumber}</span>
      <span className="min-w-0">
        <span className="flex items-center gap-1.5">
          <span className={`truncate font-medium text-ink ${f.scratched ? 'line-through' : ''}`}>{runner.horse}</span>
          {runner.dataScratched && <span className="flex-none rounded bg-rose px-1 text-[10px] font-semibold text-white">SCR</span>}
          {showBias && hasRunnerBias(runner) && !f.scratched && (
            <span
              className={`flex-none rounded border px-1 font-mono text-[10px] font-semibold ${runnerBias(runner) >= 0 ? 'border-emerald-line bg-emerald-bg text-emerald-deep' : 'border-rose-line bg-rose-bg text-rose'}`}
              title="Moved by the track bias read from earlier races at this meeting (already inside the WPR projection and SM)"
            >
              <span className="lg:hidden">{runnerBias(runner) >= 0 ? '\u25B2' : '\u25BC'}{Math.abs(runnerBias(runner)).toFixed(1)}</span>
              <span className="hidden lg:inline">bias {fmtBias(runnerBias(runner))}</span>
            </span>
          )}
          {runner.projectionModel === 'light' && !f.scratched && (
            <span className="hidden flex-none rounded border border-line px-1 text-[10px] text-ink-faint lg:inline" title="Light-history model (0-2 prior runs): wider error">
              light
            </span>
          )}
        </span>
        <span className="block truncate text-[11px] leading-snug text-ink-faint" title={`${runner.jockey} / ${runner.trainer}`}>
          <span className={`font-mono lg:hidden ${f.rtsClass}`}>{f.spell.label} · </span>
          {runner.jockey} / {runner.trainer}
          {runner.barrier != null && <> &middot; barrier {runner.barrier}</>}
        </span>
      </span>
      <span className={`text-right font-mono ${f.rtsClass} ${LG_ONLY}`} title={f.rtsTitle}>
        {f.spell.label}
      </span>
      <span className="text-right font-mono text-[12px] font-semibold text-ink lg:text-[14px]" title="TopRate's own forward rating (wpr_nett)">
        {f.scratched || runner.nett == null ? '' : fmtWpr(runner.nett)}
      </span>
      <span className="text-right font-mono leading-tight" title={l3 ? `Last 3 rated runs${l3.n < 3 ? ` (only ${l3.n} available)` : ''}: average ${fmtWpr(l3.avg)}, median ${fmtWpr(l3.median)}` : undefined}>
        {l3 ? (
          <>
            <span className="block text-[12px] text-ink-mute">{fmtWpr(l3.avg)}</span>
            <span className="hidden text-[10px] text-ink-faint lg:block">{fmtWpr(l3.median)}</span>
          </>
        ) : null}
      </span>
      <span
        className="text-right font-mono leading-tight"
        title={combo ? `Combined rank ${combo.rank}: Proj ${combo.ranks[0] ?? '-'}, Nett ${combo.ranks[1] ?? '-'}, L3 ${combo.ranks[2] ?? '-'} (mean ${combo.mean.toFixed(1)})` : undefined}
      >
        {f.scratched || !combo ? null : (
          <>
            <span className="block text-[13px] font-semibold text-ink">{combo.rank}</span>
            <span className="hidden text-[10px] text-ink-faint lg:block">{combo.ranks.map((x) => x ?? '-').join('\u00b7')}</span>
          </>
        )}
      </span>
      <span className="text-right">
        {f.scratched ? (
          <span className="font-mono font-semibold text-ink-faint">SCR</span>
        ) : (
          <span title={`Rating ${fmtWpr(f.proj)}, set from the simulated win chance. Rated price ${fmtPrice(effective?.effectivePrice ?? null)}${effective?.effectivePlacePrice != null ? `, place ${fmtPrice(effective.effectivePlacePrice)}` : ''} (model view only, not a value claim). WPR projection ${fmtWpr(effective?.projectionWpr ?? null)}${f.atwOff !== 0 ? ` at ${runner.weightCarried != null ? runner.weightCarried + 'kg' : "today's weight"}` : ''}${sd != null ? ` ± ${Math.round(sd)}` : ''}${runner.projectionModel === 'light' ? ' (light-history model)' : ''}`}>
            <span className="font-mono text-sm font-semibold leading-tight lg:text-[15px] text-emerald-deep">{fmtWpr(f.proj)}</span>
            {f.overridden && <span className="ml-0.5 text-amber" title="Manually adjusted">*</span>}
          </span>
        )}
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
