import type { Runner } from '../../types/domain'
import type { EffectiveRunner } from '../../lib/raceModel'
import { fmtPrice, fmtWpr } from '../../lib/format'
import { lastRunsRating } from '../../lib/formRatings'
import { fmtBias, hasRunnerBias, runnerBias } from '../../lib/bias'
import { FinishBadge, PriceCell, useRowFacts } from './rowParts'
import type { CombinedRank } from '../../lib/combinedRank'

interface RunnerRowProps {
  runner: Runner
  raceDate: string
  selected: boolean
  effective?: EffectiveRunner
  showFp: boolean
  // Bias chip only once enough earlier races have run at the meeting (lib/bias MIN_BIAS_RACES).
  showBias?: boolean
  combo?: CombinedRank
  onClick: () => void
}

// Table row, same columns on every screen: Spd | Nett | L3 | Proj (whole numbers) | Rank, then Fixed $ and FP. Below lg the RTS column drops out (its track collapses to
// nothing via `hidden`) so everything else fits a phone without sideways scrolling; RTS moves into the detail line instead.
// Speed figure (lengths vs par, 0 = par) shown as 100 + 2.15 points a length (within-race slope of rating on figure, 309,976 runs, 2016-2026).
const SPEED_POINTS_PER_LENGTH = 2.15
const speedOnWprScale = (lengths: number) => 100 + SPEED_POINTS_PER_LENGTH * lengths

// Strip under the rank: one square per signal (Spd, Nett, L3, Proj), darker green = better rank, outline-grey = no value.
const rankShade = (x: number | null) => (x == null ? '#e5e7eb' : x === 1 ? '#047857' : x === 2 ? '#34d399' : x === 3 ? '#a7f3d0' : '#d1d5db')

const DESKTOP_GRID = 'lg:grid-cols-[40px_28px_minmax(190px,1fr)_44px_40px_40px_40px_40px_62px_84px_30px]'
// The FP column only takes room on a phone once there is a result to show.
export const rowGrid = (showFp: boolean) =>
  // Phone: [silk] | # | Horse | Spd | Nett | L3 | Proj | Rank | Fixed $ (| FP), everything on screen at once. The silk column joins from 380px up.
  // (Full class names on purpose: Tailwind only generates classes it can read literally.)
  `${
    showFp
      ? 'grid-cols-[16px_minmax(0,1fr)_28px_24px_24px_26px_44px_60px_18px] min-[380px]:grid-cols-[24px_16px_minmax(0,1fr)_28px_24px_24px_26px_44px_60px_18px]'
      : 'grid-cols-[16px_minmax(0,1fr)_28px_24px_24px_26px_44px_60px] min-[380px]:grid-cols-[24px_16px_minmax(0,1fr)_28px_24px_24px_26px_44px_60px]'
  } ${DESKTOP_GRID}`
const LG_ONLY = 'hidden lg:block'

export function RunnerRow({ runner, raceDate, selected, effective, showFp, showBias = true, combo, onClick }: RunnerRowProps) {
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
      className={`group grid min-w-full cursor-pointer items-center gap-x-1 border-b border-l-4 border-l-transparent border-line-soft px-2 py-1 text-left text-sm lg:gap-x-2 transition-colors ${rowGrid(showFp)} ${
        f.scratched ? 'opacity-50' : selected ? 'bg-emerald-bg' : 'hover:bg-bg'
      }`}
    >
      {runner.silkUrl ? <img src={runner.silkUrl} alt="" className="hidden h-6 w-6 rounded-sm object-contain min-[380px]:block lg:h-8 lg:w-8" /> : <span className="hidden h-6 w-6 min-[380px]:block lg:h-8 lg:w-8" />}
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
        <span className="flex min-w-0 items-baseline gap-1 text-[11px] leading-snug text-ink-faint" title={`${runner.jockey} / ${runner.trainer}`}>
          <span className={`flex-none font-mono lg:hidden ${f.rtsClass}`}>{f.spell.label}</span>
          {runner.barrier != null && (
            <span className="flex-none rounded border border-line px-1 font-mono text-[9px] leading-[14px] text-ink-mute lg:hidden" title={`Barrier ${runner.barrier}`}>
              B{runner.barrier}
            </span>
          )}
          <span className="max-w-[65%] flex-none truncate text-ink-mute">{runner.jockey}</span>
          <span className="min-w-0 truncate">/ {runner.trainer}{runner.barrier != null && <span className="hidden lg:inline"> &middot; barrier {runner.barrier}</span>}</span>
        </span>
      </span>
      <span className={`text-right font-mono ${f.rtsClass} ${LG_ONLY}`} title={f.rtsTitle}>
        {f.spell.label}
      </span>
      <span
        className="text-right font-mono text-[12px] text-ink-mute lg:text-[13px]"
        title={runner.speedRating != null ? `Speed rating ${speedOnWprScale(runner.speedRating).toFixed(1)} (${runner.speedRating.toFixed(1)} lengths against par; 100 = par, higher is faster, about 2 points a length): recency-weighted mean of the horse's earlier time-based figures` : undefined}
      >
        {f.scratched || runner.speedRating == null ? '' : Math.round(speedOnWprScale(runner.speedRating))}
      </span>
      <span className="text-right font-mono text-[12px] text-ink-mute lg:text-[13px]" title="TopRate's own forward rating (wpr_nett)">
        {f.scratched || runner.nett == null ? '' : Math.round(runner.nett)}
      </span>
      <span className="text-right font-mono leading-tight" title={l3 ? `Last 3 rated runs${l3.n < 3 ? ` (only ${l3.n} available)` : ''}: average ${fmtWpr(l3.avg)}, median ${fmtWpr(l3.median)}` : undefined}>
        {l3 ? (
          <>
            <span className="block text-[12px] text-ink-mute lg:text-[13px]">{Math.round(l3.avg)}</span>
            <span className="hidden text-[10px] text-ink-faint lg:block">{Math.round(l3.median)}</span>
          </>
        ) : null}
      </span>
      <span className="text-right">
        {f.scratched ? (
          <span className="font-mono text-ink-faint">SCR</span>
        ) : (
          <span title={`Rating ${fmtWpr(f.proj)}, set from the simulated win chance. Rated price ${fmtPrice(effective?.effectivePrice ?? null)}${effective?.effectivePlacePrice != null ? `, place ${fmtPrice(effective.effectivePlacePrice)}` : ''} (model view only, not a value claim). WPR projection ${fmtWpr(effective?.projectionWpr ?? null)}${f.atwOff !== 0 ? ` at ${runner.weightCarried != null ? runner.weightCarried + 'kg' : "today's weight"}` : ''}${sd != null ? ` ± ${Math.round(sd)}` : ''}${runner.projectionModel === 'light' ? ' (light-history model)' : ''}`}>
            <span className="font-mono text-[12px] text-ink-mute lg:text-[13px]">{f.proj == null ? null : Math.round(f.proj)}</span>
            {f.overridden && <span className="ml-0.5 text-amber" title="Manually adjusted">*</span>}
          </span>
        )}
      </span>
      <span
        className="text-right font-mono leading-tight"
        title={combo ? `Combined rank ${combo.rank} (mean ${combo.mean.toFixed(1)}): Spd ${combo.ranks[0] ?? '-'}, Nett ${combo.ranks[1] ?? '-'}, L3 ${combo.ranks[2] ?? '-'}, Proj ${combo.ranks[3] ?? '-'}` : undefined}
      >
        {f.scratched || !combo ? null : (
          <>
            <span
              className={`inline-block min-w-[18px] rounded px-1 text-center text-[12px] lg:text-[13px] ${
                combo.rank === 1 ? 'bg-emerald font-medium text-white' : combo.rank <= 3 ? 'bg-emerald-bg text-emerald-deep' : 'text-ink'
              }`}
            >
              {combo.rank}
            </span>
            <span className="mt-[2px] flex justify-end gap-[2px]" aria-hidden="true">
              {combo.ranks.map((x, i) => (
                <span key={i} className="h-[5px] w-[5px] rounded-[1px] lg:h-[6px] lg:w-[6px]" style={{ background: rankShade(x) }} />
              ))}
            </span>
          </>
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
