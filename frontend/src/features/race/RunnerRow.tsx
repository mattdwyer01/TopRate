import type { Runner } from '../../types/domain'
import type { EffectiveRunner } from '../../lib/raceModel'
import { fmtPrice } from '../../lib/format'
import { fmtBias, hasRunnerBias, runnerBias } from '../../lib/bias'
import { FinishBadge, PriceCell, useRowFacts } from './rowParts'
import type { CombinedRank } from '../../lib/combinedRank'
import { speedRatingOnScale } from '../../lib/speed'

interface RunnerRowProps {
  runner: Runner
  raceDate: string
  selected: boolean
  effective?: EffectiveRunner
  showFp: boolean
  // False before any price is out: the Fixed $ cell drops out on phones (desktop keeps the column).
  showPrice?: boolean
  // Bias chip only once enough earlier races have run at the meeting (lib/bias MIN_BIAS_RACES).
  showBias?: boolean
  combo?: CombinedRank
  // Lowest and highest Proj in the field, for the bar under the Proj figure (desktop).
  onClick: () => void
}

// Table row, same columns on every screen: Peak | Base | Spd | Rating (whole numbers), then Fixed $ and FP. Below lg the RTS column drops out (its track collapses to
// nothing via `hidden`) so everything else fits a phone without sideways scrolling; RTS moves into the detail line instead.

// Strip under the rank: one square per signal (Base, Spd, WR), darker green = better rank, outline-grey = no value.
const rankShade = (x: number | null) => (x == null ? '#e5e7eb' : x === 1 ? '#047857' : x === 2 ? '#34d399' : x === 3 ? '#a7f3d0' : '#d1d5db')

const DESKTOP_GRID = 'lg:grid-cols-[40px_28px_minmax(190px,1fr)_44px_40px_40px_40px_62px_84px_30px]'
// The FP column only takes room on a phone once there is a result to show, and the Fixed $ column only once a price is out.
export const rowGrid = (showFp: boolean, showPrice = true) =>
  // Phone: [silk] | # | Horse | Peak | Base | Spd | Rating (| Fixed $) (| FP), everything on screen at once. The silk column joins from 380px up,
  // or from 430px up in the densest state (result and prices both shown) so horse names keep some room on a 390px phone.
  // The # track is 20px so a two-digit tab number clears the badge beside it.
  // (Full class names on purpose: Tailwind only generates classes it can read literally.)
  `${
    showFp
      ? showPrice
        ? 'grid-cols-[20px_minmax(0,1fr)_26px_24px_24px_44px_60px_18px] min-[430px]:grid-cols-[24px_20px_minmax(0,1fr)_26px_24px_28px_44px_60px_18px]'
        : 'grid-cols-[20px_minmax(0,1fr)_26px_24px_28px_44px_18px] min-[380px]:grid-cols-[24px_20px_minmax(0,1fr)_26px_24px_28px_44px_18px]'
      : showPrice
        ? 'grid-cols-[20px_minmax(0,1fr)_26px_24px_28px_44px_60px] min-[380px]:grid-cols-[24px_20px_minmax(0,1fr)_26px_24px_28px_44px_60px]'
        : 'grid-cols-[20px_minmax(0,1fr)_26px_24px_28px_44px] min-[380px]:grid-cols-[24px_20px_minmax(0,1fr)_26px_24px_28px_44px]'
  } ${DESKTOP_GRID}`
// Where the silk column starts showing on a phone (matches rowGrid).
export const silkFrom = (showFp: boolean, showPrice = true) => (showFp && showPrice ? 'min-[430px]:block' : 'min-[380px]:block')
const LG_ONLY = 'hidden lg:block'

// A cell with no value: a faint dash whose tooltip says why, so "not rated" is not mistaken for a blank rendering glitch.
function Missing({ why }: { why: string }) {
  return (
    <span className="text-ink-faint" title={why}>
      &ndash;
    </span>
  )
}

export function RunnerRow({ runner, raceDate, selected, effective, showFp, showPrice = true, showBias = true, combo, onClick }: RunnerRowProps) {
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
      className={`group grid min-w-full cursor-pointer items-center gap-x-1 border-b border-l-4 ${runner.finishPosition === 1 && !f.scratched ? 'border-l-amber' : 'border-l-transparent'} border-line-soft px-2 py-1 text-left text-sm lg:gap-x-2 transition-colors ${rowGrid(showFp, showPrice)} ${
        f.scratched ? 'opacity-50' : selected ? 'bg-emerald-bg' : runner.finishPosition === 1 ? 'bg-amber-bg/40 hover:bg-amber-bg/70' : 'hover:bg-bg'
      }`}
    >
      {runner.silkUrl ? <img src={runner.silkUrl} alt="" className={`hidden h-6 w-6 rounded-sm object-contain ${silkFrom(showFp, showPrice)} lg:h-8 lg:w-8`} /> : <span className={`hidden h-6 w-6 ${silkFrom(showFp, showPrice)} lg:h-8 lg:w-8`} />}
      <span className="font-mono text-ink-mute">{runner.tabNumber}</span>
      <span className="min-w-0">
        <span className="flex items-center gap-1.5">
          <span className={`truncate font-medium text-ink ${f.scratched ? 'line-through' : ''}`}>{runner.horse}</span>
          {runner.dataScratched && <span className="flex-none rounded bg-rose px-1 text-[10px] font-semibold text-white">SCR</span>}
          {showBias && hasRunnerBias(runner) && !f.scratched && (
            <span
              className={`flex-none rounded border px-1 font-mono text-[10px] font-semibold ${runnerBias(runner) >= 0 ? 'border-emerald-line bg-emerald-bg text-emerald-deep' : 'border-rose-line bg-rose-bg text-rose'}`}
              title="Draw lean read from earlier races at this meeting would move this runner by this much. Display only: it is not inside Proj."
            >
              <span className="lg:hidden">{runnerBias(runner) >= 0 ? '\u25B2' : '\u25BC'}{Math.abs(runnerBias(runner)).toFixed(1)}</span>
              <span className="hidden lg:inline">bias {fmtBias(runnerBias(runner))}</span>
            </span>
          )}
          {runner.projectionModel === 'debut' && !f.scratched && (
            <span className="hidden flex-none rounded border border-amber-line bg-amber-bg px-1 text-[10px] text-amber lg:inline" title="First starter: no form to rate. The Proj is an estimate from the race's level and this runner's price against the field, not a form rating. It is kept out of the Rating, the gap lines and the quaddie pools.">
              est
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
            <span className="flex-none rounded border border-line px-1 font-mono text-[9px] leading-[14px] text-ink-mute" title={`Barrier ${runner.barrier}`}>
              B{runner.barrier}
            </span>
          )}
          {runner.weightCarried != null && <span className="flex-none font-mono text-[10px] text-ink-faint lg:hidden" title="Weight carried">{runner.weightCarried}kg</span>}
          <span className="max-w-[65%] flex-none truncate text-ink-mute">{runner.jockey}</span>
          <span className="min-w-0 truncate">/ {runner.trainer}</span>
          {runner.weightCarried != null && <span className="hidden flex-none font-mono lg:inline">&middot; {runner.weightCarried}kg</span>}
        </span>
      </span>
      <span className={`text-right font-mono ${f.rtsClass} ${LG_ONLY}`} title={f.rtsTitle}>
        {f.spell.label}
      </span>
      <span
        className="text-right font-mono text-[12px] text-ink-mute lg:text-[13px]"
        title={runner.peakWpr != null ? `Peak ${runner.peakWpr.toFixed(1)}: the highest rating this horse has run in the 12 months before this race (runner-page ratings, same scale as WR)` : undefined}
      >
        {f.scratched ? '' : runner.peakWpr == null ? <Missing why="No rated run in the 12 months before this race" /> : Math.round(runner.peakWpr)}
      </span>
      <span className="text-right font-mono text-[12px] text-ink-mute lg:text-[13px]" title="TopRate's own forward rating (wpr_nett)">
        {f.scratched ? '' : runner.nett == null ? <Missing why="No Base from TopRate for this runner (first starters usually have none)" /> : Math.round(runner.nett)}
      </span>
      <span
        className="text-right font-mono text-[12px] text-ink-mute lg:text-[13px]"
        title={runner.speedRating != null ? `Spd ${speedRatingOnScale(runner.speedRating).toFixed(1)} (${runner.speedRating.toFixed(1)} lengths against par; 79 = par, higher is faster, about 1.3 points a length, same scale as Base and WR): recency-weighted mean of the horse's earlier time-based figures` : undefined}
      >
        {f.scratched ? '' : runner.speedRating == null ? <Missing why="No Spd: needs an earlier time-based figure (overseas runs have none)" /> : Math.round(speedRatingOnScale(runner.speedRating))}
      </span>
      <span
        className="text-right font-mono leading-tight"
        title={combo?.estimated ? `Estimated rating ${combo.rating != null ? combo.rating.toFixed(1) : '-'}: a first starter, so this is the WR estimate (race level and market price), not a form rating. It does not count in the ranks or gap lines.` : combo ? `Rating ${combo.rating != null ? combo.rating.toFixed(1) : '-'} (rank ${combo.tied ? 'joint ' : ''}${combo.rank}): the WR projection at ${runner.weightCarried != null ? runner.weightCarried + 'kg' : "today's weight"}${sd != null ? ` ± ${Math.round(sd)}` : ''}, set from the simulated win chance. Rated price ${fmtPrice(effective?.effectivePrice ?? null)}${effective?.effectivePlacePrice != null ? `, place ${fmtPrice(effective.effectivePlacePrice)}` : ''} (model view only, not a value claim). Base and Spd are shown but not counted. Ranks: Base ${combo.ranks[0] ?? '-'}, Spd ${combo.ranks[1] ?? '-'}, WR ${combo.ranks[2] ?? '-'}` : undefined}
      >
        {f.scratched ? null : !combo ? (
          <span className="mr-1.5 text-ink-faint lg:mr-0" title="No WR (no rated form, or a jumps race)">&ndash;</span>
        ) : (
          <>
            <span className={`inline-block min-w-[18px] text-center text-[13px] font-semibold lg:text-[14px] ${combo.estimated ? 'italic text-ink-faint' : combo.rank === 1 ? 'text-emerald-deep' : 'text-ink'}`}>
              {combo.estimated ? '~' : ''}{combo.rating != null ? combo.rating.toFixed(1) : combo.rank}
            </span>
            {f.overridden && <span className="ml-0.5 text-amber" title="Manually adjusted">*</span>}
            <span className="mt-[2px] flex justify-end gap-[2px]" aria-hidden="true">
              {combo.ranks.map((x, i) => (
                <span key={i} className="h-[5px] w-[5px] rounded-[1px] lg:h-[6px] lg:w-[6px]" style={{ background: rankShade(x) }} />
              ))}
            </span>
          </>
        )}
      </span>
      <span className={`text-right text-ink-mute ${showPrice ? '' : LG_ONLY}`}>
        <PriceCell runner={runner} scratched={f.scratched} move={f.move} showMove={f.showMove} />
      </span>
      <span className={`text-right ${showFp ? '' : LG_ONLY}`}>
        <FinishBadge pos={runner.finishPosition} />
      </span>
    </div>
  )
}
