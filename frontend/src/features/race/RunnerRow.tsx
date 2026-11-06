import type { Runner } from '../../types/domain'
import type { EffectiveRunner } from '../../lib/raceModel'
import { fmtPrice } from '../../lib/format'
import { fmtBias, hasRunnerBias, runnerBias } from '../../lib/bias'
import { FinishBadge, PriceCell, useRowFacts } from './rowParts'
import type { CombinedRank } from '../../lib/combinedRank'
import { ratingMiss, ratingOnActualScale } from '../../lib/atw'

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

// Table row: Rating | (Actual | +/- once the race has a result) | Rated $ | Fixed $ | FP. Peak, Base and Spd live on the runner page only.
// Below lg the RTS column drops out (its track collapses to nothing via `hidden`) so everything else fits a phone without sideways scrolling; RTS moves into the detail line instead.

// Desktop tracks: silk | # | Horse | RTS | Rating | (Actual | +/-) | Rated $ | Fixed $ | FP.
const DESKTOP_GRID = 'lg:grid-cols-[40px_28px_minmax(190px,1fr)_44px_62px_70px_84px_30px]'
const DESKTOP_GRID_RESULT = 'lg:grid-cols-[40px_28px_minmax(190px,1fr)_44px_62px_56px_52px_70px_84px_30px]'
// The FP, Actual and +/- columns only take room once there is a result; the Fixed $ column only once a price is out, and not on phones once the race has a result.
export const rowGrid = (showFp: boolean, showPrice = true) =>
  // Phone: [silk] | # | Horse | Rating | (Actual | +/-) | Rated $ | (Fixed $) | (FP). The silk column joins from 380px up.
  // The # track is 20px so a two-digit tab number clears the badge beside it.
  // (Full class names on purpose: Tailwind only generates classes it can read literally.)
  `${
    showFp
      ? 'grid-cols-[20px_minmax(0,1fr)_44px_38px_36px_46px_18px] min-[380px]:grid-cols-[24px_20px_minmax(0,1fr)_44px_38px_36px_46px_18px]'
      : showPrice
        ? 'grid-cols-[20px_minmax(0,1fr)_44px_46px_60px] min-[380px]:grid-cols-[24px_20px_minmax(0,1fr)_44px_46px_60px]'
        : 'grid-cols-[20px_minmax(0,1fr)_44px_46px] min-[380px]:grid-cols-[24px_20px_minmax(0,1fr)_44px_46px]'
  } ${showFp ? DESKTOP_GRID_RESULT : DESKTOP_GRID}`
// Where the silk column starts showing on a phone (matches rowGrid).
export const silkFrom = (_showFp: boolean, _showPrice = true) => 'min-[380px]:block'
const LG_ONLY = 'hidden lg:block'

// A cell with no value: a faint dash whose tooltip says why, so "not rated" is not mistaken for a blank rendering glitch.
function Missing({ why }: { why: string }) {
  return (
    <span className="text-ink-faint" title={why}>
      &ndash;
    </span>
  )
}

// Bad-run risk (percent) at which the race table marks a runner: about twice the average of 7%, roughly the riskiest decile (held out: predicted 16.5%, actual 18.7%).
const BAD_RUN_FLAG = 15

export function RunnerRow({ runner, raceDate, selected, effective, showFp, showPrice = true, showBias = true, combo, onClick }: RunnerRowProps) {
  const f = useRowFacts(runner, raceDate, effective)
  const sd = runner.projectionSd
  const shownRating = ratingOnActualScale(combo?.rating ?? null, runner)
  const miss = ratingMiss(runner, combo?.rating)
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
            <span className="flex-none rounded border border-line px-1 text-[10px] text-ink-faint" title="Light-history model (0-2 prior runs): wider error">
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
        className="text-right font-mono leading-tight"
        title={combo?.estimated ? `Estimated rating ${combo.rating != null ? combo.rating.toFixed(1) : '-'}: a first starter, so this is the WR estimate (race level and market price), not a form rating. It does not count in the ranks or gap lines.` : combo ? `Rating ${shownRating != null ? shownRating.toFixed(1) : '-'}, on the scale of the Actual rating (the model's ${combo.rating != null ? combo.rating.toFixed(1) : '-'} at today's weight shifted by ${(runner.resultsScaleOffset ?? 0).toFixed(1)} for weight, age, sex and month) (rank ${combo.tied ? 'joint ' : ''}${combo.rank}): the WR projection at ${runner.weightCarried != null ? runner.weightCarried + 'kg' : "today's weight"}${sd != null ? ` ± ${Math.round(sd)}` : ''}, set from the simulated win chance${effective?.directBlend ? ' (blended with the direct finishing-position model)' : ''}. Rated price ${fmtPrice(effective?.effectivePrice ?? null)}${effective?.effectivePlacePrice != null ? `, place ${fmtPrice(effective.effectivePlacePrice)}` : ''} (model view only, not a value claim).${runner.badRunRisk != null ? ` Bad-run risk ${runner.badRunRisk.toFixed(0)}% (average runner about 7%): the chance the rating comes in more than 12 below the form figure.` : ''}` : undefined}
      >
        {f.scratched ? null : !combo ? (
          <span className="mr-1.5 text-ink-faint lg:mr-0" title="No WR (no rated form, or a jumps race)">&ndash;</span>
        ) : (
          <>
            <span className={`inline-block min-w-[18px] text-center text-[13px] font-semibold lg:text-[14px] ${combo.estimated ? 'italic text-ink-faint' : combo.rank === 1 ? 'text-emerald-deep' : 'text-ink'}`}>
              {combo.estimated ? '~' : ''}{shownRating != null ? shownRating.toFixed(1) : combo.rank}
            </span>
            {f.overridden && <span className="ml-0.5 text-amber" title="Manually adjusted">*</span>}
            {runner.badRunRisk != null && runner.badRunRisk >= BAD_RUN_FLAG && <span className="ml-0.5 hidden text-amber lg:inline" title={`Bad-run risk ${runner.badRunRisk.toFixed(0)}% (average runner about 7%)`}>!</span>}
          </>
        )}
      </span>
      {showFp && (
        <span className="text-right font-mono text-[12px] text-ink lg:text-[13px]" title="The rating the horse actually ran">
          {f.scratched ? '' : runner.actualWpr == null ? <Missing why="Actual rating not published yet (usually within a few days)" /> : runner.actualWpr.toFixed(1)}
        </span>
      )}
      {showFp && (
        <span className={`text-right font-mono text-[12px] font-medium lg:text-[13px] ${miss == null ? '' : miss >= 0 ? 'text-blue-700' : 'text-rose'}`} title="Actual minus the Rating shown (blue = ran above the rating, red = below)">
          {f.scratched || miss == null ? '' : `${miss >= 0 ? '+' : '\u2212'}${Math.abs(miss).toFixed(1)}`}
        </span>
      )}
      <span className="text-right font-mono text-[12px] text-ink-mute lg:text-[13px]" title={effective?.effectivePlacePrice != null ? `Rated price (model view). Place ${fmtPrice(effective.effectivePlacePrice)}` : 'Rated price (model view)'}>
        {f.scratched ? '' : effective?.effectivePrice != null ? fmtPrice(effective.effectivePrice) : <Missing why="No rated price (no rating for this runner)" />}
      </span>
      <span className={`text-right text-ink-mute ${showPrice && !showFp ? '' : LG_ONLY}`}>
        <PriceCell runner={runner} scratched={f.scratched} move={f.move} showMove={f.showMove} />
      </span>
      <span className={`text-right ${showFp ? '' : LG_ONLY}`}>
        <FinishBadge pos={runner.finishPosition} />
      </span>
    </div>
  )
}
