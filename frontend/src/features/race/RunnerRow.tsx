import type { Runner } from '../../types/domain'
import type { EffectiveRunner } from '../../lib/raceModel'
import { fmtPrice, fmtWpr } from '../../lib/format'
import { fmtEv, modelPrice, TIER_HELP, TIER_LABEL, type Signal } from '../../lib/betSignals'
import { fmtBias, hasRunnerBias, runnerBias } from '../../lib/bias'
import { BAND_BORDER, fmtAdj, FinishBadge, PriceCell, ratingSuffix, smClass, useRowFacts } from './rowParts'

interface RunnerRowProps {
  runner: Runner
  raceDate: string
  selected: boolean
  effective?: EffectiveRunner
  // Bet signal for this runner (experimental, see lib/betSignals.ts): model price, edge and tier. null when the race has none.
  signal?: Signal | null
  band: 'core' | 'inner' | 'outer' | 'none'
  showFp: boolean
  // Bias chip only once enough earlier races have run at the meeting (lib/bias MIN_BIAS_RACES).
  showBias?: boolean
  onClick: () => void
}

// Table row, same columns on every screen. Below lg the RTS column drops out (their tracks collapse to nothing via
// `hidden`) so Horse, Proj, SM, Model $, Fixed $ and FP fit a phone without sideways scrolling; RTS moves into the detail line instead.
const DESKTOP_GRID = 'lg:grid-cols-[36px_28px_minmax(190px,1fr)_44px_58px_52px_64px_56px_84px_30px]'
// The FP column only takes room on a phone once there is a result to show.
export const rowGrid = (showFp: boolean) =>
  `${showFp ? 'grid-cols-[22px_16px_minmax(0,1fr)_36px_28px_40px_60px_20px]' : 'grid-cols-[22px_16px_minmax(0,1fr)_36px_28px_40px_60px]'} ${DESKTOP_GRID}`
const LG_ONLY = 'hidden lg:block'

export function RunnerRow({ runner, raceDate, selected, effective, signal, band, showFp, showBias = true, onClick }: RunnerRowProps) {
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
          {signal && (signal.t === 'S' || signal.t === 'V') && !f.scratched && (
            <span
              className={`flex-none rounded px-1 text-[10px] font-semibold ${signal.t === 'S' ? 'bg-emerald text-white' : 'border border-emerald-line bg-emerald-bg text-emerald-deep'}`}
              title={`${TIER_LABEL[signal.t]}: ${TIER_HELP[signal.t]}`}
            >
              <span className="lg:hidden">{signal.t}</span>
              <span className="hidden lg:inline">{signal.t === 'S' ? 'SELECT' : 'VOL'}</span>
            </span>
          )}
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
            <span className={`flex-none rounded border border-line px-1 text-[10px] text-ink-faint ${showBias && hasRunnerBias(runner) ? 'hidden lg:inline' : ''}`} title="Light-history model (0-2 prior runs): wider error">
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
      <span className="text-right">
        {f.scratched ? (
          <span className="font-mono font-semibold text-ink-faint">SCR</span>
        ) : (
          <span title={`${effective?.ratingSource === 'bet' ? 'Rating (blend of the bet-signal model and the WPR projection)' : 'Projected WPR'} ${fmtWpr(f.proj)}${f.atwOff !== 0 && effective?.ratingSource !== 'bet' ? ` at ${runner.weightCarried != null ? runner.weightCarried + 'kg' : "today's weight"} (model rating ${fmtWpr(f.proj != null ? f.proj - f.atwOff : null)})` : ''}${sd != null ? ` ± ${Math.round(sd)}` : ''}${runner.projectionModel === 'light' ? ' (light-history model)' : ''}`}>
            <span className="font-mono text-sm font-semibold leading-tight lg:text-[15px] text-emerald-deep">{fmtWpr(f.proj)}</span>
            {f.overridden && <span className="ml-0.5 text-amber" title="Manually adjusted">*</span>}
          </span>
        )}
      </span>
      <span
        className={`text-right font-mono ${smClass(effective?.speedMapAdj)}${effective?.speedMapLight ? ' opacity-70' : ''}`}
        title={effective?.speedMapLight ? 'Light-history runner: estimated without its own run history, lower confidence' : undefined}
      >
        {f.scratched ? '' : fmtAdj(effective?.speedMapAdj)}
      </span>
      <span
        className={`text-right font-mono text-ink-mute ${LG_ONLY}`}
        title={signal ? `Model price $${(modelPrice(signal.m) ?? 0).toFixed(2)}: what the bet-signal model would pay (win chance ${(signal.m * 100).toFixed(0)}%), judged against $${signal.p.toFixed(2)}. Experimental.` : 'No bet signal for this race (needs the full field, drawn and priced)'}
      >
        {f.scratched || !signal ? '' : fmtPrice(modelPrice(signal.m))}
      </span>
      <span className={`text-right font-mono text-[12px] lg:text-sm ${signal && signal.e >= 1.05 ? 'font-semibold text-emerald-deep' : 'text-ink-faint'}`} title="EV: bet-signal model win chance x price (1.00 = break-even)">
        {f.scratched || !signal ? '' : fmtEv(signal.e)}
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
