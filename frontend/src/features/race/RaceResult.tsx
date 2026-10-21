import type { Race, Runner } from '../../types/domain'
import type { CombinedRank } from '../../lib/combinedRank'
import type { EffectiveRunner } from '../../lib/raceModel'
import { fmtInt, fmtPrice } from '../../lib/format'
import { speedOnWprScale } from '../../lib/speed'

interface RaceResultProps {
  race: Race
  combo: Map<string, CombinedRank>
  effective: Record<string, EffectiveRunner>
  scratched: Set<string>
  onSelectRunner: (runId: string) => void
}

type Placed = Runner & { finishPosition: number }

const ORDINAL = ['', '1st', '2nd', '3rd', '4th']

const POS_STYLE: Record<number, string> = {
  1: 'bg-yellow-300 text-yellow-950',
  2: 'bg-slate-400 text-white',
  3: 'bg-orange-800 text-white',
}
const posStyle = (pos: number) => POS_STYLE[pos] ?? 'bg-line-soft text-ink-mute'

// Rank chip colours: 1 solid green, 2 and 3 light green, the rest plain (same as the race table's Rank cell).
const rankTone = (rank: number) => (rank === 1 ? 'border-emerald bg-emerald text-white' : rank <= 3 ? 'border-emerald-line bg-emerald-bg text-emerald-deep' : 'border-line bg-panel text-ink-mute')

function PosPill({ pos, small }: { pos: number; small?: boolean }) {
  return <span className={`inline-flex shrink-0 items-center justify-center rounded-full font-bold ${posStyle(pos)} ${small ? 'min-w-7 px-1.5 py-0.5 text-xs' : 'min-w-9 px-2 py-0.5 text-xs'}`}>{small ? pos : (ORDINAL[pos] ?? `${pos}th`)}</span>
}

function Silk({ runner, w, h }: { runner: Runner; w: number; h: number }) {
  if (runner.silkUrl) return <img src={runner.silkUrl} alt="" width={w} height={h} className="shrink-0 object-contain" style={{ width: w, height: h }} />
  return (
    <span className="grid shrink-0 place-items-center rounded-md bg-line-soft font-mono text-xs font-semibold text-ink-mute" style={{ width: w, height: h }}>
      {runner.tabNumber}
    </span>
  )
}

// Placings for a race that has run. TAB's fast feed gives the order of the first four (and last fixed prices); margins and starting
// prices arrive with the official result, so each part fills in when it exists. Phones get compact rows; from lg the four placings are full-width
// rows with the Rank chip and (from xl) the signal figures.
export function RaceResult({ race, combo, effective, scratched, onSelectRunner }: RaceResultProps) {
  const placed = race.runners
    .filter((r): r is Placed => r.finishPosition != null && !scratched.has(r.runId))
    .sort((a, b) => a.finishPosition - b.finishPosition)
    .slice(0, 4)
  if (placed.length === 0) return null

  const official = race.allResulted && !race.provisional
  const hasSp = placed.some((r) => r.startingPrice != null)

  const priceOf = (r: Runner) => r.startingPrice ?? r.fixedWinPrice
  const priceCell = (r: Runner) => {
    const p = priceOf(r)
    if (p == null) return null
    return (
      <span title={r.startingPrice != null ? 'Starting price' : 'Last fixed price (starting price not in yet)'}>
        {fmtPrice(p)}
        {!hasSp && <span className="ml-0.5 text-[9px] font-normal text-ink-faint">fx</span>}
      </span>
    )
  }
  const marginText = (r: Placed) => (r.finishPosition > 1 && r.marginFinish != null ? `${Math.abs(r.marginFinish).toFixed(1)}L` : null)

  return (
    <section className="rounded-lg border border-line bg-panel shadow-[var(--shadow-1)] xl:flex xl:h-full xl:flex-col" aria-label="Race result">
      <div className="flex items-baseline justify-between gap-2 px-3 pb-1.5 pt-2.5 sm:px-4">
        <h3 className="text-sm font-semibold text-ink">Result</h3>
        <span className="text-[11px] text-ink-faint">{official ? 'Official' : 'Provisional, from TAB'}</span>
      </div>

      {/* Phones and tablets: one compact row per placing. */}
      <div className="lg:hidden">
        <ol>
          {placed.map((r) => {
            const win = r.finishPosition === 1
            const m = marginText(r)
            return (
              <li key={r.runId} className="border-t border-line-soft">
                <button type="button" onClick={() => onSelectRunner(r.runId)} className={`flex w-full items-center gap-2.5 px-3 py-2 text-left hover:bg-bg sm:px-4 ${win ? 'bg-emerald-tint' : ''}`}>
                  <Silk runner={r} w={win ? 34 : 30} h={win ? 40 : 36} />
                  <PosPill pos={r.finishPosition} small />
                  <span className="min-w-0 flex-1">
                    <span className={`block truncate text-[15px] text-ink ${win ? 'font-bold' : 'font-semibold'}`}>
                      {r.tabNumber}. {r.horse}
                    </span>
                    <span className="block truncate text-[11.5px] text-ink-mute">
                      {r.jockey} / {r.trainer}
                      {m ? ` · ${m}` : ''}
                    </span>
                  </span>
                  <span className="shrink-0 font-mono text-sm font-semibold text-ink">{priceCell(r)}</span>
                </button>
              </li>
            )
          })}
        </ol>
      </div>

      {/* lg and up: four condensed rows, one per placing. */}
      <ol className="hidden px-3 pb-2 sm:px-4 lg:flex lg:flex-col xl:flex-1">
        {placed.map((r) => {
          const win = r.finishPosition === 1
          const c = combo.get(r.runId)
          const proj = effective[r.runId]?.effectiveProjectedWpr ?? r.projectedWpr
          const m = marginText(r)
          return (
            <li key={r.runId} className="flex flex-1">
              <button type="button" onClick={() => onSelectRunner(r.runId)} className={`flex w-full items-center gap-3 rounded-md border-t border-line-soft px-2 py-1 text-left hover:bg-bg ${win ? 'bg-emerald-tint' : ''}`}>
                <Silk runner={r} w={26} h={31} />
                <PosPill pos={r.finishPosition} small />
                <span className="min-w-0 flex-1">
                  <span className="block truncate text-sm">
                    <span className={`text-ink ${win ? 'font-bold' : 'font-semibold'}`}>
                      {r.tabNumber}. {r.horse}
                    </span>
                    {r.barrier != null && <span className="ml-1.5 text-[12px] text-ink-mute">(B{r.barrier})</span>}
                  </span>
                  <span className="block truncate text-[12px] text-ink-mute">
                    {r.jockey} / {r.trainer}
                    {m ? ` · ${m}` : ''}
                  </span>
                </span>
                <span className="hidden shrink-0 gap-3 text-center xl:flex">
                  {[
                    ['Spd', r.speedRating != null ? fmtInt(speedOnWprScale(r.speedRating)) : '–'],
                    ['Nett', fmtInt(r.nett)],
                    ['Proj', fmtInt(proj)],
                  ].map(([label, val]) => (
                    <span key={label} className="w-9">
                      <span className="block text-[10px] uppercase tracking-wide text-ink-faint">{label}</span>
                      <span className="block font-mono text-[13px] font-semibold text-ink-soft">{val}</span>
                    </span>
                  ))}
                </span>
                <span className="w-16 shrink-0 text-center">
                  {c ? <span className={`rounded-full border px-1.5 py-px text-[11px] font-semibold ${rankTone(c.rank)}`}>Rank {c.tied ? '=' : ''}{c.rank}</span> : null}
                </span>
                <span className="w-16 shrink-0 text-right">
                  <span className="block text-[10px] uppercase tracking-wide text-ink-faint">Win</span>
                  <span className="block font-mono text-[15px] font-semibold text-ink">{priceCell(r)}</span>
                </span>
              </button>
            </li>
          )
        })}
      </ol>
    </section>
  )
}
