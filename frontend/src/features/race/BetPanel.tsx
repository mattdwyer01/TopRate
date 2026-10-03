import type { QuadBet, Sel, TriBet, WinBet } from '../../lib/betRules'
import { QUAD_STAKE, TRI_STAKE, WIN_TARGET } from '../../lib/betRules'

// "Bets" box on the race page: which of the betting rules (lib/betRules.ts) this race fits, with the selections,
// combinations and stake. Shown for every race; a rule that does not apply says why in one short line.

function nums(sel: Sel[]): string {
  return sel.map((s) => s.runner.tabNumber).join(', ')
}

function flexi(stake: number, combos: number): string {
  return combos > 0 ? `${Math.round((stake / combos) * 100)}%` : '-'
}

export function BetPanel({
  win,
  tri,
  quad,
  raceNumber,
}: {
  win: WinBet | null
  tri: TriBet | null
  quad: QuadBet | null
  raceNumber: number
}) {
  const row = 'flex flex-wrap items-baseline gap-x-2 gap-y-0.5'
  const label = 'w-16 flex-none font-semibold text-ink'
  const skip = 'text-ink-faint'
  return (
    <div className="rounded-md border border-line bg-panel px-3 py-2 text-xs shadow-[var(--shadow-1)]">
      <div className="mb-1 flex items-baseline justify-between gap-2">
        <span className="text-sm font-semibold text-ink">Bets</span>
        <span className="text-ink-faint">rules card, live from Combo and SM</span>
      </div>
      <div className="flex flex-col gap-1">
        <div className={row}>
          <span className={label}>Win</span>
          {win ? (
            <span className="text-ink">
              <span className="rounded bg-emerald px-1 font-semibold text-white">{win.sel.runner.tabNumber}. {win.sel.runner.horse}</span>{' '}
              {win.price != null && win.stake != null
                ? <>stake <b>${win.stake.toFixed(0)}</b> at ${win.price.toFixed(2)} to win ${WIN_TARGET}</>
                : <>to win ${WIN_TARGET} (stake = {WIN_TARGET} &divide; (price &minus; 1))</>}
            </span>
          ) : (
            <span className={skip}>no bet (needs top pick 4+ clear, SM green, no first starter)</span>
          )}
        </div>
        <div className={row}>
          <span className={label}>Trifecta</span>
          {tri && !tri.skip ? (
            <span className="text-ink">
              {nums(tri.firstSecond)} / {nums(tri.firstSecond)} / {nums(tri.third)} &middot; {tri.combos} combos &middot;{' '}
              <b>${TRI_STAKE}</b> flexi ({flexi(TRI_STAKE, tri.combos)})
            </span>
          ) : (
            <span className={skip}>no bet{tri?.skip ? ` (${tri.skip})` : ' (fewer than 2 within 4)'}</span>
          )}
        </div>
        {quad && (
          <div className={row}>
            <span className={label}>Quaddie</span>
            {!quad.skip ? (
              <span className="text-ink">
                {quad.legs.map((l, i) => (
                  <span key={l.race.raceId} className={l.race.raceNumber === raceNumber ? 'font-semibold' : ''}>
                    {i > 0 && ' / '}R{l.race.raceNumber}: {nums(l.outer)}
                  </span>
                ))}{' '}
                &middot; {quad.combos} combos &middot; <b>${QUAD_STAKE}</b> flexi ({flexi(QUAD_STAKE, quad.combos)})
              </span>
            ) : (
              <span className={skip}>
                main quaddie R{quad.legs[0].race.raceNumber}-R{quad.legs[quad.legs.length - 1].race.raceNumber}: no bet ({quad.skip})
              </span>
            )}
          </div>
        )}
      </div>
    </div>
  )
}
