import type { QuadBet, QuinBet, Sel, TriBet, WinBet } from '../../lib/betRules'


// "Bets" card on the race page: which betting rules (lib/betRules.ts) this race fits, live from the Combo gaps and SM.
// Bets that apply get a row each (tag, selections as number chips, stake on the right); the ones that don't are
// folded into one muted "Skipped" line. The frozen pre-race record and results are on the Bets tab (bets_log.json).

function Chips({ sel }: { sel: Sel[] }) {
  return (
    <span className="inline-flex flex-wrap gap-0.5 align-middle">
      {sel.map((s) => (
        <span
          key={s.runner.runId}
          className="min-w-[1.4rem] rounded border border-line bg-bg px-1 text-center font-mono text-[11px] leading-5 text-ink"
        >
          {s.runner.tabNumber}
        </span>
      ))}
    </span>
  )
}

const TAG: Record<string, string> = {
  WIN: 'bg-emerald text-white',
  TRI: 'bg-indigo text-white',
  QUIN: 'bg-indigo-bg text-indigo border border-indigo',
  QUAD: 'bg-amber text-white',
  EARLY: 'bg-amber-bg text-amber border border-amber-line',
}

function Row({ tag, children, stake, note }: { tag: string; children: React.ReactNode; stake: string; note?: string }) {
  return (
    <div className="flex items-start gap-2 py-1.5">
      <span className={`mt-0.5 w-12 flex-none rounded px-1 text-center text-[10px] font-bold tracking-wide ${TAG[tag]}`}>{tag}</span>
      <div className="min-w-0 flex-1 text-xs text-ink">{children}</div>
      <div className="flex-none text-right">
        <div className="font-mono text-sm font-semibold text-ink">{stake}</div>
        {note && <div className="font-mono text-[10px] text-ink-faint">{note}</div>}
      </div>
    </div>
  )
}

const pct = (stake: number, combos: number) => `${combos} combos · ${Math.round((stake / combos) * 100)}%`

export function BetPanel({
  win,
  tri,
  quin,
  quad,
  earlyQuad,
  raceNumber,
}: {
  win: WinBet | null
  tri: TriBet | null
  quin: QuinBet | null
  quad: QuadBet | null
  earlyQuad: QuadBet | null
  raceNumber: number
}) {
  const skipped: string[] = []
  if (!win) skipped.push('Win')
  if (!quin || quin.skip) skipped.push(`Quinella (${quin?.skip ?? 'fewer than 2 within 4'})`)
  if (!tri || tri.skip) skipped.push(`Trifecta (${tri?.skip ?? 'fewer than 2 within 4'})`)
  for (const [name, q] of [['Early quaddie', earlyQuad], ['Quaddie', quad]] as const) {
    if (q?.skip) skipped.push(`${name} R${q.legs[0].race.raceNumber}-R${q.legs[q.legs.length - 1].race.raceNumber} (${q.skip})`)
  }
  const active =
    (win ? 1 : 0) + (tri && !tri.skip ? 1 : 0) + (quin && !quin.skip ? 1 : 0) + (quad && !quad.skip ? 1 : 0) + (earlyQuad && !earlyQuad.skip ? 1 : 0)
  const total =
    (win?.stake ?? 0) + (tri && !tri.skip ? tri.stake : 0) + (quin && !quin.skip ? quin.stake : 0) + (quad && !quad.skip ? quad.stake : 0) + (earlyQuad && !earlyQuad.skip ? earlyQuad.stake : 0)
  const halved = [win?.target === 100, tri && !tri.skip && tri.stake < 10, quin && !quin.skip && quin.stake < 15, quad && !quad.skip && quad.stake < 25, earlyQuad && !earlyQuad.skip && earlyQuad.stake < 25].some(Boolean)
  const fmt = (v: number) => (Number.isInteger(v) ? `$${v}` : `$${v.toFixed(2)}`)

  const quadRow = (tag: string, q: QuadBet) => (
    <Row tag={tag} stake={fmt(q.stake)} note={pct(q.stake, q.combos)}>
      <div className="flex flex-col gap-0.5">
        {q.legs.map((l) => (
          <div key={l.race.raceId} className="flex items-center gap-1.5">
            <span className={`w-7 flex-none font-mono text-[11px] ${l.race.raceNumber === raceNumber ? 'font-bold text-ink' : 'text-ink-mute'}`}>
              R{l.race.raceNumber}
            </span>
            <Chips sel={l.outer} />
          </div>
        ))}
      </div>
    </Row>
  )

  return (
    <div className="rounded-lg border border-line bg-panel px-3 py-2 shadow-[var(--shadow-1)]">
      <div className="flex items-baseline justify-between gap-2 border-b border-line-soft pb-1.5">
        <span className="text-sm font-semibold text-ink">Bets</span>
        <span className="text-xs text-ink-mute">
          {active ? (
            <>
              {active} bet{active > 1 ? 's' : ''} · <span className="font-mono font-semibold text-ink">${total.toFixed(0)}</span>
            </>
          ) : (
            'no bets in this race'
          )}
        </span>
      </div>
      {halved && <div className="pt-1 text-[11px] font-medium text-amber">Heavy track: stakes halved</div>}
      <div className="divide-y divide-line-soft">
        {win && (
          <Row
            tag="WIN"
            stake={win.stake != null ? `$${win.stake.toFixed(0)}` : '-'}
            note={win.price != null ? `@ $${win.price.toFixed(2)} → $${win.target}` : `returns $${win.target}`}
          >
            <span className="font-semibold">
              {win.sel.runner.tabNumber}. {win.sel.runner.horse}
            </span>
            {win.stake == null && <span className="text-ink-faint"> · stake = {win.target} ÷ price</span>}
          </Row>
        )}
        {quin && !quin.skip && (
          <Row tag="QUIN" stake={fmt(quin.stake)} note={pct(quin.stake, quin.combos)}>
            <div className="flex items-center gap-1.5">
              <span className="w-7 flex-none text-[11px] text-ink-mute">box</span>
              <Chips sel={quin.box} />
            </div>
          </Row>
        )}
        {tri && !tri.skip && (
          <Row tag="TRI" stake={fmt(tri.stake)} note={pct(tri.stake, tri.combos)}>
            <div className="flex flex-col gap-0.5">
              <div className="flex items-center gap-1.5">
                <span className="w-7 flex-none text-[11px] text-ink-mute">1-2</span>
                <Chips sel={tri.firstSecond} />
              </div>
              <div className="flex items-center gap-1.5">
                <span className="w-7 flex-none text-[11px] text-ink-mute">3rd</span>
                <Chips sel={tri.third} />
              </div>
            </div>
          </Row>
        )}
        {earlyQuad && !earlyQuad.skip && quadRow('EARLY', earlyQuad)}
        {quad && !quad.skip && quadRow('QUAD', quad)}
      </div>
      {skipped.length > 0 && (
        <div className="mt-1 border-t border-line-soft pt-1.5 text-[11px] leading-snug text-ink-faint">
          Skipped: {skipped.join(' · ')}
        </div>
      )}
    </div>
  )
}
