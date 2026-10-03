import { EARLY_QUAD_STAKE, QUAD_STAKE, QUIN_STAKE, TRI_STAKE, type QuadBet, type QuinBet, type Sel, type TriBet, type WinBet } from '../../lib/betRules'
import type { LoggedBet, LoggedKind } from '../../lib/betsLog'


// "Bets" card on the race page: which betting rules (lib/betRules.ts) this race fits, live from the Combo gaps and SM.
// Bets that apply get a row each (tag, selections as number chips, stake on the right); the ones that don't are
// folded into one muted "Skipped" line. Once a bet is logged (bets_log.json, locked ~10 minutes before the race) its
// frozen record replaces the live rule, with the result once settled: return and profit, or the stake lost. After the
// jump only logged bets are shown (the live numbers change after the start, so the rules no longer mean anything).

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

function NumChips({ nums }: { nums: string[] }) {
  return (
    <span className="inline-flex flex-wrap gap-0.5 align-middle">
      {nums.map((n) => (
        <span key={n} className="min-w-[1.4rem] rounded border border-line bg-bg px-1 text-center font-mono text-[11px] leading-5 text-ink">
          {n}
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

function Row({
  tag,
  children,
  stake,
  note,
  result,
}: {
  tag: string
  children: React.ReactNode
  stake: string
  note?: string
  result?: React.ReactNode
}) {
  return (
    <div className="flex items-start gap-2 py-1.5">
      <span className={`mt-0.5 w-12 flex-none rounded px-1 text-center text-[10px] font-bold tracking-wide ${TAG[tag]}`}>{tag}</span>
      <div className="min-w-0 flex-1 text-xs text-ink">{children}</div>
      <div className="flex-none text-right">
        <div className="font-mono text-sm font-semibold text-ink">{stake}</div>
        {note && <div className="font-mono text-[10px] text-ink-faint">{note}</div>}
        {result}
      </div>
    </div>
  )
}

const KIND_TAG: Record<LoggedKind, string> = { Win: 'WIN', Quinella: 'QUIN', Trifecta: 'TRI', EarlyQuaddie: 'EARLY', Quaddie: 'QUAD' }
const cash = (v: number) => `$${Math.abs(v).toFixed(2)}`

// Result line of a logged bet: return and profit when it won, the stake lost when it lost
function Result({ b }: { b: LoggedBet }) {
  const cls = 'mt-0.5 font-mono text-[11px]'
  if (b.status === 'won') {
    const ret = b.return ?? 0
    const div = b.bet === 'Win' ? (b.price != null ? `@ $${b.price.toFixed(2)}` : '') : b.dividend != null ? `div $${b.dividend.toFixed(2)}` : ''
    return (
      <div className={cls}>
        <div className="text-ink-mute">
          {div} → {cash(ret)}
        </div>
        <div className="font-semibold text-emerald">Won +{cash(ret - b.stake)}</div>
      </div>
    )
  }
  if (b.status === 'lost') return <div className={`${cls} font-semibold text-rose`}>Lost −{cash(b.stake)}</div>
  if (b.status === 'refund') return <div className={`${cls} text-ink-mute`}>Refunded</div>
  if (b.status === 'void') return <div className={`${cls} text-ink-mute`}>Void (no result)</div>
  return <div className={`${cls} text-ink-faint`}>Pending</div>
}

// Selection of a logged bet as the log stores it: '4 Horse' (win), 'box 4,7,3', '1,2 / 1,2 / 1,2,5', 'R5: 1,2 / R6: 3'
function LoggedSelection({ b, raceNumber }: { b: LoggedBet; raceNumber: number }) {
  if (b.bet === 'Win') return <span className="font-semibold">{b.selection.replace(/^(\d+) /, '$1. ')}</span>
  const parts = b.selection.split(' / ')
  const tri = ['1st', '2nd', '3rd']
  return (
    <div className="flex flex-col gap-0.5">
      {parts.map((p, i) => {
        const m = p.match(/^(R\d+): (.*)$/) ?? p.match(/^(box) (.*)$/)
        const label = m ? m[1] : b.bet === 'Trifecta' ? tri[i] : ''
        const nums = (m ? m[2] : p).split(',').map((x) => x.trim()).filter(Boolean)
        const bold = m && label === `R${raceNumber}`
        return (
          <div key={i} className="flex items-center gap-1.5">
            <span className={`w-7 flex-none font-mono text-[11px] ${bold ? 'font-bold text-ink' : 'text-ink-mute'}`}>{label}</span>
            <NumChips nums={nums} />
          </div>
        )
      })}
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
  logged,
  started,
  bush,
}: {
  win: WinBet | null
  tri: TriBet | null
  quin: QuinBet | null
  quad: QuadBet | null
  earlyQuad: QuadBet | null
  raceNumber: number
  logged: LoggedBet[] // bets_log.json entries covering this race
  started: boolean
  bush: boolean // bush meeting: no bets
}) {
  const log = (k: LoggedKind) => logged.find((b) => b.bet === k) ?? null
  const lw = log('Win')
  const lq = log('Quinella')
  const lt = log('Trifecta')
  const le = log('EarlyQuaddie')
  const lm = log('Quaddie')
  // live rules only before the jump, and only for bet types not already logged
  if (started || lw) win = null
  if (started || lq) quin = null
  if (started || lt) tri = null
  if (started || le) earlyQuad = null
  if (started || lm) quad = null

  const skipped: string[] = []
  if (!started && !bush) {
    if (!win && !lw) skipped.push('Win')
    if (!lq && (!quin || quin.skip)) skipped.push(`Quinella (${quin?.skip ?? 'fewer than 2 within 4'})`)
    if (!lt && (!tri || tri.skip)) skipped.push(`Trifecta (${tri?.skip ?? 'fewer than 2 within 4'})`)
    for (const [name, q] of [['Early quaddie', earlyQuad], ['Quaddie', quad]] as const) {
      if (q?.skip) skipped.push(`${name} R${q.legs[0].race.raceNumber}-R${q.legs[q.legs.length - 1].race.raceNumber} (${q.skip})`)
    }
  }
  const loggedRows = [lw, lq, lt, le, lm].filter((b): b is LoggedBet => b != null)
  const settled = loggedRows.filter((b) => b.status !== 'pending')
  const pl = settled.reduce((s, b) => s + (b.return ?? 0) - b.stake, 0)
  const active =
    loggedRows.length +
    (win ? 1 : 0) + (tri && !tri.skip ? 1 : 0) + (quin && !quin.skip ? 1 : 0) + (quad && !quad.skip ? 1 : 0) + (earlyQuad && !earlyQuad.skip ? 1 : 0)
  const total =
    loggedRows.reduce((t, b) => t + b.stake, 0) +
    (win?.stake ?? 0) + (tri && !tri.skip ? tri.stake : 0) + (quin && !quin.skip ? quin.stake : 0) + (quad && !quad.skip ? quad.stake : 0) + (earlyQuad && !earlyQuad.skip ? earlyQuad.stake : 0)
  const halved = [
    ...loggedRows.map((b) => (b.bet === 'Win' ? b.price != null && Math.abs(b.stake * b.price - 100) < 1 : b.stake < { Quinella: QUIN_STAKE, Trifecta: TRI_STAKE, Quaddie: QUAD_STAKE, EarlyQuaddie: EARLY_QUAD_STAKE }[b.bet])),win?.target === 100, tri && !tri.skip && tri.stake < TRI_STAKE, quin && !quin.skip && quin.stake < QUIN_STAKE, quad && !quad.skip && quad.stake < QUAD_STAKE, earlyQuad && !earlyQuad.skip && earlyQuad.stake < EARLY_QUAD_STAKE].some(Boolean)
  const fmt = (v: number) => (Number.isInteger(v) ? `$${v}` : `$${v.toFixed(2)}`)

  const loggedRow = (b: LoggedBet | null) =>
    b && (
      <Row
        key={b.bet_id}
        tag={KIND_TAG[b.bet]}
        stake={fmt(b.stake)}
        note={b.bet === 'Win' ? (b.price != null ? `@ $${b.price.toFixed(2)}` : undefined) : pct(b.stake, b.combos)}
        result={<Result b={b} />}
      >
        <LoggedSelection b={b} raceNumber={raceNumber} />
      </Row>
    )

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
              {settled.length > 0 && (
                <>
                  {' · '}
                  <span className={`font-mono font-semibold ${pl > 0 ? 'text-emerald' : pl < 0 ? 'text-rose' : 'text-ink'}`}>
                    {pl >= 0 ? '+' : '−'}
                    {cash(pl)}
                  </span>
                </>
              )}
            </>
          ) : (
            bush ? 'bush meeting: no bets' : started ? 'no bets logged for this race' : 'no bets in this race'
          )}
        </span>
      </div>
      {halved && <div className="pt-1 text-[11px] font-medium text-amber">Heavy track: stakes halved</div>}
      <div className="divide-y divide-line-soft">
        {loggedRow(lw)}
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
        {loggedRow(lq)}
        {quin && !quin.skip && (
          <Row tag="QUIN" stake={fmt(quin.stake)} note={pct(quin.stake, quin.combos)}>
            <div className="flex items-center gap-1.5">
              <span className="w-7 flex-none text-[11px] text-ink-mute">box</span>
              <Chips sel={quin.box} />
            </div>
          </Row>
        )}
        {loggedRow(lt)}
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
        {loggedRow(le)}
        {earlyQuad && !earlyQuad.skip && quadRow('EARLY', earlyQuad)}
        {loggedRow(lm)}
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
