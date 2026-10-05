import { useState } from 'react'
import type { Runner } from '../../types/domain'
import type { RMBlend, RMRunner } from '../../lib/racingModel'
import { fmtPrice, fmtWpr } from '../../lib/format'
import { compositeScore } from '../../lib/raceModel'

// Racing Model part of the runner detail popup (RunnerDetailModal), used whenever the race has Racing Model data
// (6 Oct 2026 layout, user request): headline strip (Proj, rank, fixed price), "How Proj is built" as a waterfall
// (base, race-day adjustments, Proj), running and price tiles, and the explanation
// behind an info toggle. No model / blend / edge figures and no signals (user decision).

export interface ModelDetail {
  m: RMRunner
  blend?: RMBlend
  settleRank: number | null
  rank: number | null
  fieldSize: number
}

const signed = (v: number | null | undefined, d = 1) => (v == null ? '—' : `${v > 0 ? '+' : ''}${v.toFixed(d)}`)
const tone = (v: number | null | undefined, t = 0.05) =>
  v == null ? 'text-ink' : v > t ? 'text-emerald-deep' : v < -t ? 'text-rose' : 'text-ink-faint'

function Tile({ label, value, className = 'text-ink' }: { label: string; value: string; className?: string }) {
  return (
    <div className="rounded-md bg-panel px-2 py-1.5 text-center">
      <div className={`font-mono text-base font-semibold leading-tight ${className}`}>{value}</div>
      <div className="text-[11px] leading-tight text-ink-faint">{label}</div>
    </div>
  )
}

export function ModelHeadline({
  runner,
  detail,
  scratched,
  effectiveWpr,
}: {
  runner: Runner
  detail: ModelDetail
  scratched: boolean
  effectiveWpr?: number | null
}) {
  const { m, settleRank, rank, fieldSize } = detail
  const [info, setInfo] = useState(false)
  const proj = scratched ? null : compositeScore(runner, effectiveWpr)
  const open = runner.openFixedPrice
  const now = runner.fixedWinPrice
  const move = open != null && now != null && open > 1 ? (now / open - 1) * 100 : null
  const flat = move == null || Math.abs(move) < 0.5
  return (
    <div className="rounded-lg bg-bg p-2.5">
      <div className="flex flex-wrap items-center gap-x-3 gap-y-1">
        {scratched ? (
          <span className="font-mono text-3xl font-bold text-rose">SCR</span>
        ) : (
          <span className="font-mono text-3xl font-bold text-emerald-deep">{fmtWpr(proj)}</span>
        )}
        <span className="text-sm text-ink-mute">
          Proj
          {rank != null && !scratched && (
            <>
              {' '}
              · rank <span className="font-semibold text-ink">{rank}</span> of {fieldSize}
            </>
          )}
        </span>
        {now != null && !scratched && (
          <span className="ml-auto rounded-full bg-panel px-2.5 py-0.5 font-mono text-sm font-semibold text-ink">
            {fmtPrice(now)}
          </span>
        )}
        <button
          type="button"
          onClick={() => setInfo((v) => !v)}
          className={`${now != null && !scratched ? '' : 'ml-auto '}flex h-6 w-6 items-center justify-center rounded-full border border-line text-xs text-ink-mute hover:text-ink`}
          aria-label="How this works"
          title="How this works"
        >
          i
        </button>
      </div>
      {info && (
        <p className="mt-2 rounded-md bg-panel p-2 text-xs text-ink-mute">
          Base = the WPR the horse should run on form alone. Each race-day adjustment is WPR points vs this field, learned
          from past races. Proj = base + adjustments: the WPR the horse should run today, the same figure the result is
          compared with. Spread = the typical miss (two runs in three land inside). Settle = projected position at the 800m.
        </p>
      )}
      {!scratched && <ProjBreakdown runner={runner} m={m} effectiveWpr={effectiveWpr} />}
      {!scratched && (
        <div className="mt-2.5">
          <div className="mb-1 text-[11px] font-semibold uppercase tracking-wide text-ink-faint">Running</div>
          <div className="grid grid-cols-4 gap-1.5">
            <Tile label={`settle of ${fieldSize}`} value={settleRank == null ? '—' : String(settleRank)} />
            <Tile label="lead chance" value={m.l == null ? '—' : `${Math.round(m.l * 100)}%`} />
            <Tile label="position value" value={signed(m.pv)} className={tone(m.pv, 0.5)} />
            <Tile label="extra ground m" value={signed(m.g)} />
          </div>
          {now != null && (
            <>
              <div className="mb-1 mt-2 text-[11px] font-semibold uppercase tracking-wide text-ink-faint">Price</div>
              <div className="grid grid-cols-3 gap-1.5">
                <Tile label="fixed now" value={fmtPrice(now)} />
                <Tile label="open" value={fmtPrice(open)} />
                <Tile
                  label="move"
                  value={flat ? 'none' : `${(move as number) > 0 ? '+' : ''}${Math.round(move as number)}%`}
                  className={flat ? 'text-ink-faint' : (move as number) < 0 ? 'text-emerald-deep' : 'text-rose'}
                />
              </div>
            </>
          )}
        </div>
      )}
    </div>
  )
}

function Bar({ v, maxAbs }: { v: number; maxAbs: number }) {
  return (
    <div className="relative h-1.5 w-16 flex-none rounded-full bg-line-soft">
      <div
        className={`absolute top-0 bottom-0 rounded-full ${v > 0 ? 'left-1/2 bg-emerald-deep' : 'right-1/2 bg-rose'}`}
        style={{ width: `${Math.min(50, (Math.abs(v) / maxAbs) * 50)}%` }}
      />
    </div>
  )
}

function AdjRow({ label, v, maxAbs }: { label: string; v: number; maxAbs: number }) {
  return (
    <div className="flex items-center gap-2 py-0.5 text-xs">
      <span className="min-w-0 flex-1 truncate text-ink-mute">{label}</span>
      <Bar v={v} maxAbs={maxAbs} />
      <span className={`w-10 flex-none text-right font-mono font-semibold ${tone(v)}`}>{signed(v)}</span>
    </div>
  )
}

function SubRow({ label, v, total }: { label: string; v: number | null; total?: boolean }) {
  return (
    <div className={`flex items-baseline gap-2 py-0.5 text-xs ${total ? 'mt-0.5 border-t border-line-soft pt-1' : ''}`}>
      <span className={`flex-1 ${total ? 'font-semibold text-ink' : 'text-ink'}`}>{label}</span>
      <span className={`font-mono font-semibold ${total ? 'text-sm text-emerald-deep' : 'text-ink'}`}>{fmtWpr(v)}</span>
    </div>
  )
}

// How Proj is built: base (form-only projected WPR) + each race-day adjustment (+ any manual override) = Proj.
// racing_model.json pb / pa (racing-model model/wpr_model.py). Adjustments under 0.05 fold into one row.
function ProjBreakdown({ runner, m, effectiveWpr }: { runner: Runner; m: RMRunner; effectiveWpr?: number | null }) {
  const [showZero, setShowZero] = useState(false)
  const adj = Object.entries(m.pa ?? {})
  const base = m.pb ?? (m.wp != null ? m.wp - adj.reduce((s, [, v]) => s + v, 0) : null)
  if (base == null) return null
  const own = effectiveWpr ?? runner.projectedWpr
  const override = own != null && m.wp != null ? own - m.wp : 0
  const rows: [string, number][] = adj.map(([k, v]) => [k, v])
  if (Math.abs(override) >= 0.05) rows.push(['Manual override', override])
  const live = rows.filter(([, v]) => Math.abs(v) >= 0.05).sort((a, b) => Math.abs(b[1]) - Math.abs(a[1]))
  const zero = rows.filter(([, v]) => Math.abs(v) < 0.05)
  const total = compositeScore(runner, effectiveWpr) ?? base + rows.reduce((s, [, v]) => s + v, 0)
  const maxAbs = Math.max(1, ...rows.map(([, v]) => Math.abs(v)))
  return (
    <div className="mt-2 rounded-md bg-panel px-2.5 py-2">
      <div className="mb-1 text-[11px] font-semibold uppercase tracking-wide text-ink-faint">How Proj is built</div>
      <SubRow label="Base: projected WPR on form" v={base} />
      {live.map(([k, v]) => (
        <AdjRow key={k} label={k} v={v} maxAbs={maxAbs} />
      ))}
      {zero.length > 0 && (
        <button
          type="button"
          onClick={() => setShowZero((s) => !s)}
          className="flex w-full items-center gap-2 py-0.5 text-left text-xs text-ink-faint hover:text-ink-mute"
        >
          <span className="flex-1">
            {showZero ? '▾' : '▸'} {zero.length} other{zero.length > 1 ? 's' : ''} at 0
          </span>
          <span className="w-10 text-right font-mono">0.0</span>
        </button>
      )}
      {showZero && zero.map(([k, v]) => <AdjRow key={k} label={k} v={v} maxAbs={maxAbs} />)}
      <SubRow label="Proj" v={total} total />
      {m.ws != null && <div className="text-[11px] text-ink-faint">spread ± {Math.round(m.ws)} WPR</div>}
    </div>
  )
}
