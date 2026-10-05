import type { Runner } from '../../types/domain'
import type { RMBlend, RMRunner } from '../../lib/racingModel'
import { fmtPrice, fmtWpr } from '../../lib/format'
import { signalList, VALUE_CUT, VALUE_MAX_PRICE } from '../../lib/signals'
import { compositeScore } from '../../lib/raceModel'

// Racing Model parts of the runner detail popup (RunnerDetailModal), used whenever the race has a Racing Model
// projection: the headline rating block and the rating breakdown (WPR points vs the field, from
// racing_model.json runners[].gb; the parts sum to "vs field").

export interface ModelDetail {
  m: RMRunner
  blend?: RMBlend
  settleRank: number | null
  rank: number | null
  fieldSize: number
}

const signed = (v: number | null | undefined, d = 1) => (v == null ? '—' : `${v > 0 ? '+' : ''}${v.toFixed(d)}`)
const tone = (v: number | null | undefined, t = 0) =>
  v == null ? 'text-ink' : v > t ? 'text-emerald-deep' : v < -t ? 'text-rose' : 'text-ink'

function Stat({ label, value, className = 'text-ink' }: { label: string; value: string; className?: string }) {
  return (
    <span className="text-xs text-ink-mute">
      <span className={`font-mono font-semibold ${className}`}>{value}</span> {label}
    </span>
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
  const { m, blend, settleRank, rank, fieldSize } = detail
  const edge = scratched ? null : (blend?.edge ?? null)
  const proj = scratched ? null : compositeScore(runner, effectiveWpr)
  return (
    <div className="rounded-lg bg-bg p-2.5">
      <div className="flex flex-wrap items-baseline gap-x-3 gap-y-1">
        {scratched ? (
          <span className="font-mono text-2xl font-bold text-rose">SCR</span>
        ) : (
          <span className="font-mono text-2xl font-bold text-emerald-deep">{fmtWpr(proj)}</span>
        )}
        <span className="text-xs text-ink-mute">Proj (projected WPR + race-day adjustments + price)</span>
        {rank != null && !scratched && (
          <span className="text-xs text-ink-mute">
            rank <span className="font-mono font-semibold text-ink">{rank}</span> of {fieldSize}
          </span>
        )}
        {m.pf === 1 && !scratched && (
          <span className="rounded-full bg-indigo-bg px-2 py-0.5 text-xs font-medium text-indigo" title="Position value in the top 10%">
            ◆ position value
          </span>
        )}
      </div>
      {!scratched && <ProjBreakdown runner={runner} m={m} effectiveWpr={effectiveWpr} />}
      {!scratched && (
        <div className="mt-2 flex flex-wrap items-center gap-x-3 gap-y-0.5">
          <Stat label="Racing Model rating" value={fmtWpr(runner.rmWpr ?? m.r)} />
          <Stat label="model" value={fmtPrice(m.p ? 1 / m.p : null)} />
          <Stat label="blend" value={fmtPrice(blend?.blendPrice)} />
          <Stat label="fixed" value={fmtPrice(runner.fixedWinPrice)} />
          <Stat
            label="edge"
            value={edge == null ? '—' : `${edge > 0 ? '+' : ''}${Math.round(edge * 100)}%`}
            className={edge != null && edge > 0 ? 'text-emerald-deep' : 'text-ink'}
          />
        </div>
      )}
      {!scratched && (
        <div className="mt-1 flex flex-wrap items-center gap-x-3 gap-y-0.5">
          <Stat label={`settle (of ${fieldSize})`} value={settleRank == null ? '—' : String(settleRank)} />
          <Stat label="chance of leading" value={m.l == null ? '—' : `${Math.round(m.l * 100)}%`} />
          <Stat label="position value" value={signed(m.pv)} className={tone(m.pv, 0.5)} />
          {m.g != null && <Stat label="m extra ground (proj.)" value={signed(m.g)} />}
        </div>
      )}
      {!scratched && <SignalsBlock runner={runner} />}
      <p className="mt-2 border-t border-line-soft pt-2 text-xs text-ink-faint">
        Base = the WPR the horse should run on form alone (+/- its typical miss: two runs in three land inside). Each
        race-day adjustment is WPR points vs this field, learned from past races; the price adjustment is 2 x log price vs
        the field. Model $ is the Racing Model alone; blend combines it with the current fixed price; edge = blend chance x
        fixed price - 1. Settle = projected position at the 800m.
      </p>
    </div>
  )
}

// How Proj is built (6 Oct 2026, user request): base (form-only projected WPR) + each race-day adjustment + the price
// adjustment = the headline figure. racing_model.json pb / pa (racing-model model/wpr_model.py), runner.mktAdj.
function ProjBreakdown({ runner, m, effectiveWpr }: { runner: Runner; m: RMRunner; effectiveWpr?: number | null }) {
  const adj = Object.entries(m.pa ?? {})
  const own = effectiveWpr ?? runner.projectedWpr
  const override = own != null && m.wp != null ? own - m.wp : 0
  const rows: [string, number | null, boolean?][] = [
    ['Base: projected WPR on form', m.pb ?? (m.wp != null ? m.wp - adj.reduce((s, [, v]) => s + v, 0) : null), true],
    ...adj.map(([k, v]) => [k, v] as [string, number]),
  ]
  if (Math.abs(override) >= 0.05) rows.push(['Manual override', override])
  if (runner.mktAdj != null) rows.push(['Price adjustment', runner.mktAdj])
  const total = compositeScore(runner, effectiveWpr)
  if (rows[0][1] == null) return null
  return (
    <div className="mt-2 border-t border-line-soft pt-2">
      <div className="mb-1 text-xs font-semibold text-ink">How Proj is built</div>
      <div className="space-y-0.5">
        {rows.map(([k, v, isBase]) => (
          <div key={k} className="flex items-baseline gap-1.5 text-xs">
            <span className={isBase ? 'text-ink' : 'text-ink-mute'}>{k}</span>
            <span
              className={`ml-auto font-mono font-semibold ${isBase ? 'text-ink' : v != null && Math.abs(v) >= 0.05 ? tone(v) : 'text-ink-faint'}`}
            >
              {isBase ? fmtWpr(v) : signed(v)}
            </span>
          </div>
        ))}
        <div className="flex items-baseline gap-1.5 border-t border-line-soft pt-1 text-xs font-semibold text-ink">
          <span>Proj</span>
          <span className="ml-auto font-mono">{fmtWpr(total)}</span>
        </div>
        {m.ws != null && <div className="text-[11px] text-ink-faint">spread +/- {Math.round(m.ws)} WPR</div>}
      </div>
    </div>
  )
}

// Market signals (lib/signals.ts) and the value model's verdict at the current fixed price.
function SignalsBlock({ runner }: { runner: Runner }) {
  const list = signalList(runner.signals)
  const v = runner.valueNow
  if (!list.length && v == null) return null
  const isValue = v != null && v >= VALUE_CUT && (runner.fixedWinPrice ?? 0) <= VALUE_MAX_PRICE
  return (
    <div className="mt-2 border-t border-line-soft pt-2">
      <div className="mb-1 flex flex-wrap items-baseline gap-x-2 text-xs">
        <span className="font-semibold text-ink">Market signals</span>
        {v != null && (
          <span className={isValue ? 'font-semibold text-emerald-deep' : 'text-ink-mute'}>
            value {v.toFixed(2)} at {fmtPrice(runner.fixedWinPrice)}
            {isValue ? ' (value bet)' : ' (needs 1.00)'}
          </span>
        )}
      </div>
      {list.length > 0 && (
        <ul className="space-y-0.5">
          {list.map(({ code, info }) => (
            <li key={code} className="flex items-baseline gap-1.5 text-xs">
              <span className={`inline-block h-1.5 w-1.5 flex-none translate-y-[-1px] rounded-full ${info.effect > 0 ? 'bg-emerald' : 'bg-rose'}`} />
              <span className="text-ink">{info.label}</span>
              <span className="text-ink-faint">{info.detail}</span>
              <span className={`ml-auto font-mono font-semibold ${info.effect > 0 ? 'text-emerald-deep' : 'text-rose'}`}>
                {info.effect > 0 ? '+' : ''}
                {Math.round(info.effect * 100)}%
              </span>
            </li>
          ))}
        </ul>
      )}
    </div>
  )
}
