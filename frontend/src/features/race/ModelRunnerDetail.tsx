import type { Runner } from '../../types/domain'
import type { RMBlend, RMRunner } from '../../lib/racingModel'
import { fmtPrice, fmtWpr } from '../../lib/format'

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

export function ModelHeadline({ runner, detail, scratched }: { runner: Runner; detail: ModelDetail; scratched: boolean }) {
  const { m, blend, settleRank, rank, fieldSize } = detail
  const edge = scratched ? null : (blend?.edge ?? null)
  return (
    <div className="rounded-lg bg-bg p-2.5">
      <div className="flex flex-wrap items-baseline gap-x-3 gap-y-1">
        {scratched ? (
          <span className="font-mono text-2xl font-bold text-rose">SCR</span>
        ) : (
          <span className="font-mono text-2xl font-bold text-emerald-deep">{fmtWpr(m.r)}</span>
        )}
        <span className="text-xs text-ink-mute">Racing Model rating (projected WPR)</span>
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
      {!scratched && (
        <div className="mt-2 flex flex-wrap items-center gap-x-3 gap-y-0.5">
          <Stat label="vs field" value={signed(m.v)} className={tone(m.v)} />
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
      <p className="mt-2 border-t border-line-soft pt-2 text-xs text-ink-faint">
        Model $ is the Racing Model alone; blend combines it with the current fixed price; edge = blend chance x
        fixed price - 1. Settle = projected position at the 800m.
      </p>
    </div>
  )
}

export function ModelBreakdown({ detail }: { detail: ModelDetail }) {
  const rows = Object.entries(detail.m.gb ?? {})
    .filter(([, v]) => Math.abs(v) >= 0.05)
    .sort((a, b) => Math.abs(b[1]) - Math.abs(a[1]))
  if (!rows.length) return null
  const maxAbs = Math.max(1, ...rows.map(([, v]) => Math.abs(v)))
  return (
    <div>
      <div className="mb-1.5 text-xs font-semibold text-ink">What&apos;s driving the rating</div>
      <div className="space-y-0.5">
        {rows.map(([key, v]) => (
          <div key={key} className="flex items-center gap-1.5 border-b border-line-soft/60 py-1 last:border-0">
            <div className="min-w-0 flex-1 text-xs text-ink">{key}</div>
            <div className="relative h-1.5 w-10 flex-none rounded-full bg-line-soft">
              <div
                className={`absolute top-0 bottom-0 rounded-full ${v > 0 ? 'left-1/2 bg-emerald-deep' : 'right-1/2 bg-rose'}`}
                style={{ width: `${Math.min(48, (Math.abs(v) / maxAbs) * 48)}%` }}
              />
            </div>
            <div className={`w-9 flex-none text-right font-mono text-xs font-semibold ${v > 0 ? 'text-emerald-deep' : 'text-rose'}`}>
              {signed(v)}
            </div>
          </div>
        ))}
        <div className="flex items-center gap-1.5 border-t border-line-soft pt-1.5 font-semibold text-ink">
          <div className="flex-1 text-xs">vs field (WPR points)</div>
          <div className="w-10 flex-none" />
          <div className="w-9 flex-none text-right font-mono text-xs">{signed(detail.m.v)}</div>
        </div>
      </div>
    </div>
  )
}
