import { useMemo } from 'react'
import type { Race } from '../../types/domain'
import type { StrategyPick } from '../../lib/strategyPicks'
import type { StrategyTier } from '../../lib/jtComboStrategy'

interface StrategyScoreboardProps {
  races: Race[]
  picks: Record<string, StrategyPick>
}

// 1 unit = $50, matching the dashboard-wide staking convention.
const UNIT_VALUE_DOLLARS = 50

interface TierStats {
  taken: number
  pending: number
  resulted: number
  wins: number
  profit: number
}

function emptyStats(): TierStats {
  return { taken: 0, pending: 0, resulted: 0, wins: 0, profit: 0 }
}

export function StrategyScoreboard({ races, picks }: StrategyScoreboardProps) {
  const stats = useMemo(() => {
    const byTier: Record<StrategyTier, TierStats> = {
      'high-volume': emptyStats(),
      'low-volume': emptyStats(),
      closers: emptyStats(),
    }
    const pickList = Object.values(picks)
    if (pickList.length === 0) return byTier

    const runnerById = new Map<string, { won: boolean; startingPrice: number | null; fixedWinPrice: number | null }>()
    const raceById = new Map<string, Race>()
    for (const race of races) {
      raceById.set(race.raceId, race)
      for (const r of race.runners) {
        runnerById.set(r.runId, { won: r.won, startingPrice: r.startingPrice, fixedWinPrice: r.fixedWinPrice })
      }
    }

    for (const pick of pickList) {
      const s = byTier[pick.tier]
      s.taken += 1
      const race = raceById.get(pick.raceId)
      const runner = runnerById.get(pick.runId)
      if (!race || !runner || !race.allResulted) {
        s.pending += 1
        continue
      }
      s.resulted += 1
      const price = runner.startingPrice ?? runner.fixedWinPrice
      if (runner.won) {
        s.wins += 1
        if (price != null) s.profit += price - 1
      } else {
        if (price != null) s.profit -= 1
      }
    }
    return byTier
  }, [races, picks])

  const totalTaken = stats['high-volume'].taken + stats['low-volume'].taken + stats.closers.taken
  if (totalTaken === 0) return null

  return (
    <div className="rounded-lg border border-line bg-panel px-3 py-2.5 text-sm">
      <div className="mb-1.5 text-xs font-medium text-ink-mute">Your tracked bets (forward performance, not backtest)</div>
      <div className="flex flex-wrap gap-x-8 gap-y-2">
        {(['high-volume', 'low-volume', 'closers'] as StrategyTier[]).map((tier) => {
          const s = stats[tier]
          if (s.taken === 0) return null
          const strike = s.resulted > 0 ? (s.wins / s.resulted) * 100 : null
          const roi = s.resulted > 0 ? (s.profit / s.resulted) * 100 : null
          const label = tier === 'high-volume' ? 'High volume' : tier === 'low-volume' ? 'Low volume' : 'Closers'
          return (
            <div key={tier}>
              <div className="text-xs text-ink-mute">{label}</div>
              <div className="font-mono text-ink">
                {s.taken} taken{s.pending > 0 ? ` (${s.pending} pending)` : ''}
                {s.resulted > 0 && (
                  <>
                    {' · '}
                    {s.wins}/{s.resulted} won ({strike!.toFixed(1)}%){' · '}
                    <span className={roi! >= 0 ? 'font-semibold text-emerald-deep' : 'font-semibold text-rose'}>
                      {s.profit >= 0 ? '+' : ''}${(s.profit * UNIT_VALUE_DOLLARS).toFixed(0)} ({roi! >= 0 ? '+' : ''}
                      {roi!.toFixed(1)}%)
                    </span>
                  </>
                )}
              </div>
            </div>
          )
        })}
      </div>
    </div>
  )
}
