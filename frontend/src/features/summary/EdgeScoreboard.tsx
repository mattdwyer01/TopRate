import { useMemo } from 'react'
import type { Race } from '../../types/domain'
import type { StrategyPick } from '../../lib/strategyPicks'
import type { EdgeTier } from '../../lib/edgeOverlay'

interface EdgeScoreboardProps {
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

// Real forward performance of picks actually taken, by edge-tier - this is
// what should be trusted over any hardcoded backtest claim (see
// edgeOverlay.ts's file header on why a backtested number alone burned this
// exact tab once already). Replaces StrategyScoreboard.tsx.
export function EdgeScoreboard({ races, picks }: EdgeScoreboardProps) {
  const stats = useMemo(() => {
    const byTier: Record<EdgeTier, TierStats> = {
      'edge-8': emptyStats(),
      'edge-10': emptyStats(),
      'edge-13': emptyStats(),
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
      if (!s) continue // stale pick from before the tier enum changed - skip rather than crash
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

  const totalTaken = stats['edge-8'].taken + stats['edge-10'].taken + stats['edge-13'].taken
  if (totalTaken === 0) return null

  const TIER_LABEL: Record<EdgeTier, string> = { 'edge-8': '8%+ edge', 'edge-10': '10%+ edge', 'edge-13': '13%+ edge' }

  return (
    <div className="rounded-lg border border-line bg-panel px-3 py-2.5 text-sm">
      <div className="mb-1.5 text-xs font-medium text-ink-mute">Your tracked bets (forward performance, not backtest)</div>
      <div className="flex flex-wrap gap-x-8 gap-y-2">
        {(['edge-8', 'edge-10', 'edge-13'] as EdgeTier[]).map((tier) => {
          const s = stats[tier]
          if (s.taken === 0) return null
          const strike = s.resulted > 0 ? (s.wins / s.resulted) * 100 : null
          const roi = s.resulted > 0 ? (s.profit / s.resulted) * 100 : null
          return (
            <div key={tier}>
              <div className="text-xs text-ink-mute">{TIER_LABEL[tier]}</div>
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
