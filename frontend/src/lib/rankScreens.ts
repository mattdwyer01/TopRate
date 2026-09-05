import type { Race, Runner } from '../types/domain'
import { BUSH_TRACK_THRESHOLD } from './meetings'

// Three volume tiers of ONE validated rule (Sep 2026, see
// wpr_rank_conjunction_screen_v9_deduped.py in the repo root): jockey_win_
// pct_90d AND trainer_win_pct_365d both above a cutoff, with the market
// price capped at $15 to keep it staking-sane. Tiers vary only the
// cutoff (18/20/22%) to trade selectivity for volume - no rank
// condition (WPR, sect_i_time, or recent-form ewm5) is part of this rule.
//
// This is a full redesign, not a tuning pass, of the original rank-
// conjunction rule (form/ewm5 rank AND jockey/trainer>=15%) shipped
// earlier this same session. That rule was invalidated after discovering
// wpr_form_history.csv.gz is 42% duplicate (horse, date) rows (a WPR
// rebaseline re-scrape issue toprate_daily.py already dedupes for the
// Race tab's form-history display, but which none of v1-v8's ewm5/
// sect_i_time computations did) - fixing the duplication alone flipped
// every rank-based tier from solidly positive to solidly negative ROI.
// Re-running the full signal search (v9, on deduplicated data, large
// chronological H1/H2 halves) found EVERY rank signal (WPR, sect_i_time,
// form) is NEGATIVE alone or in combination, at every threshold tried -
// the only genuinely robust, both-halves-positive finding left is
// jockey/trainer on their own, and only once the cutoff is raised to
// 18%+ (15% fails clean data: H1 -5.9%, H2 +0.9%). Checked live against
// the real last 30 days: still positive at all three cutoffs, though (as
// with every check this session) smaller and noisier than the H1/H2
// historical split - the usual pattern for a rule mined by search.
export const RANK_SCREEN_PRICE_CAP = 15

export type RankScreenTierId = 'targeted' | 'mid' | 'high'

export interface RankScreenTier {
  id: RankScreenTierId
  label: string
  cutoffPct: number
  description: string
}

export const RANK_SCREEN_TIERS: RankScreenTier[] = [
  {
    id: 'targeted',
    label: 'Targeted',
    cutoffPct: 22,
    description: 'Jockey (90-day) and trainer (365-day) win% both >=22%, price <=$15 - fewest bets, best backtested ROI.',
  },
  {
    id: 'mid',
    label: 'Mid volume',
    cutoffPct: 20,
    description: 'Jockey and trainer win% both >=20%, price <=$15 - a middle ground on volume vs selectivity.',
  },
  {
    id: 'high',
    label: 'High volume',
    cutoffPct: 18,
    description: 'Jockey and trainer win% both >=18%, price <=$15 - most bets, lower average edge per bet.',
  },
]

export interface RankScreenRow {
  raceId: string
  runId: string
  date: string
  venue: string
  horse: string
  price: number
  jockeyWinPct90d: number | null
  trainerWinPct365d: number | null
  // false/false (not yet won-or-placed), NOT unknown, when resulted is
  // false - see collectRankScreenRows and computeRankScreenStats, which
  // both key off `resulted`, never off won/placed alone, to decide
  // whether a row counts toward the strike rate/ROI stats.
  resulted: boolean
  won: boolean
  placed: boolean
}

// Three ways to slice by date: one single calendar day (Today by default,
// with Yesterday/Tomorrow/an arbitrary date - same quick-nav convention as
// MeetingsGrid's date picker, so today's actual qualifying picks are the
// first thing this tab shows, not a historical backtest), the usual
// rolling window (matches signalWatch.ts/accuracyStats.ts's Period), or
// "last N occurrences of this weekday" - added so a specific validation
// check done during this rule's research (checking results against the
// real last 4 actual Saturdays, since that's the day most of the
// meaningful racing falls on) can be reproduced live on the dashboard
// instead of needing a one-off script.
export type RankScreenDateFilter =
  | { mode: 'day'; date: string } // "YYYY-MM-DD"
  | { mode: 'period'; period: 'all' | '90' | '30' }
  | { mode: 'weekday'; weekday: number; count: number } // weekday: 0=Sun..6=Sat

export interface RankScreenFilters {
  dateFilter: RankScreenDateFilter
  excludeBush: boolean
}

function dateOnly(s: string): string {
  return s.slice(0, 10)
}

/** The last `count` calendar dates (today included) that fall on `weekday`,
 * as "YYYY-MM-DD" strings - computed by walking back from today one day at a
 * time rather than doing modular date arithmetic, since that's trivially
 * correct across month/year boundaries and DST doesn't apply to plain
 * calendar dates. Built once per render, not per-race. */
export function lastNWeekdayDates(weekday: number, count: number): Set<string> {
  const dates = new Set<string>()
  const now = new Date()
  const cursor = new Date(Date.UTC(now.getUTCFullYear(), now.getUTCMonth(), now.getUTCDate()))
  let guard = 0
  while (dates.size < count && guard < 3660) {
    if (cursor.getUTCDay() === weekday) dates.add(cursor.toISOString().slice(0, 10))
    cursor.setUTCDate(cursor.getUTCDate() - 1)
    guard += 1
  }
  return dates
}

function buildDateMatcher(filter: RankScreenDateFilter): (raceDate: string) => boolean {
  if (filter.mode === 'day') {
    return (raceDate) => dateOnly(raceDate) === filter.date
  }
  if (filter.mode === 'period') {
    if (filter.period === 'all') return () => true
    const cutoff = Date.now() - Number(filter.period) * 86_400_000
    return (raceDate) => new Date(raceDate).getTime() >= cutoff
  }
  const dates = lastNWeekdayDates(filter.weekday, filter.count)
  return (raceDate) => dates.has(dateOnly(raceDate))
}

function meetsCutoff(r: Runner, cutoffPct: number): boolean {
  return (r.jockeyWinPct90d ?? -Infinity) >= cutoffPct && (r.trainerWinPct365d ?? -Infinity) >= cutoffPct
}

/** Same bush-track filtering convention as signalWatch.ts/accuracyStats.ts,
 * applied independently so this feature can't regress either pipeline. */
export function collectRankScreenRows(races: Race[], tierId: RankScreenTierId, filters: RankScreenFilters): RankScreenRow[] {
  const tier = RANK_SCREEN_TIERS.find((t) => t.id === tierId) ?? RANK_SCREEN_TIERS[0]
  const matchesDate = buildDateMatcher(filters.dateFilter)
  const rows: RankScreenRow[] = []
  for (const race of races) {
    if (!matchesDate(race.date)) continue
    if (filters.excludeBush && (race.prizeMoney ?? 0) <= BUSH_TRACK_THRESHOLD) continue

    for (const r of race.runners) {
      if (r.dataScratched) continue
      if (!meetsCutoff(r, tier.cutoffPct)) continue
      const price = r.fixedWinPrice ?? r.startingPrice
      if (price == null || price <= 1 || price > RANK_SCREEN_PRICE_CAP) continue
      // Not-yet-resulted runners (today's/tomorrow's races) are kept, not
      // skipped - a "Today" view needs to show today's qualifying picks
      // before they've run, not just backtested history. computeRankScreenStats
      // below is the thing that must never count them as a loss.
      const resulted = r.finishPosition != null

      rows.push({
        raceId: race.raceId,
        runId: r.runId,
        date: race.date,
        venue: race.venue,
        horse: r.horse,
        price,
        jockeyWinPct90d: r.jockeyWinPct90d,
        trainerWinPct365d: r.trainerWinPct365d,
        resulted,
        won: resulted && r.won,
        placed: resulted && r.finishPosition! >= 1 && r.finishPosition! <= 3,
      })
    }
  }
  return rows
}

export interface RankScreenStats {
  n: number // resulted rows only - the population strikePct/roiPct/avgPrice are computed over
  pendingN: number // qualifying rows still awaiting a result (today's/tomorrow's picks)
  strikePct: number | null
  placeStrikePct: number | null
  roiPct: number | null
  avgPrice: number | null
}

/** Same proportional-return convention as signalWatch.ts's computeSignalWatchStats.
 * Only resulted rows count toward strike rate/ROI/avg price - an
 * unresulted (pending) row is neither a win nor a loss yet, so counting
 * it as a loss (its won/placed both default false) would understate
 * every stat the moment "today" or "tomorrow" is selected. */
export function computeRankScreenStats(rows: RankScreenRow[]): RankScreenStats {
  const resultedRows = rows.filter((r) => r.resulted)
  const pendingN = rows.length - resultedRows.length
  if (resultedRows.length === 0) {
    return { n: 0, pendingN, strikePct: null, placeStrikePct: null, roiPct: null, avgPrice: null }
  }
  let wins = 0
  let places = 0
  let profit = 0
  let priceSum = 0
  for (const r of resultedRows) {
    priceSum += r.price
    if (r.won) {
      wins += 1
      profit += r.price - 1
    } else {
      profit -= 1
    }
    if (r.placed) places += 1
  }
  return {
    n: resultedRows.length,
    pendingN,
    strikePct: (wins / resultedRows.length) * 100,
    placeStrikePct: (places / resultedRows.length) * 100,
    roiPct: (profit / resultedRows.length) * 100,
    avgPrice: priceSum / resultedRows.length,
  }
}

/** For badging a single race's runners on the Race tab: the most
 * selective tier (Targeted > Mid > High) each non-scratched runner
 * qualifies for right now, keyed by runId. Since the tiers are nested
 * (a higher cutoff also clears the lower ones), a runner only ever gets
 * its BEST tier - no need to show three badges on one horse. Works
 * identically whether the race has resulted or not, so today's/
 * tomorrow's fields get badges too, not just settled ones. */
export function qualifyingTierForRace(race: Race): Map<string, RankScreenTierId> {
  const result = new Map<string, RankScreenTierId>()
  for (const r of race.runners) {
    if (r.dataScratched) continue
    const price = r.fixedWinPrice ?? r.startingPrice
    if (price == null || price <= 1 || price > RANK_SCREEN_PRICE_CAP) continue
    const tier = RANK_SCREEN_TIERS.find((t) => meetsCutoff(r, t.cutoffPct))
    if (tier) result.set(r.runId, tier.id)
  }
  return result
}
