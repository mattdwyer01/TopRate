import { useEffect, useState } from 'react'
import type { Race } from '../types/domain'
import type { ModelSpeedMap } from '../features/race/SpeedMapGrid'

// Racing Model layer (Sep 2026): a second, independent model's projections, produced daily by the
// racing-model repo (mattdwyer01/racing-model, tools/dashboard_export.py) and committed here as
// racing_model.json. Optional: if the file is missing or fails to load, nothing in the dashboard changes.
//
// Per runner it carries the model's own win probability (no market input). The blend with the market is
// recomputed here from the CURRENT fixed prices on every data refresh, using the blend weights the
// racing model fitted walk-forward: p_blend ~ exp(a ln p_model + b ln p_market), normalised per race.

export interface RMRunner {
  r: number | null // projected rating (WPR points, absolute)
  v: number | null // rating vs the field average
  p: number | null // model win probability (market-free)
  s: number | null // projected settle share, 0 = leader, 1 = last (v4 model)
  l: number | null // P(leads) from the race simulation
  g: number | null // projected extra ground vs the field (m)
  d: number | null // race-day adjustment (WPR points: projection + track bias)
  ab: number | null // ability contribution (WPR points vs field)
  jt: number | null // jockey / trainer contribution (WPR points vs field)
  pv?: number | null // position value: expected worth of the projected position and width (WPR points vs race)
  pf?: number // 1 = position value in the top 10% (the group the market has underrated in testing)
}

export interface RMRace {
  pace: [number, number, number] | null // P(slow, even, fast)
  pv: number | null // projected pace vs the distance average (GPS pace units)
  on: string | null // date the projection was made (always before the race)
  // projected track bias as the model applies it (from past meetings at the track, long-run + recent same rail):
  // lead = WPR edge of a leader over a backmarker, inside = of the inside draw over the outside draw
  bias?: { lead: number; inside: number } | null
}

// Plain-words reading of a race's projected bias; values under 0.25 WPR count as neutral.
export function biasText(b: { lead: number; inside: number } | null | undefined): { pos: string; draw: string; tone: 'strong' | 'mild' | 'neutral' } | null {
  if (!b) return null
  const f = (v: number) => `${Math.abs(v).toFixed(1)} WPR`
  const pos = Math.abs(b.lead) < 0.25 ? 'position neutral' : b.lead > 0 ? `leaders favoured (+${f(b.lead)})` : `backmarkers favoured (+${f(b.lead)})`
  const draw = Math.abs(b.inside) < 0.25 ? 'draw neutral' : b.inside > 0 ? `inside draw favoured (+${f(b.inside)})` : `wide draw favoured (+${f(b.inside)})`
  const m = Math.max(Math.abs(b.lead), Math.abs(b.inside))
  return { pos, draw, tone: m >= 1 ? 'strong' : m >= 0.25 ? 'mild' : 'neutral' }
}

export interface RMPayload {
  generated: string
  trainEnd: string
  a: number
  b: number
  posFlagThreshold?: number | null
  races: Record<string, RMRace>
  runners: Record<string, RMRunner>
}

export interface RMBlend {
  blendProb: number
  blendPrice: number
  edge: number | null // blendProb x fixed price - 1
}

const FILE = 'racing_model.json'
const REFRESH_MS = 10 * 60_000

let cached: Promise<RMPayload | null> | null = null

function load(force = false): Promise<RMPayload | null> {
  if (!cached || force) {
    cached = fetch(FILE, { cache: 'no-cache' })
      .then((r) => (r.ok ? (r.json() as Promise<RMPayload>) : null))
      .catch(() => null)
  }
  return cached
}

// Shared across every component that asks: one fetch, refreshed every 10 minutes (the file itself only
// changes when the racing model's daily job runs).
export function useRacingModel(): RMPayload | null {
  const [data, setData] = useState<RMPayload | null>(null)
  useEffect(() => {
    let alive = true
    load().then((d) => alive && setData(d))
    const id = setInterval(() => load(true).then((d) => alive && setData(d)), REFRESH_MS)
    return () => {
      alive = false
      clearInterval(id)
    }
  }, [])
  return data
}

// Blend and edge for one race from the current fixed prices. Needs a model probability and a fixed price
// for every runner still in the race; returns an empty map otherwise (a partial market would misstate the
// blend for everyone).
export function blendRace(race: Race, rm: RMPayload, excluded: Set<string>): Record<string, RMBlend> {
  const field = race.runners.filter((r) => !excluded.has(r.runId))
  const rows = field.map((r) => ({ id: r.runId, pm: rm.runners[r.runId]?.p ?? null, price: r.fixedWinPrice }))
  if (!rows.length || rows.some((x) => x.pm == null || x.pm <= 0 || x.price == null || x.price <= 1)) return {}
  const invSum = rows.reduce((s, x) => s + 1 / (x.price as number), 0)
  const pmSum = rows.reduce((s, x) => s + (x.pm as number), 0)
  const score = rows.map((x) => rm.a * Math.log((x.pm as number) / pmSum) + rm.b * Math.log(1 / (x.price as number) / invSum))
  const top = Math.max(...score)
  const ex = score.map((s) => Math.exp(s - top))
  const tot = ex.reduce((s, x) => s + x, 0)
  const out: Record<string, RMBlend> = {}
  rows.forEach((x, i) => {
    const bp = ex[i] / tot
    out[x.id] = { blendProb: bp, blendPrice: 1 / bp, edge: bp * (x.price as number) - 1 }
  })
  return out
}

// Speed-map input for SpeedMapGrid's Racing Model source: every runner still in the race needs a settle
// projection, otherwise null (a map mixing two models' positions would mislead).
export function modelSpeedMap(race: Race, rm: RMPayload, excluded: Set<string>): ModelSpeedMap | null {
  const field = race.runners.filter((r) => !excluded.has(r.runId))
  if (!field.length || field.some((r) => rm.runners[r.runId]?.s == null)) return null
  const relSettle = new Map<string, number>()
  const rating = new Map<string, number | null>()
  const tone = new Map<string, number | null>()
  // The settle model is a mean projection, so its values bunch toward the middle (few runners projected
  // below 0.2 even when one clearly leads). Stretched across this race's own range so the model's front
  // runner sits in Lead and its last in Back, same scale the grid's columns assume; gaps are kept.
  const ss = field.map((r) => rm.runners[r.runId].s as number)
  const lo = Math.min(...ss)
  const span = Math.max(...ss) - lo
  for (const r of field) {
    const m = rm.runners[r.runId]
    relSettle.set(r.runId, span > 1e-9 ? ((m.s as number) - lo) / span : 0.5)
    rating.set(r.runId, m.r)
    tone.set(r.runId, m.pv ?? null)
  }
  const pace = rm.races[race.raceId]?.pace ?? null
  const names = ['Slow', 'Even', 'Fast'] as const
  const top = pace ? pace.indexOf(Math.max(...pace)) : 1
  const pct = (v: number) => `${Math.round(v * 100)}%`
  return {
    relSettle,
    rating,
    tone,
    toneThreshold: 0.5,
    tempoBucket: names[top],
    paceLabel: pace ? `${names[top]} likely · slow ${pct(pace[0])} even ${pct(pace[1])} fast ${pct(pace[2])}` : 'Pace n/a',
  }
}
