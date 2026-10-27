import { useEffect, useState } from 'react'
import type { Race, Runner } from '../types/domain'

// Draw and style card data (draw_style.py, Oct 2026): per venue, every priced runner since 2017 as a compact row so the card can filter by distance, rail, going and
// race pace in the browser. Files are data/venue_draw/<slug>.json.gz with data/venue_draw/index.json mapping venue names to them. Optional: no file, no card.

export const STYLE_EDGES = [0.15, 0.3, 0.42, 0.55, 0.7] // L, OP, OP/MF, MF, MF/BM, BM (share of the field at 800m, 0 = led)
export const STYLE_NAMES = ['L', 'OP', 'OP/MF', 'MF', 'MF/BM', 'BM']
export const FORWARD_MAX = 0.3 // a runner whose average position is at or under this counts as a Forward-style runner in the race pace count

// row = [barrier (16 = 16 and wider), style 0-5, distance group 0-2, rail -1..3, going -1..6, race pace 0-2, won, normalised price-implied chance]
export type DrawRow = [number, number, number, number, number, number, number, number]

// [rating points inside to widest, its se, runners, rating points per barrier step wider, its se]
export type SlopeEntry = [number, number, number, number, number]
export interface RatingSlope {
  [k: string]: SlopeEntry | undefined
}

export interface VenueDraw {
  venue: string
  runners: number
  races: number
  from: string
  through: string
  rating: RatingSlope // draw slope of the within-race ATW rating by distance group (keys '0' '1' '2') and 'all'
  rows: DrawRow[]
}

interface Index {
  through: string
  aliases: Record<string, string>
}

const BASE = 'data/venue_draw/'
let indexPromise: Promise<Index | null> | null = null
const venues = new Map<string, Promise<VenueDraw | null>>()

function loadIndex(): Promise<Index | null> {
  if (!indexPromise) {
    indexPromise = fetch(`${BASE}index.json`)
      .then((r) => (r.ok ? (r.json() as Promise<Index>) : null))
      .catch(() => null)
  }
  return indexPromise
}

async function gunzip(res: Response): Promise<string> {
  // GitHub Pages may already have undone the gzip (Content-Encoding); only decompress raw gzip bytes.
  if (res.headers.get('content-encoding') === 'gzip') return res.text()
  if (typeof DecompressionStream === 'undefined') throw new Error('no DecompressionStream')
  return new Response(res.body!.pipeThrough(new DecompressionStream('gzip'))).text()
}

function loadVenue(slug: string): Promise<VenueDraw | null> {
  let p = venues.get(slug)
  if (!p) {
    p = fetch(`${BASE}${slug}.json.gz`)
      .then(async (r) => (r.ok ? (JSON.parse(await gunzip(r)) as VenueDraw) : null))
      .catch(() => null)
    venues.set(slug, p)
  }
  return p
}

// The race's venue file, or null while loading / when the venue has none. One fetch per venue, shared.
export function useVenueDraw(venue: string): VenueDraw | null {
  const [data, setData] = useState<VenueDraw | null>(null)
  useEffect(() => {
    let alive = true
    setData(null)
    loadIndex()
      .then((ix) => {
        const slug = ix?.aliases[venue.trim().toLowerCase()]
        return slug ? loadVenue(slug) : null
      })
      .then((d) => alive && setData(d))
    return () => {
      alive = false
    }
  }, [venue])
  return data
}

export function styleIndex(avg: number): number {
  let i = 0
  while (i < STYLE_EDGES.length && avg > (STYLE_EDGES[i] as number)) i++
  return i
}

export function distanceGroup(m: number): number {
  return m <= 1300 ? 0 : m <= 1650 ? 1 : 2
}

// 0 true, 1 out 1-4m, 2 out 5-9m, 3 out 10m+, -1 unknown
export function railGroup(rail: string | null): number {
  const s = (rail ?? '').trim()
  if (!s) return -1
  if (/^true/i.test(s)) return 0
  const m = /(\d+)\s*m/i.exec(s)
  if (!m) return -1
  const k = Number(m[1])
  return k <= 4 ? 1 : k <= 9 ? 2 : 3
}

// 0 Firm, 1 Good 3 and better, 2 Good 4, 3 Soft 5, 4 Soft 6, 5 Soft 7, 6 Heavy, -1 unknown (synthetic)
export function goingGroup(going: string): number {
  const m = /^(Firm|Good|Soft|Heavy)\s*(\d+)?/i.exec(going.trim())
  if (!m) return -1
  const k = (m[1] as string).toLowerCase()
  const n = Number(m[2] ?? 0)
  if (k === 'firm') return 0
  if (k === 'good') return n <= 3 ? 1 : 2
  if (k === 'soft') return n <= 5 ? 3 : n === 6 ? 4 : 5
  return 6
}

export function paceGroup(forward: number): number {
  return forward >= 4 ? 2 : forward >= 2 ? 1 : 0
}

export const DISTANCE_LABELS = ['Up to 1300m', '1301-1650m', 'Over 1650m']
export const RAIL_LABELS = ['Rail true', 'Out 1-4m', 'Out 5-9m', 'Out 10m+']
export const GOING_LABELS = ['Firm', 'Good 3', 'Good 4', 'Soft 5', 'Soft 6', 'Soft 7', 'Heavy']
export const PACE_LABELS = ['Few leaders', 'Some leaders', 'Many leaders']

export interface Conditions {
  d: number | null
  r: number | null
  g: number | null
  p: number | null
}

export function raceConditions(race: Race, active: Runner[]): Conditions {
  const forward = active.filter((r) => r.styleAvg != null && r.styleAvg <= FORWARD_MAX).length
  const some = active.some((r) => r.styleAvg != null)
  const r = railGroup(race.rail)
  const g = goingGroup(race.going)
  return { d: distanceGroup(race.distance), r: r < 0 ? null : r, g: g < 0 ? null : g, p: some ? paceGroup(forward) : null }
}

export function filterRows(rows: DrawRow[], c: Conditions): DrawRow[] {
  return rows.filter((x) => (c.d === null || x[2] === c.d) && (c.r === null || x[3] === c.r) && (c.g === null || x[4] === c.g) && (c.p === null || x[5] === c.p))
}

export interface Cell {
  n: number
  w: number
  e: number
  z: number
}

export function aggregate(rows: DrawRow[], barrier: [number, number], styles: number[]): Cell {
  let n = 0
  let w = 0
  let e = 0
  let v = 0
  for (const r of rows) {
    if (r[0] < barrier[0] || r[0] > barrier[1] || !styles.includes(r[1])) continue
    n++
    w += r[6]
    e += r[7]
    v += r[7] * (1 - r[7])
  }
  return { n, w, e, z: v > 0 ? (w - e) / Math.sqrt(v) : 0 }
}

// Smoothed A2E: wins over expected wins with K expected wins of weight pulled toward 1, so a small cell is not read as a finding.
export const SMOOTH_K = 10
export const smoothA2E = (c: Cell): number => (c.w + SMOOTH_K) / (c.e + SMOOTH_K)

export const MIN_RUNNERS = 500

// The race's own conditions, widened (pace first, then going, then rail) until the filter holds enough runners. Distance is never dropped.
export function widen(rows: DrawRow[], race: Conditions): { cond: Conditions; dropped: ('p' | 'g' | 'r')[] } {
  const cond = { ...race }
  const dropped: ('p' | 'g' | 'r')[] = []
  for (const k of ['p', 'g', 'r'] as const) {
    if (filterRows(rows, cond).length >= MIN_RUNNERS) break
    if (cond[k] !== null) {
      cond[k] = null
      dropped.push(k)
    }
  }
  return { cond, dropped }
}
