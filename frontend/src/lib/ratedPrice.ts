// Rated prices by simulation (14 Oct 2026). Each runner's true performance is its projected rating plus normal noise whose size depends on
// how well the runner is known (the projection's own sd: light-history runners are noisier). Win chances are exact (numerical integration of
// P(runner's figure beats every other)); place chances come from a seeded Monte Carlo (3 places for 8+ runners, 2 for 5 to 7, none below).
// Replaces the softmax: tested on 50,540 races (betsignal/rated_price_sim.py) the by-type simulation beat the softmax every year and roughly
// halved the longshot over-statement. It is the projection's view, not a betting price.

const REF_SD = 7.0       // projection sd that gets the base noise
const BASE_SD = 7.9      // noise sd at beta 0.20: matches the softmax's overall sharpness (equal average entropy on 300 synthetic fields)
const RATIO_MIN = 0.8
const RATIO_MAX = 1.8
const QUAD_POINTS = 121
const MC_DRAWS = 2500

export interface SimInput { runId: string; wpr: number; sd: number | null }
export interface SimOut { win: number; place: number | null }

function normCdf(x: number): number {
  // Abramowitz-Stegun 7.1.26 via erf
  const t = 1 / (1 + 0.3275911 * Math.abs(x) / Math.SQRT2)
  const y = 1 - (((((1.061405429 * t - 1.453152027) * t) + 1.421413741) * t - 0.284496736) * t + 0.254829592) * t * Math.exp(-(x * x) / 2)
  return x >= 0 ? 0.5 * (1 + y) : 0.5 * (1 - y)
}

function mulberry32(a: number) {
  return () => {
    a |= 0; a = (a + 0x6d2b79f5) | 0
    let t = Math.imul(a ^ (a >>> 15), 1 | a)
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296
  }
}

export function placesFor(n: number): number {
  return n >= 8 ? 3 : n >= 5 ? 2 : 0
}

export function noiseSd(projectionSd: number | null, beta: number): number {
  const ratio = projectionSd != null ? Math.min(RATIO_MAX, Math.max(RATIO_MIN, projectionSd / REF_SD)) : 1
  return BASE_SD * (0.2 / Math.max(beta, 0.01)) * ratio
}

const cache = new Map<string, SimOut[]>()

export function simulateRace(inputs: SimInput[], beta: number): SimOut[] {
  const n = inputs.length
  const key = `${beta}|` + inputs.map((r) => `${r.wpr.toFixed(2)}:${(r.sd ?? -1).toFixed(2)}`).join(',')
  const hit = cache.get(key)
  if (hit) return hit
  const mu = inputs.map((r) => r.wpr)
  const sd = inputs.map((r) => noiseSd(r.sd, beta))

  // Win: integrate over runner i's standard-normal draw z, all rivals' cdfs at that figure.
  const win = new Array<number>(n).fill(0)
  const zs: number[] = []
  const ws: number[] = []
  let wsum = 0
  for (let k = 0; k < QUAD_POINTS; k++) {
    const z = -6 + (12 * k) / (QUAD_POINTS - 1)
    const w = Math.exp(-(z * z) / 2)
    zs.push(z); ws.push(w); wsum += w
  }
  for (let i = 0; i < n; i++) {
    let acc = 0
    for (let k = 0; k < QUAD_POINTS; k++) {
      const x = mu[i] + sd[i] * zs[k]
      let lp = 0
      for (let j = 0; j < n; j++) {
        if (j === i) continue
        lp += Math.log(Math.max(normCdf((x - mu[j]) / sd[j]), 1e-300))
      }
      acc += ws[k] * Math.exp(lp)
    }
    win[i] = acc / wsum
  }
  const tot = win.reduce((a, b) => a + b, 0) || 1
  for (let i = 0; i < n; i++) win[i] /= tot

  const np = placesFor(n)
  let place: (number | null)[] = new Array(n).fill(null)
  if (np > 0) {
    let seed = 2166136261
    for (let i = 0; i < key.length; i++) seed = Math.imul(seed ^ key.charCodeAt(i), 16777619)
    const rnd = mulberry32(seed)
    const counts = new Array<number>(n).fill(0)
    const fig = new Array<number>(n)
    const idx = Array.from({ length: n }, (_, i) => i)
    for (let d = 0; d < MC_DRAWS; d++) {
      for (let i = 0; i < n; i++) {
        const u1 = Math.max(rnd(), 1e-12), u2 = rnd()
        fig[i] = mu[i] + sd[i] * Math.sqrt(-2 * Math.log(u1)) * Math.cos(2 * Math.PI * u2)
      }
      idx.sort((a, b) => fig[b] - fig[a])
      for (let r = 0; r < np; r++) counts[idx[r]]++
    }
    place = counts.map((c, i) => Math.max(c / MC_DRAWS, win[i]))
  }
  const out = inputs.map((_, i) => ({ win: win[i], place: place[i] }))
  if (cache.size > 400) cache.clear()
  cache.set(key, out)
  return out
}
