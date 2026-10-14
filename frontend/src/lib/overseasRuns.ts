import type { FormRun } from '../types/domain'

// Past runs from racing.com for horses we hold no Australian results for (imports, first-time Australian starters), written by
// rc_horse_overseas.py into overseas_runs.json. They carry no rating, so they are shown in Recent runs as unrated runs and never
// feed anything else. One fetch for the whole file (a few KB), shared by every horse. Never throws: null means "no file".
interface RawOverseasRun {
  d: string
  trk: string
  dist: number | null
  go: string
  fin: number | null
  wt: number | null
  sp: number | null
  mgn: number | null
  jck: string
  cls: string
  bar: number | null
  tr: 0 | 1
}

let filePromise: Promise<Record<string, RawOverseasRun[]> | null> | null = null

function loadFile(): Promise<Record<string, RawOverseasRun[]> | null> {
  if (!filePromise) {
    filePromise = fetch('overseas_runs.json', { cache: 'no-cache' })
      .then((res) => (res.ok ? (res.json() as Promise<Record<string, RawOverseasRun[]>>) : null))
      .catch(() => null)
  }
  return filePromise
}

export async function fetchOverseasRuns(horseName: string): Promise<FormRun[]> {
  const file = await loadFile()
  const raw = file?.[horseName.trim().toLowerCase()]
  if (!raw) return []
  return raw.map((r) => ({
    track: r.tr ? `${r.trk} (trial)` : r.trk,
    distance: r.dist ?? 0,
    going: r.go,
    finishPosition: r.fin,
    wpr: null,
    raceShapeEarly: null,
    raceShapeMid: null,
    raceShapeLate: null,
    sectionalEarly: null,
    sectionalTo800: null,
    sectionalLate600: null,
    barrier: r.bar,
    margin: r.mgn,
    positionSettled: null,
    position800m: null,
    position400m: null,
    raceClass: r.cls || null,
    jockey: r.jck || null,
    isPeakRun: false,
    date: r.d,
    weight: r.wt,
    startingPrice: r.sp,
    raceNumber: null,
    overseas: true,
  }))
}
