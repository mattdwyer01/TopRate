import { useEffect, useState } from 'react'

// Plan maps of courses (Oct 2026): the racerate.com plan maps (home straight at the bottom, winning post, start posts and chutes with distances) traced into smooth SVG by
// research/racerate_maps.py. track_maps.json at the repo root indexes them by lowercase alphanumeric course name and track_maps/<slug>.svg holds the drawing (class "ink"
// for the strokes and text, "acc" for the red text). Both are optional: a venue without a map falls back to the OSM outline.

export interface TrackMapEntry {
  name: string
  w: number
  h: number
}

interface MapIndex {
  source: string
  maps: Record<string, TrackMapEntry>
}

let indexP: Promise<MapIndex | null> | null = null
const svgCache = new Map<string, Promise<string | null>>()

function loadIndex(): Promise<MapIndex | null> {
  if (!indexP) {
    indexP = fetch('track_maps.json')
      .then((r) => (r.ok ? (r.json() as Promise<MapIndex>) : null))
      .catch(() => null)
  }
  return indexP
}

function loadSvg(slug: string): Promise<string | null> {
  let p = svgCache.get(slug)
  if (!p) {
    p = fetch(`track_maps/${slug}.svg`)
      .then((r) => (r.ok ? r.text() : null))
      .catch(() => null)
    svgCache.set(slug, p)
  }
  return p
}

const norm = (s: string) => s.toLowerCase().replace(/[^a-z0-9]/g, '')

// The plan map for a venue: its entry and the SVG markup, or null (still loading or no map). `loaded` tells those two apart.
export function useTrackMap(venue: string): { entry: TrackMapEntry | null; svg: string | null; loaded: boolean } {
  const [state, setState] = useState<{ entry: TrackMapEntry | null; svg: string | null; loaded: boolean }>({ entry: null, svg: null, loaded: false })
  useEffect(() => {
    let alive = true
    setState({ entry: null, svg: null, loaded: false })
    loadIndex().then(async (idx) => {
      const slug = norm(venue)
      const entry = idx?.maps[slug] ?? null
      const svg = entry ? await loadSvg(slug) : null
      if (alive) setState({ entry: svg ? entry : null, svg, loaded: true })
    })
    return () => {
      alive = false
    }
  }, [venue])
  return state
}
