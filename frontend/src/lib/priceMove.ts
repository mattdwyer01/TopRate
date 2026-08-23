// Fixed-price movement vs the raceday reference price (open_price, frozen
// at the ~9am AEST daily fetch - see toprate_daily.py). Racing convention:
// a price getting SHORTER ("firming") signals more support and is the
// "good" direction map dashboards colour positive; a price getting LONGER
// ("drifting") is the opposite. Framed by direction/magnitude rather than
// raw sign so callers don't have to re-derive the (current < open) logic.

export interface PriceMove {
  direction: 'firmed' | 'drifted'
  pctChange: number // positive magnitude, e.g. 23.4 for a 23.4% move
}

export function computePriceMove(open: number | null, current: number | null): PriceMove | null {
  if (open == null || current == null || open <= 0 || current <= 0) return null
  if (open === current) return null
  return {
    direction: current < open ? 'firmed' : 'drifted',
    pctChange: (Math.abs(current - open) / open) * 100,
  }
}

// Below this magnitude, treat a move as rounding/API noise rather than a
// real market signal - keeps the compact table quiet except for real moves.
export const MOVE_DISPLAY_THRESHOLD_PCT = 3
