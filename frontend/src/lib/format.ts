export function fmtPrice(v: number | null | undefined): string {
  if (v === null || v === undefined || Number.isNaN(v)) return '-'
  return `$${v.toFixed(2)}`
}

export function fmtWpr(v: number | null | undefined): string {
  if (v === null || v === undefined || Number.isNaN(v)) return '-'
  return v.toFixed(1)
}

export function fmtInt(v: number | null | undefined): string {
  if (v === null || v === undefined || Number.isNaN(v)) return '-'
  return String(Math.round(v))
}

// Overlay%: how much more (or less) than the model's fair price the market
// is offering. NOTE: an earlier backtest on this project found overlay% is
// NOT predictive of outcome on its own - it's shown as information, never
// styled as a "buy signal" (a past version of this dashboard did highlight
// it green as a signal and that was deliberately removed once the backtest
// came back negative - see CLAUDE.md history). Keep it plain here too.
export function overlayPct(
  fixedPrice: number | null,
  wprPrice: number | null,
): number | null {
  if (!fixedPrice || !wprPrice) return null
  return ((fixedPrice - wprPrice) / wprPrice) * 100
}

export function fmtPct(v: number | null | undefined): string {
  if (v === null || v === undefined || Number.isNaN(v)) return '-'
  const sign = v > 0 ? '+' : ''
  return `${sign}${v.toFixed(0)}%`
}
