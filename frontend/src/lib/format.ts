// The model hard-caps wprPrice at 999 (see PRICE_CAP in lib/raceModel.ts /
// wpr_projection.py project_race) - a raw softmax price for a no-hope
// runner can blow out to 5-6 figures, so past the cap the exact number is
// meaningless. Showing "$999+" rather than "$999.00" signals that instead
// of reading as a suspiciously round literal price.
export function fmtPrice(v: number | null | undefined): string {
  if (v === null || v === undefined || Number.isNaN(v)) return '-'
  if (v >= 999) return '$999+'
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
