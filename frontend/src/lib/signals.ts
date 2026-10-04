// Market signals (5 Oct 2026, the user's chosen set): pre-race facts the market has consistently under-rated (green) or
// over-rated (red). Effect = wins vs what the price implies, among runners within 4 of the top pick at $2+ with no first
// starter, averaged over 2023-24 and 2025-26 (racing-model reports/filter_screen*.md). Codes: racing_model.json sg
// (racing-model model/value_live.SIGNALS). The V badge is separate (the value model).
export interface SignalInfo {
  label: string
  detail: string
  effect: number // fractional change in wins vs the price, e.g. 0.10 = 10% more winners than priced
}

export const SIGNAL_INFO: Record<string, SignalInfo> = {
  f_wide: { label: 'Raced wide last start', detail: 'stewards: wide / without cover', effect: 0.1 },
  f_vet: { label: 'Vet issue last start', detail: 'lame, bled, heart or soreness reported', effect: 0.09 },
  f_laid: { label: 'Laid in / hung / shifted last start', detail: 'an excuse the market marks down too far', effect: 0.05 },
  f_heldup: { label: 'Held up / checked last start', detail: 'held up, checked, hampered or crowded', effect: 0.04 },
  f_sm: { label: 'Speed map favoured', detail: "race-day projection in the field's top 18%", effect: 0.04 },
  f_bias: { label: 'Track bias helps', detail: "projected track bias in the field's top 20% for this runner", effect: 0.04 },
  f_back14: { label: 'Back within 14 days', detail: 'quick backup', effect: 0.04 },
  f_4thup: { label: '4th+ run this prep', detail: 'fit and racing', effect: 0.03 },
  n_apprentice: { label: 'Apprentice rider', detail: 'claiming rider; the market over-rates the claim', effect: -0.08 },
  n_stay_poor_sire: { label: 'Staying trip, weak staying sire', detail: "1600m+ and the sire's progeny win less over it", effect: -0.07 },
  n_every_chance: { label: "'Every chance' last start", detail: 'ran to its mark with no excuse; over-bet next time', effect: -0.03 },
}

export function signalList(codes: string[] | undefined): { code: string; info: SignalInfo }[] {
  return (codes ?? [])
    .filter((c) => SIGNAL_INFO[c])
    .map((c) => ({ code: c, info: SIGNAL_INFO[c] }))
    .sort((a, b) => b.info.effect - a.info.effect)
}

// Value at the current fixed price (racing-model model/value_live.py): p = softmax(vs x log p_price + vu) over the
// field; value = p x price. The value log bets value >= 1.0 at $51 or less.
export const VALUE_CUT = 1.0
export const VALUE_MAX_PRICE = 51
