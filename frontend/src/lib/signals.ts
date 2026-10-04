// Market signals (5 Oct 2026): pre-race facts the market has consistently under-rated (green) or over-rated (red) in
// 2023-2026 (racing-model reports/filter_screen*.md). Codes and effects come from the value model's fitted weights
// (racing-model model/value_params.json, |weight| >= 0.015; racing_model.json runners[].sg). Effect = how much the
// signal moves the horse's win chance vs its price, other things equal.
export interface SignalInfo {
  label: string
  detail: string
  effect: number // fractional change in win chance vs the price, e.g. 0.08 = +8%
}

export const SIGNAL_INFO: Record<string, SignalInfo> = {
  f_vet: { label: 'Vet issue last start', detail: 'lame, bled, heart or soreness reported last start', effect: 0.11 },
  f_gps_ground: { label: 'Covered extra ground last start', detail: 'GPS: top 20% for extra metres vs that field', effect: 0.08 },
  f_wide: { label: 'Raced wide last start', detail: 'stewards: wide / without cover', effect: 0.07 },
  f_barrier10: { label: 'Barrier 10+', detail: 'wide draws are over-penalised by the market', effect: 0.05 },
  f_4thup: { label: '4th+ run this prep', detail: 'fit and racing; under-bet vs first and second up', effect: 0.05 },
  f_dist_up: { label: 'Up 200m+ in distance', detail: 'stepping up from last start', effect: 0.03 },
  f_age6: { label: 'Age 6+', detail: 'older horses are under-bet', effect: 0.02 },
  f_laid: { label: 'Laid in / hung / shifted last start', detail: 'an excuse the market marks down too far', effect: 0.02 },
  f_sm: { label: 'Speed map favoured', detail: "race-day projection in the field's top 18%", effect: 0.02 },
  f_back14: { label: 'Back within 14 days', detail: 'quick backup', effect: 0.02 },
  f_weak_jockey: { label: 'Low-strike jockey', detail: 'under 7% wins in the last year; the market over-penalises', effect: 0.02 },
  n_every_chance: { label: "'Every chance' last start", detail: 'ran to its mark with no excuse; over-bet next time', effect: -0.09 },
  n_stay_poor_sire: { label: 'Staying trip, weak staying sire', detail: "1600m+ and the sire's progeny win less over it", effect: -0.06 },
  n_top_jockey: { label: 'Top jockey', detail: '18%+ strike rate; the market over-bets them', effect: -0.02 },
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
