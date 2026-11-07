# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-07; races checked 146; bets still open 20.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 49 | 103 | 5 | $1225 | $492 | $-732 | -59.8% | -54.3% |
| Volume v2 | 39 | 71 | 4 | $975 | $457 | $-517 | -53.1% | -46.2% |
| Volume v3 (P cut) | 21 | 35 | 2 | $525 | $179 | $-346 | -66.0% | -66.0% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 18 | $20 | 13 | $35 | 9 | $54 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 103 | $-732 | -59.8% | 71 | $-517 | -53.1% | 35 | $-346 | -66.0% |
| Meeting minimum prize $30k+ | 59 | $-480 | -66.2% | 40 | $-340 | -61.8% | 25 | $-196 | -52.3% |
| Meeting minimum prize $40k+ | 45 | $-280 | -53.3% | 32 | $-190 | -47.5% | 15 | $-21 | -10.6% |
| Meeting minimum prize $50k+ | 34 | $-130 | -34.7% | 24 | $-65 | -23.6% | 9 | $54 | 43.0% |
| Good or firm going (1 to 4) | 84 | $-617 | -61.7% | 53 | $-402 | -53.7% | 31 | $-271 | -60.3% |
| $30k+ and good/firm | 44 | $-305 | -55.5% | 26 | $-165 | -44.0% | 21 | $-121 | -40.4% |
| $40k+ and good/firm | 36 | $-205 | -45.6% | 23 | $-115 | -35.4% | 15 | $-21 | -10.6% |
| Field of 8 or more | 90 | $-557 | -53.1% | 63 | $-392 | -46.2% | 32 | $-271 | -60.3% |
| Field of 5 to 7 | 13 | $-175 | -100.0% | 8 | $-125 | -100.0% | 3 | $-75 | -100.0% |
| $40k+ and field of 8+ | 42 | $-255 | -51.0% | 29 | $-165 | -44.0% | 15 | $-21 | -10.6% |
| P(first third) 0.7+ | 22 | $-94 | -37.0% | 14 | $-75 | -37.5% | 22 | $-178 | -49.8% |
| P(first third) 0.5 to 0.7 | 21 | $-256 | -100.0% | 12 | $-171 | -100.0% | 13 | $-169 | -100.0% |
| P(first third) under 0.5 | 14 | $-80 | -48.5% | 7 | $-44 | -34.2% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 26 | $-325 | -100.0% | 22 | $-300 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, under 25% won from first third | 29 | $-275 | -100.0% | 13 | $-175 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 75
- first starter, light-history or no-Proj runner: 54
- bush meeting: 17
