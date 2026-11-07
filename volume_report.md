# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-07; races checked 149; bets still open 16.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 52 | 108 | 6 | $1300 | $580 | $-720 | -55.4% | -50.2% |
| Volume v2 | 41 | 73 | 5 | $1025 | $545 | $-480 | -46.8% | -40.2% |
| Volume v3 (P cut) | 23 | 37 | 2 | $575 | $179 | $-396 | -68.9% | -68.9% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 23 | $33 | 15 | $72 | 11 | $4 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 108 | $-720 | -55.4% | 73 | $-480 | -46.8% | 37 | $-396 | -68.9% |
| Meeting minimum prize $30k+ | 61 | $-505 | -67.3% | 40 | $-340 | -61.8% | 26 | $-221 | -55.3% |
| Meeting minimum prize $40k+ | 47 | $-305 | -55.5% | 32 | $-190 | -47.5% | 16 | $-46 | -20.6% |
| Meeting minimum prize $50k+ | 36 | $-155 | -38.7% | 24 | $-65 | -23.6% | 10 | $29 | 19.2% |
| Good or firm going (1 to 4) | 86 | $-642 | -62.7% | 53 | $-402 | -53.7% | 32 | $-296 | -62.4% |
| $30k+ and good/firm | 46 | $-330 | -57.4% | 26 | $-165 | -44.0% | 22 | $-146 | -45.0% |
| $40k+ and good/firm | 38 | $-230 | -48.4% | 23 | $-115 | -35.4% | 16 | $-46 | -20.6% |
| Field of 8 or more | 93 | $-520 | -47.3% | 64 | $-330 | -37.7% | 33 | $-296 | -62.4% |
| Field of 5 to 7 | 15 | $-200 | -100.0% | 9 | $-150 | -100.0% | 4 | $-100 | -100.0% |
| $40k+ and field of 8+ | 44 | $-280 | -53.3% | 29 | $-165 | -44.0% | 16 | $-46 | -20.6% |
| P(first third) 0.7+ | 24 | $-119 | -42.7% | 14 | $-75 | -37.5% | 24 | $-228 | -56.0% |
| P(first third) 0.5 to 0.7 | 23 | $-206 | -70.2% | 14 | $-133 | -60.4% | 13 | $-169 | -100.0% |
| P(first third) under 0.5 | 15 | $-92 | -52.1% | 7 | $-44 | -34.2% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 26 | $-325 | -100.0% | 22 | $-300 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, under 25% won from first third | 29 | $-275 | -100.0% | 13 | $-175 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 76
- first starter, light-history or no-Proj runner: 55
- bush meeting: 18
