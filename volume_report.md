# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-07; races checked 131; bets still open 11.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 45 | 97 | 4 | $1125 | $408 | $-717 | -63.8% | -57.8% |
| Volume v2 | 36 | 66 | 4 | $900 | $457 | $-442 | -49.2% | -41.7% |
| Volume v3 (P cut) | 19 | 32 | 1 | $475 | $94 | $-381 | -80.3% | -80.3% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 12 | $35 | 8 | $110 | 6 | $19 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 97 | $-717 | -63.8% | 66 | $-442 | -49.2% | 32 | $-381 | -80.3% |
| Meeting minimum prize $30k+ | 53 | $-465 | -74.4% | 35 | $-265 | -55.8% | 22 | $-231 | -71.2% |
| Meeting minimum prize $40k+ | 39 | $-265 | -62.3% | 27 | $-115 | -35.4% | 12 | $-56 | -37.5% |
| Meeting minimum prize $50k+ | 29 | $-140 | -46.7% | 20 | $-15 | -6.7% | 6 | $19 | 25.0% |
| Good or firm going (1 to 4) | 78 | $-602 | -66.9% | 48 | $-328 | -48.5% | 28 | $-306 | -76.6% |
| $30k+ and good/firm | 38 | $-290 | -64.4% | 21 | $-90 | -30.0% | 18 | $-156 | -62.5% |
| $40k+ and good/firm | 30 | $-190 | -54.3% | 18 | $-40 | -16.0% | 12 | $-56 | -37.5% |
| Field of 8 or more | 84 | $-542 | -57.1% | 58 | $-318 | -41.0% | 29 | $-306 | -76.6% |
| Field of 5 to 7 | 13 | $-175 | -100.0% | 8 | $-125 | -100.0% | 3 | $-75 | -100.0% |
| $40k+ and field of 8+ | 36 | $-240 | -60.0% | 24 | $-90 | -30.0% | 12 | $-56 | -37.5% |
| P(first third) 0.7+ | 19 | $-137 | -64.7% | 12 | $-58 | -31.8% | 19 | $-212 | -69.4% |
| P(first third) 0.5 to 0.7 | 20 | $-231 | -100.0% | 11 | $-146 | -100.0% | 13 | $-169 | -100.0% |
| P(first third) under 0.5 | 12 | $-47 | -35.4% | 5 | $-11 | -11.3% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 23 | $-300 | -100.0% | 19 | $-275 | -100.0% | 9 | $-125 | -100.0% |
| 3+ earlier races, under 25% won from first third | 29 | $-275 | -100.0% | 13 | $-175 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 67
- first starter, light-history or no-Proj runner: 52
- bush meeting: 12
