# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-08; races checked 225; bets still open 7.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 90 | 187 | 18 | $2250 | $2250 | $1 | 0.0% | 0.3% |
| Volume v2 | 72 | 130 | 13 | $1800 | $2020 | $220 | 12.2% | 14.3% |
| Volume v3 (P cut) | 53 | 79 | 9 | $1325 | $1292 | $-33 | -2.5% | -10.5% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 93 | $770 | 67 | $764 | 47 | $384 |
| 2026-11-08 | 9 | $-17 | 5 | $8 | 6 | $-17 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 187 | $1 | 0.0% | 130 | $220 | 12.2% | 79 | $-33 | -2.5% |
| Meeting minimum prize $30k+ | 114 | $325 | 23.3% | 79 | $527 | 49.0% | 56 | $179 | 18.8% |
| Meeting minimum prize $40k+ | 97 | $550 | 46.9% | 71 | $677 | 73.2% | 45 | $379 | 50.5% |
| Meeting minimum prize $50k+ | 65 | $857 | 114.2% | 49 | $739 | 128.6% | 27 | $541 | 120.3% |
| Good or firm going (1 to 4) | 151 | $121 | 6.6% | 102 | $397 | 27.9% | 71 | $62 | 5.4% |
| $30k+ and good/firm | 96 | $525 | 43.8% | 65 | $702 | 78.0% | 51 | $279 | 32.8% |
| $40k+ and good/firm | 88 | $625 | 56.9% | 62 | $752 | 88.4% | 45 | $379 | 50.5% |
| Field of 8 or more | 159 | $266 | 14.2% | 115 | $387 | 24.9% | 67 | $54 | 5.0% |
| Field of 5 to 7 | 28 | $-265 | -70.7% | 15 | $-167 | -66.7% | 12 | $-87 | -34.7% |
| $40k+ and field of 8+ | 90 | $625 | 56.9% | 68 | $702 | 78.0% | 43 | $429 | 61.3% |
| P(first third) 0.7+ | 49 | $-49 | -8.4% | 33 | $-50 | -10.9% | 49 | $-40 | -4.7% |
| P(first third) 0.5 to 0.7 | 55 | $438 | 59.7% | 35 | $477 | 83.3% | 30 | $7 | 1.5% |
| P(first third) under 0.5 | 37 | $-86 | -22.6% | 24 | $20 | 6.9% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 67 | $-252 | -30.6% | 53 | $17 | 2.3% | 32 | $-25 | -4.3% |
| 3+ earlier races, under 25% won from first third | 30 | $-300 | -100.0% | 14 | $-200 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 121
- first starter, light-history or no-Proj runner: 71
- bush meeting: 33
