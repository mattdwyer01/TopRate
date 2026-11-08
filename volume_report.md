# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-08; races checked 240; bets still open 14.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 96 | 202 | 19 | $2400 | $2281 | $-119 | -4.9% | -4.7% |
| Volume v2 | 76 | 137 | 13 | $1900 | $2020 | $120 | 6.3% | 8.2% |
| Volume v3 (P cut) | 57 | 88 | 10 | $1425 | $1323 | $-102 | -7.2% | -14.6% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 93 | $770 | 67 | $764 | 47 | $384 |
| 2026-11-08 | 24 | $-136 | 12 | $-92 | 15 | $-86 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 202 | $-119 | -4.9% | 137 | $120 | 6.3% | 88 | $-102 | -7.2% |
| Meeting minimum prize $30k+ | 124 | $256 | 17.1% | 84 | $452 | 39.3% | 62 | $135 | 13.1% |
| Meeting minimum prize $40k+ | 103 | $531 | 43.4% | 72 | $652 | 68.6% | 50 | $360 | 45.0% |
| Meeting minimum prize $50k+ | 71 | $838 | 104.7% | 50 | $714 | 119.0% | 32 | $522 | 104.4% |
| Good or firm going (1 to 4) | 160 | $21 | 1.1% | 108 | $322 | 21.5% | 75 | $12 | 1.0% |
| $30k+ and good/firm | 100 | $475 | 38.0% | 69 | $652 | 68.6% | 52 | $254 | 29.0% |
| $40k+ and good/firm | 88 | $625 | 56.9% | 62 | $752 | 88.4% | 45 | $379 | 50.5% |
| Field of 8 or more | 172 | $171 | 8.6% | 120 | $312 | 19.2% | 75 | $10 | 0.8% |
| Field of 5 to 7 | 30 | $-290 | -72.5% | 17 | $-192 | -69.7% | 13 | $-112 | -40.6% |
| $40k+ and field of 8+ | 96 | $606 | 52.7% | 69 | $677 | 73.2% | 48 | $410 | 54.6% |
| P(first third) 0.7+ | 56 | $-81 | -12.5% | 37 | $-113 | -21.6% | 56 | $-93 | -9.9% |
| P(first third) 0.5 to 0.7 | 58 | $409 | 53.6% | 35 | $477 | 83.3% | 32 | $-10 | -2.0% |
| P(first third) under 0.5 | 42 | $-144 | -32.9% | 27 | $-17 | -5.2% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 69 | $-277 | -32.6% | 55 | $-8 | -1.1% | 32 | $-25 | -4.3% |
| 3+ earlier races, under 25% won from first third | 32 | $-325 | -100.0% | 14 | $-200 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 133
- first starter, light-history or no-Proj runner: 74
- bush meeting: 33
