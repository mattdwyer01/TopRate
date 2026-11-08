# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-08; races checked 227; bets still open 8.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 91 | 189 | 18 | $2275 | $2250 | $-24 | -1.1% | -0.8% |
| Volume v2 | 73 | 132 | 13 | $1825 | $2020 | $195 | 10.7% | 12.7% |
| Volume v3 (P cut) | 54 | 80 | 9 | $1350 | $1292 | $-58 | -4.3% | -12.2% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 93 | $770 | 67 | $764 | 47 | $384 |
| 2026-11-08 | 11 | $-42 | 7 | $-17 | 7 | $-42 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 189 | $-24 | -1.1% | 132 | $195 | 10.7% | 80 | $-58 | -4.3% |
| Meeting minimum prize $30k+ | 116 | $300 | 21.1% | 81 | $502 | 45.6% | 57 | $154 | 15.8% |
| Meeting minimum prize $40k+ | 97 | $550 | 46.9% | 71 | $677 | 73.2% | 45 | $379 | 50.5% |
| Meeting minimum prize $50k+ | 65 | $857 | 114.2% | 49 | $739 | 128.6% | 27 | $541 | 120.3% |
| Good or firm going (1 to 4) | 153 | $96 | 5.2% | 104 | $372 | 25.7% | 72 | $37 | 3.2% |
| $30k+ and good/firm | 98 | $500 | 40.9% | 67 | $677 | 73.2% | 52 | $254 | 29.0% |
| $40k+ and good/firm | 88 | $625 | 56.9% | 62 | $752 | 88.4% | 45 | $379 | 50.5% |
| Field of 8 or more | 159 | $266 | 14.2% | 115 | $387 | 24.9% | 67 | $54 | 5.0% |
| Field of 5 to 7 | 30 | $-290 | -72.5% | 17 | $-192 | -69.7% | 13 | $-112 | -40.6% |
| $40k+ and field of 8+ | 90 | $625 | 56.9% | 68 | $702 | 78.0% | 43 | $429 | 61.3% |
| P(first third) 0.7+ | 50 | $-62 | -10.3% | 34 | $-63 | -13.3% | 50 | $-65 | -7.4% |
| P(first third) 0.5 to 0.7 | 55 | $438 | 59.7% | 35 | $477 | 83.3% | 30 | $7 | 1.5% |
| P(first third) under 0.5 | 38 | $-98 | -25.1% | 25 | $8 | 2.6% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 67 | $-252 | -30.6% | 53 | $17 | 2.3% | 32 | $-25 | -4.3% |
| 3+ earlier races, under 25% won from first third | 30 | $-300 | -100.0% | 14 | $-200 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 123
- first starter, light-history or no-Proj runner: 71
- bush meeting: 33
