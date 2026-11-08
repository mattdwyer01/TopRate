# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-08; races checked 244; bets still open 9.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 99 | 209 | 20 | $2475 | $2331 | $-144 | -5.8% | -5.6% |
| Volume v2 | 79 | 142 | 14 | $1975 | $2095 | $120 | 6.1% | 7.9% |
| Volume v3 (P cut) | 59 | 92 | 11 | $1475 | $1373 | $-102 | -6.9% | -14.1% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 93 | $770 | 67 | $764 | 47 | $384 |
| 2026-11-08 | 31 | $-161 | 17 | $-92 | 19 | $-86 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 209 | $-144 | -5.8% | 142 | $120 | 6.1% | 92 | $-102 | -6.9% |
| Meeting minimum prize $30k+ | 129 | $256 | 16.5% | 87 | $477 | 39.7% | 66 | $135 | 12.5% |
| Meeting minimum prize $40k+ | 105 | $506 | 40.5% | 73 | $627 | 64.3% | 51 | $335 | 40.6% |
| Meeting minimum prize $50k+ | 73 | $813 | 98.5% | 51 | $689 | 110.3% | 33 | $497 | 94.7% |
| Good or firm going (1 to 4) | 163 | $46 | 2.4% | 110 | $372 | 24.4% | 78 | $37 | 3.0% |
| $30k+ and good/firm | 103 | $500 | 39.3% | 71 | $702 | 72.0% | 55 | $279 | 31.0% |
| $40k+ and good/firm | 88 | $625 | 56.9% | 62 | $752 | 88.4% | 45 | $379 | 50.5% |
| Field of 8 or more | 179 | $146 | 7.1% | 125 | $312 | 18.3% | 79 | $10 | 0.8% |
| Field of 5 to 7 | 30 | $-290 | -72.5% | 17 | $-192 | -69.7% | 13 | $-112 | -40.6% |
| $40k+ and field of 8+ | 98 | $581 | 49.5% | 70 | $652 | 68.6% | 49 | $385 | 49.6% |
| P(first third) 0.7+ | 58 | $-97 | -14.6% | 38 | $-125 | -23.4% | 58 | $-109 | -11.5% |
| P(first third) 0.5 to 0.7 | 61 | $425 | 53.4% | 37 | $527 | 88.2% | 34 | $7 | 1.4% |
| P(first third) under 0.5 | 44 | $-169 | -36.5% | 29 | $-55 | -14.8% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 71 | $-302 | -34.5% | 57 | $-33 | -4.3% | 32 | $-25 | -4.3% |
| 3+ earlier races, under 25% won from first third | 32 | $-325 | -100.0% | 14 | $-200 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 135
- first starter, light-history or no-Proj runner: 76
- bush meeting: 33
