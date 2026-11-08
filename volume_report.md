# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-08; races checked 246; bets still open 6.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 100 | 212 | 21 | $2500 | $2389 | $-110 | -4.4% | -4.2% |
| Volume v2 | 80 | 145 | 15 | $2000 | $2153 | $153 | 7.7% | 9.5% |
| Volume v3 (P cut) | 60 | 93 | 11 | $1500 | $1373 | $-127 | -8.5% | -15.6% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 93 | $770 | 67 | $764 | 47 | $384 |
| 2026-11-08 | 34 | $-128 | 20 | $-58 | 20 | $-111 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 212 | $-110 | -4.4% | 145 | $153 | 7.7% | 93 | $-127 | -8.5% |
| Meeting minimum prize $30k+ | 129 | $256 | 16.5% | 87 | $477 | 39.7% | 66 | $135 | 12.5% |
| Meeting minimum prize $40k+ | 105 | $506 | 40.5% | 73 | $627 | 64.3% | 51 | $335 | 40.6% |
| Meeting minimum prize $50k+ | 73 | $813 | 98.5% | 51 | $689 | 110.3% | 33 | $497 | 94.7% |
| Good or firm going (1 to 4) | 166 | $80 | 4.0% | 113 | $406 | 26.2% | 79 | $12 | 1.0% |
| $30k+ and good/firm | 103 | $500 | 39.3% | 71 | $702 | 72.0% | 55 | $279 | 31.0% |
| $40k+ and good/firm | 88 | $625 | 56.9% | 62 | $752 | 88.4% | 45 | $379 | 50.5% |
| Field of 8 or more | 182 | $180 | 8.6% | 128 | $345 | 20.0% | 80 | $-15 | -1.3% |
| Field of 5 to 7 | 30 | $-290 | -72.5% | 17 | $-192 | -69.7% | 13 | $-112 | -40.6% |
| $40k+ and field of 8+ | 98 | $581 | 49.5% | 70 | $652 | 68.6% | 49 | $385 | 49.6% |
| P(first third) 0.7+ | 58 | $-97 | -14.6% | 38 | $-125 | -23.4% | 58 | $-109 | -11.5% |
| P(first third) 0.5 to 0.7 | 63 | $467 | 57.5% | 39 | $569 | 92.5% | 35 | $-18 | -3.3% |
| P(first third) under 0.5 | 45 | $-178 | -37.6% | 30 | $-63 | -16.7% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 71 | $-302 | -34.5% | 57 | $-33 | -4.3% | 32 | $-25 | -4.3% |
| 3+ earlier races, under 25% won from first third | 35 | $-292 | -83.3% | 17 | $-167 | -74.1% | 12 | $-175 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 136
- first starter, light-history or no-Proj runner: 77
- bush meeting: 33
