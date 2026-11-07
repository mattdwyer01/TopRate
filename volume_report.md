# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-07; races checked 205; bets still open 10.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 77 | 163 | 14 | $1925 | $1410 | $-514 | -26.7% | -23.2% |
| Volume v2 | 63 | 118 | 11 | $1575 | $1287 | $-288 | -18.3% | -14.0% |
| Volume v3 (P cut) | 43 | 66 | 7 | $1075 | $1129 | $54 | 5.0% | 5.0% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 78 | $238 | 60 | $264 | 40 | $454 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 163 | $-514 | -26.7% | 118 | $-288 | -18.3% | 66 | $54 | 5.0% |
| Meeting minimum prize $30k+ | 104 | $-175 | -14.0% | 76 | $-48 | -4.8% | 52 | $279 | 32.8% |
| Meeting minimum prize $40k+ | 90 | $25 | 2.4% | 68 | $102 | 12.0% | 42 | $454 | 67.2% |
| Meeting minimum prize $50k+ | 64 | $232 | 32.0% | 48 | $114 | 20.8% | 27 | $541 | 120.3% |
| Good or firm going (1 to 4) | 135 | $-387 | -24.2% | 92 | $-161 | -12.9% | 61 | $154 | 15.8% |
| $30k+ and good/firm | 89 | $0 | 0.0% | 62 | $127 | 15.4% | 48 | $354 | 45.6% |
| $40k+ and good/firm | 81 | $100 | 10.3% | 59 | $177 | 22.8% | 42 | $454 | 67.2% |
| Field of 8 or more | 146 | $-265 | -15.8% | 109 | $-138 | -9.7% | 61 | $179 | 18.8% |
| Field of 5 to 7 | 17 | $-250 | -100.0% | 9 | $-150 | -100.0% | 5 | $-125 | -100.0% |
| $40k+ and field of 8+ | 86 | $75 | 7.5% | 65 | $127 | 15.4% | 41 | $479 | 73.7% |
| P(first third) 0.7+ | 41 | $-16 | -3.4% | 26 | $-17 | -4.9% | 41 | $18 | 2.6% |
| P(first third) 0.5 to 0.7 | 44 | $-89 | -15.2% | 30 | $-65 | -13.9% | 25 | $35 | 9.7% |
| P(first third) under 0.5 | 32 | $-108 | -33.4% | 24 | $20 | 6.9% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 61 | $-152 | -21.0% | 51 | $67 | 9.9% | 29 | $50 | 10.0% |
| 3+ earlier races, under 25% won from first third | 30 | $-300 | -100.0% | 14 | $-200 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 110
- first starter, light-history or no-Proj runner: 62
- bush meeting: 33
