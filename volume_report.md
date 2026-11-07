# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-07; races checked 207; bets still open 9.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 80 | 168 | 15 | $2000 | $2060 | $61 | 3.0% | 6.4% |
| Volume v2 | 66 | 122 | 12 | $1650 | $1937 | $287 | 17.4% | 21.5% |
| Volume v3 (P cut) | 45 | 69 | 7 | $1125 | $1129 | $4 | 0.3% | 0.3% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 83 | $813 | 64 | $839 | 43 | $404 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 168 | $61 | 3.0% | 122 | $287 | 17.4% | 69 | $4 | 0.3% |
| Meeting minimum prize $30k+ | 106 | $425 | 32.7% | 78 | $552 | 52.5% | 53 | $254 | 29.0% |
| Meeting minimum prize $40k+ | 92 | $625 | 56.9% | 70 | $702 | 78.0% | 43 | $429 | 61.3% |
| Meeting minimum prize $50k+ | 65 | $857 | 114.2% | 49 | $739 | 128.6% | 27 | $541 | 120.3% |
| Good or firm going (1 to 4) | 140 | $188 | 11.2% | 96 | $414 | 31.3% | 64 | $104 | 10.1% |
| $30k+ and good/firm | 91 | $600 | 53.4% | 64 | $727 | 83.1% | 49 | $329 | 41.1% |
| $40k+ and good/firm | 83 | $700 | 68.3% | 61 | $777 | 94.1% | 43 | $429 | 61.3% |
| Field of 8 or more | 151 | $310 | 17.7% | 113 | $437 | 29.1% | 64 | $129 | 12.9% |
| Field of 5 to 7 | 17 | $-250 | -100.0% | 9 | $-150 | -100.0% | 5 | $-125 | -100.0% |
| $40k+ and field of 8+ | 88 | $675 | 64.3% | 67 | $727 | 83.1% | 42 | $454 | 67.2% |
| P(first third) 0.7+ | 44 | $-57 | -11.2% | 29 | $-67 | -17.0% | 44 | $-32 | -4.2% |
| P(first third) 0.5 to 0.7 | 45 | $536 | 88.1% | 31 | $560 | 114.5% | 25 | $35 | 9.7% |
| P(first third) under 0.5 | 33 | $-116 | -35.1% | 24 | $20 | 6.9% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 62 | $-177 | -23.6% | 52 | $42 | 6.0% | 30 | $25 | 4.8% |
| 3+ earlier races, under 25% won from first third | 30 | $-300 | -100.0% | 14 | $-200 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 112
- first starter, light-history or no-Proj runner: 62
- bush meeting: 33
