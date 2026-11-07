# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-07; races checked 112; bets still open 5.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 42 | 92 | 3 | $1050 | $322 | $-727 | -69.3% | -62.9% |
| Volume v2 | 34 | 63 | 3 | $850 | $372 | $-477 | -56.2% | -48.2% |
| Volume v3 (P cut) | 17 | 30 | 1 | $425 | $94 | $-331 | -77.9% | -77.9% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 7 | $25 | 5 | $75 | 4 | $69 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 92 | $-727 | -69.3% | 63 | $-477 | -56.2% | 30 | $-331 | -77.9% |
| Meeting minimum prize $30k+ | 48 | $-475 | -86.4% | 32 | $-300 | -70.6% | 20 | $-181 | -65.9% |
| Meeting minimum prize $40k+ | 34 | $-275 | -78.6% | 24 | $-150 | -54.6% | 10 | $-6 | -6.2% |
| Meeting minimum prize $50k+ | 24 | $-150 | -66.7% | 17 | $-50 | -28.6% | 4 | $69 | 275.0% |
| Good or firm going (1 to 4) | 73 | $-612 | -74.2% | 45 | $-363 | -58.0% | 26 | $-256 | -73.2% |
| $30k+ and good/firm | 33 | $-300 | -80.0% | 18 | $-125 | -50.0% | 16 | $-106 | -53.1% |
| $40k+ and good/firm | 25 | $-200 | -72.7% | 15 | $-75 | -37.5% | 10 | $-6 | -6.2% |
| Field of 8 or more | 79 | $-552 | -63.1% | 55 | $-352 | -48.6% | 27 | $-256 | -73.2% |
| Field of 5 to 7 | 13 | $-175 | -100.0% | 8 | $-125 | -100.0% | 3 | $-75 | -100.0% |
| $40k+ and field of 8+ | 31 | $-250 | -76.9% | 21 | $-125 | -50.0% | 10 | $-6 | -6.2% |
| P(first third) 0.7+ | 18 | $-125 | -62.5% | 11 | $-46 | -26.9% | 18 | $-188 | -66.7% |
| P(first third) 0.5 to 0.7 | 18 | $-206 | -100.0% | 10 | $-133 | -100.0% | 12 | $-144 | -100.0% |
| P(first third) under 0.5 | 10 | $-94 | -100.0% | 4 | $-71 | -100.0% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 23 | $-300 | -100.0% | 19 | $-275 | -100.0% | 9 | $-125 | -100.0% |
| 3+ earlier races, under 25% won from first third | 29 | $-275 | -100.0% | 13 | $-175 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 57
- first starter, light-history or no-Proj runner: 50
- bush meeting: 5
