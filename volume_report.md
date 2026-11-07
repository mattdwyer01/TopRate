# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-07; races checked 122; bets still open 8.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 43 | 93 | 4 | $1075 | $408 | $-667 | -62.1% | -55.8% |
| Volume v2 | 35 | 64 | 4 | $875 | $457 | $-417 | -47.7% | -40.0% |
| Volume v3 (P cut) | 17 | 30 | 1 | $425 | $94 | $-331 | -77.9% | -77.9% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 8 | $85 | 6 | $135 | 4 | $69 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 93 | $-667 | -62.1% | 64 | $-417 | -47.7% | 30 | $-331 | -77.9% |
| Meeting minimum prize $30k+ | 49 | $-415 | -72.2% | 33 | $-240 | -53.3% | 20 | $-181 | -65.9% |
| Meeting minimum prize $40k+ | 35 | $-215 | -57.3% | 25 | $-90 | -30.0% | 10 | $-6 | -6.2% |
| Meeting minimum prize $50k+ | 25 | $-90 | -36.0% | 18 | $10 | 5.0% | 4 | $69 | 275.0% |
| Good or firm going (1 to 4) | 74 | $-552 | -65.0% | 46 | $-303 | -46.5% | 26 | $-256 | -73.2% |
| $30k+ and good/firm | 34 | $-240 | -60.0% | 19 | $-65 | -23.6% | 16 | $-106 | -53.1% |
| $40k+ and good/firm | 26 | $-140 | -46.7% | 16 | $-15 | -6.7% | 10 | $-6 | -6.2% |
| Field of 8 or more | 80 | $-492 | -54.7% | 56 | $-292 | -39.0% | 27 | $-256 | -73.2% |
| Field of 5 to 7 | 13 | $-175 | -100.0% | 8 | $-125 | -100.0% | 3 | $-75 | -100.0% |
| $40k+ and field of 8+ | 32 | $-190 | -54.3% | 22 | $-65 | -23.6% | 10 | $-6 | -6.2% |
| P(first third) 0.7+ | 18 | $-125 | -62.5% | 11 | $-46 | -26.9% | 18 | $-188 | -66.7% |
| P(first third) 0.5 to 0.7 | 18 | $-206 | -100.0% | 10 | $-133 | -100.0% | 12 | $-144 | -100.0% |
| P(first third) under 0.5 | 11 | $-34 | -28.7% | 5 | $-11 | -11.3% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 23 | $-300 | -100.0% | 19 | $-275 | -100.0% | 9 | $-125 | -100.0% |
| 3+ earlier races, under 25% won from first third | 29 | $-275 | -100.0% | 13 | $-175 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 61
- first starter, light-history or no-Proj runner: 52
- bush meeting: 9
