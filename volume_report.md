# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-07; races checked 176; bets still open 10.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 62 | 128 | 8 | $1550 | $780 | $-770 | -49.7% | -45.3% |
| Volume v2 | 50 | 90 | 7 | $1250 | $845 | $-405 | -32.4% | -27.0% |
| Volume v3 (P cut) | 29 | 46 | 2 | $725 | $179 | $-546 | -75.3% | -75.3% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 43 | $-18 | 32 | $147 | 20 | $-146 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 128 | $-770 | -49.7% | 90 | $-405 | -32.4% | 46 | $-546 | -75.3% |
| Meeting minimum prize $30k+ | 76 | $-505 | -53.2% | 53 | $-240 | -32.0% | 35 | $-371 | -67.5% |
| Meeting minimum prize $40k+ | 62 | $-305 | -40.7% | 45 | $-90 | -15.0% | 25 | $-196 | -52.3% |
| Meeting minimum prize $50k+ | 47 | $-155 | -28.2% | 35 | $-65 | -15.3% | 17 | $-96 | -35.0% |
| Good or firm going (1 to 4) | 102 | $-667 | -53.4% | 66 | $-302 | -31.8% | 41 | $-446 | -71.4% |
| $30k+ and good/firm | 61 | $-330 | -42.6% | 39 | $-65 | -11.3% | 31 | $-296 | -62.4% |
| $40k+ and good/firm | 53 | $-230 | -34.1% | 36 | $-15 | -2.9% | 25 | $-196 | -52.3% |
| Field of 8 or more | 112 | $-545 | -41.1% | 81 | $-255 | -23.2% | 42 | $-446 | -71.4% |
| Field of 5 to 7 | 16 | $-225 | -100.0% | 9 | $-150 | -100.0% | 4 | $-100 | -100.0% |
| $40k+ and field of 8+ | 59 | $-280 | -38.6% | 42 | $-65 | -11.3% | 25 | $-196 | -52.3% |
| P(first third) 0.7+ | 31 | $-198 | -55.3% | 19 | $-138 | -52.4% | 31 | $-344 | -65.8% |
| P(first third) 0.5 to 0.7 | 31 | $-175 | -42.4% | 21 | $-77 | -24.5% | 15 | $-202 | -100.0% |
| P(first third) under 0.5 | 20 | $-95 | -41.2% | 12 | $37 | 18.7% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 39 | $-275 | -57.9% | 33 | $-150 | -33.3% | 17 | $-275 | -100.0% |
| 3+ earlier races, under 25% won from first third | 30 | $-300 | -100.0% | 14 | $-200 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 90
- first starter, light-history or no-Proj runner: 59
- bush meeting: 27
