# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-07; races checked 140; bets still open 15.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 47 | 101 | 5 | $1175 | $492 | $-682 | -58.1% | -52.3% |
| Volume v2 | 37 | 69 | 4 | $925 | $457 | $-467 | -50.5% | -43.2% |
| Volume v3 (P cut) | 21 | 35 | 2 | $525 | $179 | $-346 | -66.0% | -66.0% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 16 | $70 | 11 | $85 | 9 | $54 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 101 | $-682 | -58.1% | 69 | $-467 | -50.5% | 35 | $-346 | -66.0% |
| Meeting minimum prize $30k+ | 57 | $-430 | -63.7% | 38 | $-290 | -58.0% | 25 | $-196 | -52.3% |
| Meeting minimum prize $40k+ | 43 | $-230 | -48.4% | 30 | $-140 | -40.0% | 15 | $-21 | -10.6% |
| Meeting minimum prize $50k+ | 33 | $-105 | -30.0% | 23 | $-40 | -16.0% | 9 | $54 | 43.0% |
| Good or firm going (1 to 4) | 82 | $-567 | -59.7% | 51 | $-352 | -50.4% | 31 | $-271 | -60.3% |
| $30k+ and good/firm | 42 | $-255 | -51.0% | 24 | $-115 | -35.4% | 21 | $-121 | -40.4% |
| $40k+ and good/firm | 34 | $-155 | -38.7% | 21 | $-65 | -23.6% | 15 | $-21 | -10.6% |
| Field of 8 or more | 88 | $-507 | -50.7% | 61 | $-342 | -42.8% | 32 | $-271 | -60.3% |
| Field of 5 to 7 | 13 | $-175 | -100.0% | 8 | $-125 | -100.0% | 3 | $-75 | -100.0% |
| $40k+ and field of 8+ | 40 | $-205 | -45.6% | 27 | $-115 | -35.4% | 15 | $-21 | -10.6% |
| P(first third) 0.7+ | 22 | $-94 | -37.0% | 14 | $-75 | -37.5% | 22 | $-178 | -49.8% |
| P(first third) 0.5 to 0.7 | 20 | $-231 | -100.0% | 11 | $-146 | -100.0% | 13 | $-169 | -100.0% |
| P(first third) under 0.5 | 13 | $-55 | -39.3% | 6 | $-19 | -18.4% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 26 | $-325 | -100.0% | 22 | $-300 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, under 25% won from first third | 29 | $-275 | -100.0% | 13 | $-175 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 72
- first starter, light-history or no-Proj runner: 53
- bush meeting: 15
