# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-14; races checked 478; bets still open 33.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 173 | 359 | 40 | $4312 | $3650 | $-662 | -15.3% | -11.5% |
| Volume v2 | 128 | 221 | 27 | $3200 | $3065 | $-135 | -4.2% | 0.7% |
| Volume v3 (P cut) | 114 | 167 | 22 | $2837 | $2563 | $-275 | -9.7% | -7.0% |

## Volume v2 from 2026-11-13: fields of 8+ only, judged at the Betfair starting price after commission

Bets settled 52 (profit at the logged fixed price $48, ROI 5.8%). With a Betfair price 0: staked $0, returned $0, profit $0, ROI None%.

## The same bets at the Betfair starting price, after commission (10% NSW, 8% elsewhere)

Only bets whose Betfair price has arrived (Betfair publishes a day or more after the race).

| Rule | Bets with a Betfair price | Staked | Returned | Profit | ROI at Betfair | ROI at logged price, same bets |
|---|---|---|---|---|---|---|
| Volume v1 | 237 | $2862 | $2927 | $65 | 2.3% | -13.9% |
| Volume v2 | 163 | $2275 | $2638 | $363 | 15.9% | -3.6% |
| Volume v3 (P cut) | 104 | $1737 | $1616 | $-122 | -7.0% | -8.9% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 93 | $770 | 67 | $764 | 47 | $384 |
| 2026-11-08 | 42 | $-278 | 27 | $-183 | 24 | $-186 |
| 2026-11-09 | 16 | $-106 | 10 | $-150 | 7 | $25 |
| 2026-11-10 | 11 | $-99 | 5 | $-36 | 8 | $-47 |
| 2026-11-12 | 2 | $-25 | 2 | $-25 | 0 | $0 |
| 2026-11-13 | 64 | $-20 | 32 | $131 | 34 | $118 |
| 2026-11-14 | 46 | $-151 | 20 | $-83 | 21 | $-168 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 359 | $-662 | -15.3% | 221 | $-135 | -4.2% | 167 | $-275 | -9.7% |
| Meeting minimum prize $30k+ | 209 | $-143 | -5.7% | 127 | $327 | 18.2% | 110 | $-243 | -13.3% |
| Meeting minimum prize $40k+ | 159 | $341 | 17.7% | 102 | $627 | 44.0% | 80 | $95 | 6.9% |
| Meeting minimum prize $50k+ | 110 | $534 | 40.3% | 70 | $472 | 49.6% | 54 | $172 | 18.6% |
| Good or firm going (1 to 4) | 266 | $-497 | -15.6% | 165 | $-54 | -2.3% | 130 | $-133 | -6.3% |
| $30k+ and good/firm | 150 | $229 | 12.6% | 94 | $511 | 39.3% | 81 | $126 | 9.7% |
| $40k+ and good/firm | 109 | $587 | 42.7% | 74 | $711 | 69.4% | 56 | $364 | 38.3% |
| Field of 8 or more | 307 | $-227 | -6.3% | 199 | $106 | 3.7% | 142 | $-35 | -1.5% |
| Field of 5 to 7 | 52 | $-435 | -60.0% | 22 | $-242 | -74.4% | 25 | $-239 | -47.8% |
| $40k+ and field of 8+ | 142 | $483 | 28.4% | 99 | $652 | 46.6% | 73 | $245 | 20.0% |
| P(first third) 0.7+ | 104 | $-310 | -27.1% | 62 | $-253 | -29.0% | 104 | $-363 | -20.8% |
| P(first third) 0.5 to 0.7 | 122 | $461 | 28.5% | 72 | $636 | 54.6% | 63 | $89 | 8.1% |
| P(first third) under 0.5 | 87 | $-510 | -51.1% | 49 | $-290 | -42.2% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 114 | $-372 | -25.9% | 78 | $2 | 0.1% | 50 | $18 | 1.9% |
| 3+ earlier races, under 25% won from first third | 71 | $-511 | -68.1% | 35 | $-309 | -65.1% | 30 | $-388 | -73.8% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 45 | $-436 | -87.2% | 19 | $-217 | -66.9% | 22 | $-400 | -100.0% |

## Races checked without a bet, by reason

- ok: 242
- first starter, light-history or no-Proj runner: 147
- bush meeting: 87
- field under 5: 2
