# Value model forward test

The model was locked on races to 2026-10-08. Every race below is later than that. Bets are the fixed rule (model chance x net return above 1.00, Betfair starting price under $30), 1 unit each, paid at the Betfair starting price after commission (10% NSW, 8% elsewhere). Research only: no bets are placed, and the Betfair starting price is not known before the jump.

Pass rule, fixed before the first day was scored: first read at 2000 bets, final read at 6000. Pass = return above zero without the 10 best winners, and the bets win more often than the Betfair price implied.

**no read yet: 1497 of 2000 bets**

2026-10-09 to 2026-11-08: 31 days, 1405 races scored, 13507 runners.

| | Bets | Wins | Won | Model said | Betfair said | Avg price | Profit (units) | Return | Return without 10 best |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 1497 | 217 | 14.5% | 15.5% | 13.9% | $12.23 | -57.7 | -3.9% | -17.4% |
| Under $6 | 394 | 128 | 32.5% | 33.7% | 30.8% | $3.74 | +9.6 | +2.4% | -8.2% |
| $6 to $12 | 419 | 45 | 10.7% | 13.2% | 11.7% | $8.92 | -71.1 | -17.0% | -37.7% |
| $12 to $30 | 684 | 44 | 6.4% | 6.4% | 5.6% | $19.14 | +3.7 | +0.5% | -29.1% |
| NSW | 318 | 51 | 16.0% | 16.1% | 14.3% | $12.04 | +25.1 | +7.9% | -33.3% |
| Other states | 1179 | 166 | 14.1% | 15.3% | 13.8% | $12.28 | -82.8 | -7.0% | -24.2% |

Return range from resampling days (90%): -17.5% to +11.4%; chance the return is above zero: 32%.
Winner log-likelihood gain over the Betfair price: -0.0026 a race (standard error 0.0021).

## By week

| Week starting | Bets | Wins | Profit (units) | Return |
|---|---|---|---|---|
| 2026-10-05 | 180 | 25 | +9.9 | +5.5% |
| 2026-10-12 | 326 | 50 | -27.6 | -8.5% |
| 2026-10-19 | 329 | 59 | +115.4 | +35.1% |
| 2026-10-26 | 339 | 42 | -59.3 | -17.5% |
| 2026-11-02 | 323 | 41 | -96.2 | -29.8% |
