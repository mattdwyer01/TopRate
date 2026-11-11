# Value model forward test

The model was locked on races to 2026-10-08. Every race below is later than that. Bets are the fixed rule (model chance x net return above 1.00, Betfair starting price under $30), 1 unit each, paid at the Betfair starting price after commission (10% NSW, 8% elsewhere). Research only: no bets are placed, and the Betfair starting price is not known before the jump.

Pass rule, fixed before the first day was scored: first read at 2000 bets, final read at 6000. Pass = return above zero without the 10 best winners, and the bets win more often than the Betfair price implied.

**no read yet: 1407 of 2000 bets**

2026-10-09 to 2026-11-08: 31 days, 1466 races scored, 14074 runners.

| | Bets | Wins | Won | Model said | Betfair said | Avg price | Profit (units) | Return | Return without 10 best |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 1407 | 211 | 15.0% | 15.7% | 14.1% | $12.20 | +1.3 | +0.1% | -14.5% |
| Under $6 | 367 | 122 | 33.2% | 34.6% | 31.6% | $3.64 | +8.2 | +2.2% | -9.1% |
| $6 to $12 | 395 | 45 | 11.4% | 13.2% | 11.7% | $8.94 | -44.8 | -11.3% | -33.7% |
| $12 to $30 | 645 | 44 | 6.8% | 6.4% | 5.6% | $19.07 | +37.9 | +5.9% | -26.0% |
| NSW | 286 | 45 | 15.7% | 16.8% | 14.8% | $11.52 | +12.9 | +4.5% | -38.6% |
| Other states | 1121 | 166 | 14.8% | 15.4% | 13.9% | $12.38 | -11.6 | -1.0% | -19.3% |

Return range from resampling days (90%): -10.1% to +10.7%; chance the return is above zero: 50%.
Winner log-likelihood gain over the Betfair price: -0.0007 a race (standard error 0.0020).

## By week

| Week starting | Bets | Wins | Profit (units) | Return |
|---|---|---|---|---|
| 2026-10-05 | 187 | 23 | -26.0 | -13.9% |
| 2026-10-12 | 292 | 52 | +91.1 | +31.2% |
| 2026-10-19 | 300 | 45 | -9.2 | -3.1% |
| 2026-10-26 | 314 | 42 | -39.0 | -12.4% |
| 2026-11-02 | 314 | 49 | -15.6 | -5.0% |
