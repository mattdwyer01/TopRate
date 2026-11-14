# Value model forward test

The model was locked on races to 2026-10-08. Every race below is later than that. Bets are the fixed rule (model chance x net return above 1.00, Betfair starting price under $30), 1 unit each, paid at the Betfair starting price after commission (10% NSW, 8% elsewhere). Research only: no bets are placed, and the Betfair starting price is not known before the jump.

Pass rule, fixed before the first day was scored: first read at 2000 bets, final read at 6000. Pass = return above zero without the 10 best winners, and the bets win more often than the Betfair price implied.

**no read yet: 1521 of 2000 bets**

2026-10-09 to 2026-11-12: 35 days, 1586 races scored, 15196 runners.

| | Bets | Wins | Won | Model said | Betfair said | Avg price | Profit (units) | Return | Return without 10 best |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 1521 | 231 | 15.2% | 15.8% | 14.2% | $12.17 | -7.3 | -0.5% | -14.0% |
| Under $6 | 397 | 135 | 34.0% | 34.8% | 31.7% | $3.63 | +14.4 | +3.6% | -6.9% |
| $6 to $12 | 434 | 50 | 11.5% | 13.2% | 11.7% | $8.93 | -44.3 | -10.2% | -30.8% |
| $12 to $30 | 690 | 46 | 6.7% | 6.4% | 5.6% | $19.12 | +22.6 | +3.3% | -26.5% |
| NSW | 315 | 49 | 15.6% | 16.8% | 14.9% | $11.43 | -5.9 | -1.9% | -41.0% |
| Other states | 1206 | 182 | 15.1% | 15.5% | 14.0% | $12.36 | -1.4 | -0.1% | -17.1% |

Return range from resampling days (90%): -9.9% to +10.0%; chance the return is above zero: 47%.
Winner log-likelihood gain over the Betfair price: -0.0003 a race (standard error 0.0019).

## By week

| Week starting | Bets | Wins | Profit (units) | Return |
|---|---|---|---|---|
| 2026-10-05 | 187 | 23 | -26.0 | -13.9% |
| 2026-10-12 | 292 | 52 | +91.1 | +31.2% |
| 2026-10-19 | 300 | 45 | -9.2 | -3.1% |
| 2026-10-26 | 314 | 42 | -39.0 | -12.4% |
| 2026-11-02 | 314 | 49 | -15.6 | -5.0% |
| 2026-11-09 | 114 | 20 | -8.6 | -7.5% |
