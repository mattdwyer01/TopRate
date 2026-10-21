// Speed figure (lengths vs par, 0 = par, higher = faster) shown as 85 + 2.15 points a length (within-race slope of rating on figure, 309,976 runs, 2016-2026).
export const SPEED_PAR = 85 // chosen so the average runner (about -4.9 lengths) lands near the other ratings' average (about 75)
export const SPEED_POINTS_PER_LENGTH = 2.15
export const speedOnWprScale = (lengths: number) => SPEED_PAR + SPEED_POINTS_PER_LENGTH * lengths

// The Spd RATING (a horse's average of earlier figures) on the same scale as Nett and Proj, 22 Oct 2026: 73.15 + 1.33 x (lengths + 4.51) over 3,035 upcoming runners
// with all three signals (17 to 22 Oct). Mean matched to Nett (73.2); 1.33 points a length makes the within-race spread 4.2, equal to Nett's and Proj's (4.2).
// Per-run figures in Recent runs keep the 85 + 2.15 scale above (a single run is not an average, so it spreads more).
export const SPEED_RATING_PAR = 79.15
export const SPEED_RATING_POINTS_PER_LENGTH = 1.33
export const speedRatingOnScale = (lengths: number) => SPEED_RATING_PAR + SPEED_RATING_POINTS_PER_LENGTH * lengths
