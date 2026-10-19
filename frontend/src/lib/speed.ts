// Speed figure (lengths vs par, 0 = par, higher = faster) shown as 85 + 2.15 points a length (within-race slope of rating on figure, 309,976 runs, 2016-2026).
export const SPEED_PAR = 85 // chosen so the average runner (about -4.9 lengths) lands near the other ratings' average (about 75)
export const SPEED_POINTS_PER_LENGTH = 2.15
export const speedOnWprScale = (lengths: number) => SPEED_PAR + SPEED_POINTS_PER_LENGTH * lengths
