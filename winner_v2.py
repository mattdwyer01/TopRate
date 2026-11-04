"""winner_v2.py -- Proj v2: a rating built from WINNER chances instead of rating forecasts (4 Nov 2026).

Proj (v1) predicts the rating a horse will run, then a softmax turns the ratings into win chances. Proj v2 starts from the other end: the direct model
(direct_score.py, softmax loss on the winner, see CLAUDE.md "Direct finishing-position model") gives each runner's win chance, and this module puts that on the
Proj scale so every consumer of Proj (Rating column, gap lines, Rated $, Quaddie) can read it unchanged.

  rating = race mean of Proj + (z - race mean of z) / BETA        z = W_DIRECT x ln p_direct + (1 - W_DIRECT) x BETA x Proj

so with W_DIRECT = 1 the softmax of the rating at BETA is exactly the direct model's win chance, and with 0 it is Proj itself. The race mean of Proj is kept, so the
level of the field does not move (only the order and the gaps do). 0.8 is the blend that scored best in research/proj_direct_blend.py (T1 2025 results-file races
and 556 real fields); research/proj_v2_eval.py re-checks it on the growing complete-field log.

A race where any runner has no Proj uses the direct chance alone with the mean of the Proj figures that exist (no level = no rating).

Two guards (chosen on the 1,064-race log of 14 Oct to 3 Nov 2026, so treat them as cosmetic until re-checked on later races):
  - a first starter (n_runs 0) keeps its Proj v1 estimate: the winner model has no form for it, and keeping Proj lowered the winner log-lik loss by about 0.009;
  - the change from Proj v1 is limited to +-CLIP (6) points: a long shot Proj rates 34 would otherwise show 54 because the winner model's chance for a hopeless runner
    never falls below about 1% (1.5% of runners are clipped; the winner log-lik is unchanged within 0.0003).
"""
import numpy as np, pandas as pd

BETA = 0.20          # price sharpness of the dashboard (priceBeta); Proj v1 is softmaxed at this
W_DIRECT = 0.8       # share of the winner model in the blend (log space); 1 = winner model alone, 0 = Proj v1
CLIP = 6.0           # largest change from Proj v1, rating points


def to_rating(df, p_col='dm', proj_col='proj', race_col='race_id', runs_col='n_runs', w=W_DIRECT, beta=BETA, clip=CLIP):
    """Proj v2 rating per row. df: one row per runner of whole fields, p_col = direct win chance (normalised in the race), proj_col = Proj v1 (NaN allowed),
    runs_col = earlier runs (0 = first starter, kept at Proj v1; None to switch the rule off)."""
    p = pd.to_numeric(df[p_col], errors='coerce').clip(lower=1e-9)
    pr = pd.to_numeric(df[proj_col], errors='coerce')
    g = df[race_col]
    lnp = np.log(p)
    full = pr.notna().groupby(g).transform('all')                       # every runner has a Proj
    level = pr.groupby(g).transform('mean')                             # mean of the Proj figures that exist
    z = np.where(full, w * lnp + (1 - w) * beta * pr.fillna(0), lnp)    # a race with a missing Proj uses the winner model alone
    z = pd.Series(z, index=df.index)
    out = level + (z - z.groupby(g).transform('mean')) / beta
    if clip:
        base = pr.fillna(level)
        out = base + (out - base).clip(-clip, clip)
    if runs_col and runs_col in df.columns:
        out = out.where(~(pd.to_numeric(df[runs_col], errors='coerce') == 0), pr)
    return out.where(level.notna())
