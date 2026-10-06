# Suitability adjustment

A small second-stage adjustment to the rating projection, trained on the main model's out-of-sample residuals
(2024-07 onward, 335,305 runs). `suitability_model.txt` is a LightGBM model, `features.json` lists its inputs.

Inputs (all known before the race): the horse's settling style and draw, past steward/video comments (held up, raced
wide, slow away, lugging, weakened), day-of track bias from earlier races at the meeting (front-runner and draw
advantage, crossed with the horse's style), late versus early sectional profile, and the jockey's and trainer's tendency
to ride a horse further forward or back than its usual style.

Validated with 5-fold validation by month: rating RMSE 9.0792 -> 9.0590 (MAE 6.1040 -> 6.0934), every fold improves.
Projected 70+: RMSE 7.9764 -> 7.9630. The effect is small (the top-decile runners run about +0.9 points better than
projected and the bottom decile about -1.1 worse), well calibrated, and not a winner-selection edge: adding it to the market
price changed win log loss by 0.0001. Use it as an adjustment of about one rating point, not a headline signal.

Not yet a pipeline: the feature builder still lives in analysis scratch scripts (comment parsing, day-of bias, jockey tendency
as-of features) and needs porting before the adjustment can be computed for upcoming races. gear changes and blinkers
could not be tested (those columns are empty in the results data).
