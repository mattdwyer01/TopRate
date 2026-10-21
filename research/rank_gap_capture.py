"""Winners within N rating points of the top Rating, by blend (22 Oct 2026). Same 319-race sample as rank_refit_ctx.py. Rating = race mean of Proj + score x race sd of Proj
(the dashboard's Rating), so the gap is in Proj-scale points. Usage: PYTHONPATH=. python research/rank_gap_capture.py pc.pkl"""
import sys, numpy as np, pandas as pd
o = pd.read_pickle(sys.argv[1] if len(sys.argv) > 1 else "pc.pkl")
g = o.groupby("rk").ctx
o["psd"] = g.transform("std"); o["pm"] = g.transform("mean")
blends = {"Proj only": (1, 0, 0), "shipped 65/25/10": (.65, .25, .10), "55/30/15": (.55, .30, .15), "50/35/15": (.5, .35, .15), "fitted 38/39/23": (.388, .395, .228)}
n = o.rk.nunique(); print(n, "races,", len(o), "runners")
print("blend".ljust(20) + "".join(f"  <={k}pt" for k in range(1, 7)) + "   (winners captured %, avg runners inside)")
for lab, (a, b, c) in blends.items():
    s = a * o.z_context + b * o.z_nett + c * o.z_spd
    o["rating"] = o.pm + s * o.psd
    o["gap"] = o.groupby("rk").rating.transform("max") - o.rating
    row = []
    for k in range(1, 7):
        ins = o.gap <= k + 1e-9
        row.append(f"{100 * o[(o.won == 1)].gap.le(k + 1e-9).mean():5.1f}%/{ins.groupby(o.rk).sum().mean():.1f}")
    print(lab.ljust(20) + "  ".join(row))
