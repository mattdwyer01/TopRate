import pandas as pd, json
import wpr_projection as wpr

wpr._load_models()

df = pd.read_csv("toprate_runners.csv", low_memory=False)
df["date"] = pd.to_datetime(df["date"], errors="coerce")
df["scratched"] = pd.to_numeric(df.get("scratched"), errors="coerce").fillna(0)
df["won"] = pd.to_numeric(df.get("won"), errors="coerce")
has = df[(df["wprp_contrib"].notna()) & (df["scratched"]!=1) & (df["resulted"].fillna(0).astype(float)==1)].copy()

def parse(x,k):
    try: return json.loads(x).get(k)
    except Exception: return None
has["pace_shape"] = pd.to_numeric(has["wprp_contrib"].apply(lambda x: parse(x,"pace_shape")), errors="coerce")
has = has.dropna(subset=["pace_shape"])

since = (has["date"].max() - pd.Timedelta(days=365)).strftime("%Y-%m-%d")
race_id_to_score = wpr._build_pace_shape_race_scores(since)
FORM_CSV = "wpr_form_history.csv.gz"
name_map, _ = wpr._load_trainer_jockey_by_horse_date(FORM_CSV)
has["horse_lc"] = has["horse_id"].map(name_map).astype(str).str.lower()
settle_lookup = wpr._build_pace_shape_settle_lookup(since)
has["pace_score"] = has["race_id"].map(race_id_to_score)
has["predicted_rel_settle"] = [settle_lookup.get((h,d)) for h,d in zip(has["horse_lc"], has["date"])]
has = has.dropna(subset=["pace_score","predicted_rel_settle"])

has["settle_signal"] = (has["predicted_rel_settle"] - 0.5) * 2
has["pace_signal"] = (has["pace_score"] - 0.5) * 2
has["interaction"] = has["settle_signal"] * has["pace_signal"]

print(f"n={len(has):,}\n")
for label, mask in [
    ("LEADS + SLOW pace (uncontested lead)", (has["settle_signal"]<-0.4)&(has["pace_signal"]<-0.2)),
    ("LEADS + HOT pace (contested speed battle)", (has["settle_signal"]<-0.4)&(has["pace_signal"]>0.2)),
    ("BACK/LAST + HOT pace (closer into a demanding tempo)", (has["settle_signal"]>0.4)&(has["pace_signal"]>0.2)),
    ("BACK/LAST + SLOW pace (closer into no tempo, hard to get there)", (has["settle_signal"]>0.4)&(has["pace_signal"]<-0.2)),
]:
    sub = has[mask]
    print(f"{label}: n={len(sub)}, mean pace_shape={sub['pace_shape'].mean():+.2f}, win rate={sub['won'].mean()*100:.1f}%")
