"""Read-only: racing.com GraphQL schema introspection (names only) plus ONE request for Racing Australia's robots.txt.
Looks for result/placing/margin fields that might exist for non-VIC/SA/QLD meetings. About 8 requests, 1 s apart."""
import functools, json, os, re, time
import requests

print = functools.partial(print, flush=True)
EPS = {"form": "https://graphql.rmdprod.racing.com/", "cal": "https://graphql.api.racing.com/"}
UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/140.0 Safari/537.36")
KEYS = {"form": "RACINGCOM_API_KEY", "cal": "RACINGCOM_CAL_API_KEY"}
WORDS = re.compile(r"result|placing|finish|margin|dividend|runner|entry|position|time", re.I)

TYPES = """query{ __schema{ queryType{ name fields{ name args{ name } type{ name kind ofType{ name kind } } } } } }"""
TYPE = """query{ __type(name:"%s"){ name fields{ name type{ name kind ofType{ name kind ofType{ name } } } } } }"""


def sess(k):
    key = (os.environ.get(KEYS[k]) or "").strip()
    if not key:
        print(KEYS[k], "not set"); return None
    s = requests.Session()
    s.headers.update({"User-Agent": UA, "X-Api-Key": key, "Content-Type": "application/json",
                      "Referer": "https://dxp-static.racing.com/" if k == "form" else "https://www.racing.com/",
                      **({"Origin": "https://www.racing.com"} if k == "cal" else {})})
    return s


def q(s, ep, query):
    time.sleep(1.0)
    try:
        r = s.get(ep, params={"query": query}, timeout=12)
        if r.status_code != 200:
            return {"_http": r.status_code, "_body": r.text[:200]}
        return r.json()
    except Exception as e:
        return {"_err": str(e)[:200]}


def tname(t):
    while t and not t.get("name") and t.get("ofType"):
        t = t["ofType"]
    return (t or {}).get("name")


def main():
    for k in ("form", "cal"):
        s = sess(k)
        if not s:
            continue
        d = q(s, EPS[k], TYPES)
        fields = (((d.get("data") or {}).get("__schema") or {}).get("queryType") or {}).get("fields")
        if not fields:
            print(k, "introspection unavailable:", str(d)[:200]); continue
        print(f"== {k}: {len(fields)} query fields")
        print(" ", ", ".join(f["name"] for f in fields))
        if k == "form":
            seen = []
            for f in fields:
                if WORDS.search(f["name"]):
                    seen.append(tname(f["type"]))
            for tn in sorted(set(x for x in seen if x and not x.startswith("__")))[:8]:
                t = q(s, EPS[k], TYPE % tn)
                fl = ((t.get("data") or {}).get("__type") or {}).get("fields") or []
                print(f" type {tn}:", ", ".join(f"{x['name']}:{tname(x['type'])}" for x in fl)[:900])
    # one polite request for robots.txt
    time.sleep(2)
    try:
        r = requests.get("https://www.racingaustralia.horse/robots.txt", headers={"User-Agent": UA}, timeout=12)
        print("== RA robots.txt", r.status_code, "\n" + r.text[:1500])
    except Exception as e:
        print("RA robots error", str(e)[:200])


if __name__ == "__main__":
    main()
