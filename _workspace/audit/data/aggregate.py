#!/usr/bin/env python3
"""Merge per-batch triage + verify results into final.json, cross-checked vs inventory."""
import json
import glob
import os
import sys
from collections import Counter

SCRATCH = os.path.dirname(os.path.abspath(__file__))
RES = os.path.join(SCRATCH, "results")

inv = json.load(open(f"{SCRATCH}/inventory.json"))
inv_ids = {r["id"] for r in inv}
inv_by_id = {r["id"]: r for r in inv}

final = {}
problems_seen = Counter()
batch_status = {}

for tf in sorted(glob.glob(f"{RES}/*.triage.json")):
    bid = os.path.basename(tf).removesuffix(".triage.json")
    try:
        triage = json.load(open(tf))
    except Exception as e:
        batch_status[bid] = f"TRIAGE PARSE ERROR: {e}"
        continue
    verdicts = {}
    vf = f"{RES}/{bid}.verify.json"
    if os.path.exists(vf):
        try:
            vdata = json.load(open(vf))
            for v in vdata.get("verdicts", []):
                verdicts[v["id"]] = v
        except Exception as e:
            batch_status[bid] = f"VERIFY PARSE ERROR (triage kept unverified): {e}"
    n_rev = n_rej = n_conf = 0
    for p in triage.get("problems", []):
        pid = p.get("id", "")
        problems_seen[pid] += 1
        p = dict(p)
        p["batch"] = bid
        p.setdefault("flags", [])
        v = verdicts.get(pid)
        if v:
            verdict = v.get("verdict")
            if verdict == "CONFIRMED":
                p["flags"].append("verifier:confirmed")
                n_conf += 1
            elif verdict in ("REVISED", "REJECTED"):
                p["triage_cat"] = p["cat"]
                p["cat"] = v.get("final_cat", p["cat"])
                if v.get("final_match"):
                    p["match"] = v["final_match"]
                p["flags"].append(f"verifier:{verdict.lower()}")
                p["verifier_notes"] = v.get("notes", "")
                if verdict == "REVISED":
                    n_rev += 1
                else:
                    n_rej += 1
        final[pid] = p
    batch_status.setdefault(bid, f"ok ({len(triage.get('problems', []))} problems, verify: {n_conf} confirmed / {n_rev} revised / {n_rej} rejected)")

missing = sorted(inv_ids - set(final))
extra = sorted(set(final) - inv_ids)
dupes = [k for k, c in problems_seen.items() if c > 1]

out = {
    "problems": [final[k] for k in sorted(final)],
    "coverage": {
        "inventory": len(inv_ids),
        "audited": len(final),
        "missing": missing,
        "extra_ids_not_in_inventory": extra,
        "duplicate_ids": dupes,
    },
    "batch_status": batch_status,
}
json.dump(out, open(f"{SCRATCH}/final.json", "w"), indent=1)

cats = Counter(str(p["cat"]) for p in out["problems"])
print(f"audited {len(final)}/{len(inv_ids)}; missing {len(missing)}; extra {len(extra)}; dupes {len(dupes)}")
print("category histogram:", dict(sorted(cats.items(), key=lambda kv: int(kv[0]) if kv[0].isdigit() else 99)))
for b, s in sorted(batch_status.items()):
    if not s.startswith("ok"):
        print("  !!", b, s)
if missing[:10]:
    print("first missing:", missing[:10])
