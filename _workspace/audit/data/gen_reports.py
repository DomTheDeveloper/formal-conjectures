#!/usr/bin/env python3
"""Generate _workspace/audit/ markdown reports from final.json."""
import json
import os
from collections import defaultdict, Counter

SCRATCH = os.path.dirname(os.path.abspath(__file__))
REPO = "/home/user/formal-conjectures"
AUD = os.path.join(REPO, "_workspace", "audit")
os.makedirs(AUD, exist_ok=True)
os.makedirs(os.path.join(AUD, "data"), exist_ok=True)

data = json.load(open(f"{SCRATCH}/final.json"))
problems = data["problems"]
inv = {r["id"]: r for r in json.load(open(f"{SCRATCH}/inventory.json"))}

CAT_NAMES = {
    0: "Already solved internally",
    1: "Already solved externally",
    2: "Trivially or easily solvable",
    3: "False / refutable as stated",
    4: "Vacuously true / accidentally weakened",
    5: "Solved mathematically, not yet formalized",
    6: "Computationally solvable with certificate",
    7: "Plausibly solvable with moderate formal work",
    8: "Deep but approachable research problem",
    9: "Major open problem / currently infeasible",
    10: "Cannot classify without correction/clarification",
}


def esc(s):
    return (s or "").replace("|", "\\|").replace("\n", " ").strip()


def fileline(pid):
    f, _, name = pid.rpartition(":")
    r = inv.get(pid)
    return f"{f}:{r['line']}" if r else f


# ---------- INDEX.md ----------
rows = []
for p in sorted(problems, key=lambda p: p["id"]):
    f, _, name = p["id"].rpartition(":")
    short = f.replace("FormalConjectures/", "")
    rows.append(
        f"| `{short}` | `{name}` | {p['cat']} | {p.get('cat2') if p.get('cat2') is not None else ''} "
        f"| {p['match']} | {p['mdiff']}/{p['ldiff']} | {p['compute']} | {p['conf']} | {esc(p['action'])[:110]} |"
    )
cats = Counter(p["cat"] for p in problems)
hist = "\n".join(
    f"| {c} | {CAT_NAMES[c]} | {cats.get(c, 0)} |" for c in range(11)
)
with open(f"{AUD}/INDEX.md", "w") as fh:
    fh.write(f"""# Master audit index

**{len(problems)}** `research open` declarations audited (of {data['coverage']['inventory']} in inventory).
Coverage gaps: {len(data['coverage']['missing'])} missing, {len(data['coverage']['duplicate_ids'])} duplicated.
See [README.md](./README.md) for methodology and category definitions; per-directory detail reports carry the full 13 audit fields per problem.

## Category histogram

| Cat | Meaning | Count |
|---|---|---|
{hist}

## All problems

Columns: **Cat** = primary category, **Cat2** = secondary, **Match** = does the Lean statement match the intended problem (yes/suspect/no),
**M/L** = mathematical / Lean difficulty (1-10), **Compute** = compute requirement, **Conf** = confidence.

| File | Declaration | Cat | Cat2 | Match | M/L | Compute | Conf | Next action |
|---|---|---|---|---|---|---|---|---|
""" + "\n".join(rows) + "\n")

# ---------- per-directory reports ----------
bydir = defaultdict(list)
for p in problems:
    d = p["id"].split("/")[1]
    bydir[d].append(p)

for d, plist in sorted(bydir.items()):
    lines = [f"# Audit detail — {d}", "",
             f"{len(plist)} research-open declarations. Fields per problem: plain statement, source, category, match, status, action, difficulties, compute, confidence, evidence, flags.",
             ""]
    for p in sorted(plist, key=lambda p: p["id"]):
        f, _, name = p["id"].rpartition(":")
        lines.append(f"## `{name}` — {CAT_NAMES[p['cat']]} (cat {p['cat']})")
        lines.append("")
        lines.append(f"**File:** `{fileline(p['id'])}`  ")
        if p.get("cat2") is not None:
            lines.append(f"**Secondary category:** {p['cat2']} ({CAT_NAMES.get(p['cat2'], '?')})  ")
        lines.append(f"**Statement:** {p['plain']}  ")
        lines.append(f"**Source:** {p['source']}  ")
        lines.append(f"**Statement matches intent:** {p['match']}"
                     + (f" — {p['match_note']}" if p.get("match_note") and p["match"] != "yes" else "") + "  ")
        lines.append(f"**Known status:** {p['status']}  ")
        lines.append(f"**Difficulty:** math {p['mdiff']}/10, Lean {p['ldiff']}/10 · **Compute:** {p['compute']} · **Confidence:** {p['conf']}  ")
        lines.append(f"**Evidence:** {p['evidence']}  ")
        if p.get("flags"):
            lines.append(f"**Flags:** {'; '.join(p['flags'])}  ")
        if p.get("verifier_notes"):
            lines.append(f"**Verifier:** {p['verifier_notes']} (triage said cat {p.get('triage_cat')})  ")
        lines.append(f"**Next action:** {p['action']}")
        lines.append("")
    open(f"{AUD}/{d}.md", "w").write("\n".join(lines))

# ---------- PRIORITIES.md ----------
def bucket(p):
    c, comp = p["cat"], p["compute"]
    if c == 0:
        return 0
    if c == 1:
        return 1
    if c in (3, 4, 10):
        return 2
    if c == 2:
        return 3
    if c == 6 and comp in ("none", "small"):
        return 4
    if c == 5:
        return 5
    if c == 7 or c == 6:
        return 6
    if c == 8:
        return 7
    return 8

BUCKETS = [
    "0. Internal proofs to port/merge (category 0 — fastest wins)",
    "1. External solutions to import (category 1)",
    "2. Defective statements needing correction (categories 3, 4, 10)",
    "3. Easy direct Lean proofs (category 2)",
    "4. Small certificate-based finite problems (category 6, small compute)",
    "5. Mathematically solved, moderate formalization (category 5)",
    "6. Tractable unsolved with clear strategies (category 7 + heavier 6)",
    "7. Deep research problems (category 8)",
    "8. Major open problems (category 9)",
]
bybucket = defaultdict(list)
for p in problems:
    bybucket[bucket(p)].append(p)

CONF_ORD = {"high": 0, "medium": 1, "low": 2}
lines = ["# Prioritized work queue", "",
         "Ranked per the audit prioritization order. Within a bucket, sorted by confidence then Lean difficulty.",
         "Every 'solved/solvable' claim below is static-analysis only until a `lake --wfail build` and axiom audit pass — see README verification standards.", ""]
for b, title in enumerate(BUCKETS):
    plist = sorted(bybucket.get(b, []), key=lambda p: (CONF_ORD.get(p["conf"], 3), p["ldiff"]))
    lines.append(f"## {title}  ({len(plist)})")
    lines.append("")
    if b <= 6:
        for p in plist:
            f, _, name = p["id"].rpartition(":")
            short = f.replace("FormalConjectures/", "")
            lines.append(f"- **`{short}:{name}`** (cat {p['cat']}, conf {p['conf']}, L{p['ldiff']}, {p['compute']}) — {esc(p['action'])[:200]}")
    else:
        lines.append(f"{len(plist)} problems — see per-directory reports; not individually queued.")
    lines.append("")
open(f"{AUD}/PRIORITIES.md", "w").write("\n".join(lines))

print("wrote INDEX.md, PRIORITIES.md, and", len(bydir), "directory reports to", AUD)
print("bucket sizes:", {BUCKETS[b].split(".")[0]: len(v) for b, v in sorted(bybucket.items())})
