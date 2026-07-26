#!/usr/bin/env python3
"""Extract every @[category research open] declaration from FormalConjectures/.

Produces inventory.json: list of records with file, line, theorem name,
docstring, attribute text, AMS codes, answer() usage, statement source,
and per-file module docstring/reference info.
"""
import json
import os
import re
import sys

ROOT = "/home/user/formal-conjectures"
SRC = os.path.join(ROOT, "FormalConjectures")
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "inventory.json")

# Files that mention 'research open' only as documentation/tests of the attribute machinery.
EXCLUDE_DIRS = {os.path.join(SRC, "Util")}

ATTR_RE = re.compile(r"@\[(?P<attr>[^\]]*?category\s+research\s+open[^\]]*)\]", re.DOTALL)
DECL_RE = re.compile(r"\s*(?P<kw>theorem|lemma|def|abbrev|instance)\s+(?P<name>[^\s:({\[]+)")
AMS_RE = re.compile(r"AMS\s+((?:\d+\s*)+)")


def find_docstring_before(text, attr_start):
    """Find /-- ... -/ docstring immediately preceding attr_start."""
    prefix = text[:attr_start].rstrip()
    if not prefix.endswith("-/"):
        return None
    open_idx = prefix.rfind("/--")
    if open_idx == -1:
        return None
    return prefix[open_idx + 3 : len(prefix) - 2].strip()


def find_module_docstring(text):
    m = re.search(r"/-!(.*?)-/", text, re.DOTALL)
    return m.group(1).strip() if m else None


def statement_source(text, attr_start, decl_body_start):
    """Grab attribute + declaration source until the next top-level item."""
    tail = text[decl_body_start:]
    end = len(tail)
    m = re.search(r"\n(?=(/--|/-!|@\[|namespace |end |section |open |theorem |lemma |def |abbrev ))", tail)
    if m:
        end = m.start()
    return (text[attr_start:decl_body_start] + tail[:end]).strip()[:4000]


records = []
for dirpath, _dirnames, filenames in os.walk(SRC):
    if any(dirpath.startswith(e) for e in EXCLUDE_DIRS):
        continue
    for fn in sorted(filenames):
        if not fn.endswith(".lean"):
            continue
        path = os.path.join(dirpath, fn)
        rel = os.path.relpath(path, ROOT)
        with open(path) as f:
            text = f.read()
        module_doc = find_module_docstring(text)
        refs = re.findall(r"\[([^\]]+)\]\((https?://[^)]+)\)", module_doc or "")
        for am in ATTR_RE.finditer(text):
            attr = re.sub(r"\s+", " ", am.group("attr")).strip()
            decl_start = am.end()
            dm = DECL_RE.match(text, decl_start)
            if not dm:
                # attribute not directly followed by a decl (e.g. docs) — skip
                continue
            name = dm.group("name")
            line = text.count("\n", 0, am.start()) + 1
            doc = find_docstring_before(text, am.start())
            ams = AMS_RE.search(attr)
            stmt = statement_source(text, am.start(), dm.end())
            records.append(
                {
                    "id": f"{rel}:{name}",
                    "file": rel,
                    "line": line,
                    "kind": dm.group("kw"),
                    "name": name,
                    "attr": attr,
                    "ams": ams.group(1).split() if ams else [],
                    "docstring": doc,
                    "uses_answer": "answer(" in stmt,
                    "statement": stmt,
                    "module_refs": refs,
                }
            )

with open(OUT, "w") as f:
    json.dump(records, f, indent=1)

from collections import Counter

dirs = Counter(r["file"].split("/")[1] for r in records)
print(f"extracted {len(records)} research-open declarations from {len(set(r['file'] for r in records))} files")
for d, c in dirs.most_common():
    print(f"  {d}: {c}")
missing_doc = [r["id"] for r in records if not r["docstring"]]
print(f"missing docstring: {len(missing_doc)}")
for x in missing_doc[:10]:
    print("   ", x)
