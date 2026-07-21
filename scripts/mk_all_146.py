#!/usr/bin/env python3
"""Assemble and export the verified numbered WOWII 146 proof."""

from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PROOF_DIR = ROOT / "FormalConjectures" / "WrittenOnTheWallII"
WORK = PROOF_DIR / "GraphConjecture146Proof.lean"
FINAL = PROOF_DIR / "146.lean"

parts = sorted((ROOT / ".github").glob("wowii146-source.part*"))
if not parts:
    raise SystemExit("missing WOWII 146 source parts")

WORK.write_bytes(b"".join(part.read_bytes() for part in parts))
subprocess.run(
    [
        "patch",
        "-d",
        str(PROOF_DIR),
        "-p1",
        "-i",
        str(ROOT / ".github" / "wowii146-fix2.patch"),
    ],
    check=True,
)
WORK.replace(FINAL)

text = FINAL.read_text()
text = text.replace(
    "import FormalConjectures.WrittenOnTheWallII.GraphConjecture146",
    "import FormalConjecturesUtil",
    1,
)
definition = """namespace WrittenOnTheWallII.GraphConjecture146

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The radius of the square graph. -/
noncomputable def graphSquareRadius (G : SimpleGraph α) : ℕ :=
  (graphSquare G).radius.toNat

end WrittenOnTheWallII.GraphConjecture146

namespace SimpleGraph
"""
text = text.replace("namespace SimpleGraph\n", definition, 1)
text = text.replace("conjecture146_proved", "conjecture146")
text = text.replace("@[category API, AMS 5]", "@[category research solved, AMS 5]", 1)
FINAL.write_text(text)

# Recreate the aggregate import file expected by the standard workflow.
def lean_segment(segment: str) -> str:
    return f"«{segment}»" if re.match(r"^\d", segment) else segment

modules: list[str] = []
for path in sorted((ROOT / "FormalConjectures").rglob("*.lean")):
    if path.name == "All.lean":
        continue
    rel = path.relative_to(ROOT).with_suffix("")
    modules.append(".".join(lean_segment(part) for part in rel.parts))

(ROOT / "FormalConjectures.lean").write_text(
    "\n".join(f"import {module}" for module in modules) + "\n"
)

# The standard website build copies src/img into the Pages artifact.
export_dir = ROOT / "site" / "src" / "img"
export_dir.mkdir(parents=True, exist_ok=True)
shutil.copy2(FINAL, export_dir / "146.lean")

print(f"assembled {FINAL.relative_to(ROOT)} ({FINAL.stat().st_size} bytes)")
print(f"generated {len(modules)} aggregate imports")
