#!/usr/bin/env python3
"""Integrate the Green14 finite-certificate proof into the catalog file.

The script intentionally uses exact source strings and aborts if the branch no
longer has the expected shape.  It is idempotent after a successful run.
"""

from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CATALOG = ROOT / "FormalConjectures/GreensOpenProblems/14.lean"
CERTS = ROOT / "FormalConjectures/GreensOpenProblems/Green14Certificates.lean"
FINITE = ROOT / "FormalConjectures/GreensOpenProblems/Green14FiniteExistence.lean"

OLD_CATALOG_IMPORT = "import FormalConjectures.Util.ProblemImports"
NEW_CATALOG_IMPORT = (
    "import FormalConjectures.GreensOpenProblems.Green14CertificateBridge"
)
OLD_PROOF_IMPORT = "import FormalConjectures.GreensOpenProblems.«14»"
NEW_PROOF_IMPORT = "import FormalConjectures.GreensOpenProblems.Green14Core"

BOUNDS = {
    20: (389, "ge"),
    21: (416, "ge"),
    22: (464, "ge"),
    23: (516, "ge"),
    24: (593, "ge"),
    25: (656, "ge"),
    26: (727, "ge"),
    27: (770, "ge"),
    28: (827, "ge"),
    29: (868, "ge"),
    30: (903, "ge"),
    31: (930, "gt"),
    32: (1006, "gt"),
    33: (1063, "gt"),
    34: (1143, "gt"),
    35: (1204, "gt"),
    36: (1257, "gt"),
    37: (1338, "gt"),
    38: (1378, "gt"),
    39: (1418, "gt"),
}


def replace_once(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count == 0 and new in text:
        return text
    if count != 1:
        raise SystemExit(f"{label}: expected one occurrence, found {count}")
    return text.replace(old, new, 1)


def patch_proof_import(path: Path) -> None:
    text = path.read_text()
    text = replace_once(text, OLD_PROOF_IMPORT, NEW_PROOF_IMPORT, str(path))
    path.write_text(text)


def direct_proof(t: int, relation: str) -> str:
    if relation == "ge":
        body = f"    exact CertificateBridge.W_3_{t}_lower_proved"
    else:
        body = (
            f"    have h := CertificateBridge.W_3_{t}_lower_proved\n"
            "    omega"
        )
    return "by\n  constructor\n  · intro _\n" + body + "\n  · intro _\n    trivial"


def patch_catalog() -> None:
    text = CATALOG.read_text()
    text = replace_once(text, OLD_CATALOG_IMPORT, NEW_CATALOG_IMPORT, str(CATALOG))

    definitions_start = "/--\nThe set of natural numbers $N$ such that any 2-coloring"
    next_section = "/--\nIs $W(k, r)$ a polynomial in $r$, for fixed $k$?"
    if definitions_start in text:
        start = text.index(definitions_start)
        end = text.index(next_section, start)
        text = text[:start] + next_section + text[end + len(next_section):]
    elif "def mixedMonoAPGuaranteeSet" in text or "noncomputable def W" in text:
        raise SystemExit("catalog core definitions are present in an unexpected shape")

    for t, (bound, relation) in BOUNDS.items():
        op = "≥" if relation == "ge" else ">"
        old = (
            f"theorem W_3_{t}_lower : answer(sorry) ↔ "
            f"W 3 {t} {op} {bound} := sorry"
        )
        new = (
            f"theorem W_3_{t}_lower : answer(sorry) ↔ "
            f"W 3 {t} {op} {bound} := {direct_proof(t, relation)}"
        )
        if old in text:
            text = text.replace(old, new, 1)
        elif new not in text:
            raise SystemExit(f"catalog theorem W_3_{t}_lower has an unexpected shape")

    unresolved = re.findall(
        r"theorem W_3_(?:2[0-9]|3[0-9])_lower[^\n]*:= sorry", text
    )
    if unresolved:
        raise SystemExit(f"unresolved lower-bound placeholders: {unresolved}")
    CATALOG.write_text(text)


def main() -> int:
    patch_proof_import(CERTS)
    patch_proof_import(FINITE)
    patch_catalog()
    print("Green14 catalog integration complete")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
