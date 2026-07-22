#!/usr/bin/env python3
"""Deterministic certificate builder for WOWII Conjecture 217.

This script has two jobs:
  1. enumerate every positive graphical degree sequence of order <= 14,
     maximum degree <= 6, Havel--Hakimi residue 2, and failure of the
     Chvatal path criterion;
  2. classify the resulting 40 sequences into reusable proof families.

The low-minimum-degree sublist (minimum degree <= 3) has exactly 22 rows.
No graph-generation package or randomized step is used.
"""
from __future__ import annotations

from collections import Counter
from dataclasses import asdict, dataclass
from hashlib import sha256
from itertools import combinations_with_replacement
import json
from pathlib import Path


def hh_step_desc(s: tuple[int, ...]) -> tuple[int, ...] | None:
    if not s:
        return ()
    d, *rest = s
    if d > len(rest):
        return None
    for i in range(d):
        rest[i] -= 1
        if rest[i] < 0:
            return None
    return tuple(sorted(rest, reverse=True))


def residue_and_graphical(s: tuple[int, ...]) -> tuple[int, bool]:
    cur = tuple(sorted(s, reverse=True))
    while cur and cur[0] != 0:
        nxt = hh_step_desc(cur)
        if nxt is None:
            return 0, False
        cur = nxt
    return len(cur), True


def chvatal_path_holds(desc: tuple[int, ...]) -> bool:
    asc = tuple(reversed(desc))
    n = len(asc)
    for i in range(1, (n + 1) // 2 + 1):
        if 2 * i >= n + 1:
            continue
        if asc[i - 1] < i and asc[n - i] < n - i:
            return False
    return True


def enumerate_exceptions() -> list[tuple[int, ...]]:
    rows: list[tuple[int, ...]] = []
    for n in range(2, 15):
        for asc in combinations_with_replacement(range(1, min(6, n - 1) + 1), n):
            desc = tuple(reversed(asc))
            if sum(desc) % 2:
                continue
            residue, graphical = residue_and_graphical(desc)
            if not graphical or residue != 2 or chvatal_path_holds(desc):
                continue
            rows.append(desc)
    return rows


def is_regular_boundary(s: tuple[int, ...]) -> bool:
    return len(set(s)) == 1 and len(s) == 2 * s[0] + 2


def parametric_parameters(s: tuple[int, ...]) -> tuple[int, int] | None:
    """Recognize `(h-1)^h, q^(q+1)` with h >= q+2."""
    counts = Counter(s)
    if len(counts) != 2:
        return None
    hi, lo = max(counts), min(counts)
    h, q = hi + 1, lo
    if counts[hi] == h and counts[lo] == q + 1 and h >= q + 2:
        return h, q
    return None


LOW_SEED = {
    (3, 3, 2, 2, 2, 2),
    (4, 4, 4, 3, 3, 3, 3, 2),
    (4, 4, 3, 3, 3, 3, 3, 3),
    (5, 4, 4, 3, 3, 3, 3, 3),
    (5, 5, 5, 5, 4, 4, 4, 4, 3, 3),
    (6, 5, 5, 5, 4, 4, 4, 4, 4, 3),
}
LOW_TWO_STAGE = {(5, 5, 5, 4, 4, 4, 4, 4, 4, 3)}

HIGH_CLOSURE = {
    (5, 5, 4, 4, 4, 4, 4, 4, 4, 4),
    (6, 5, 5, 4, 4, 4, 4, 4, 4, 4),
    (5, 5, 5, 5, 4, 4, 4, 4, 4, 4),
    (6, 6, 5, 5, 4, 4, 4, 4, 4, 4),
    (6, 6, 6, 6, 5, 5, 4, 4, 4, 4, 4),
    (6, 6, 6, 6, 6, 5, 5, 5, 5, 4, 4, 4),
    (6, 6, 6, 6, 5, 5, 5, 5, 5, 5, 4, 4),
    (6, 6, 6, 5, 5, 5, 5, 5, 5, 5, 5, 4),
    (6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5, 4),
    (6, 6, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5),
    (6, 6, 6, 6, 5, 5, 5, 5, 5, 5, 5, 5),
}
HIGH_LEAF_OBSTRUCTION = {(6, 6, 6, 6, 4, 4, 4, 4, 4, 4)}
IMPOSSIBLE_CONNECTED = {(1, 1, 1, 1)}


@dataclass(frozen=True)
class Row:
    index: int
    sequence: list[int]
    order: int
    minimum_degree: int
    proof_family: str
    parameters: dict[str, int]


def classify(index: int, s: tuple[int, ...]) -> Row:
    parameters: dict[str, int] = {}
    if s in IMPOSSIBLE_CONNECTED:
        family = "impossible_connected"
    elif is_regular_boundary(s):
        family = "regular_boundary"
        parameters = {"k": s[0], "order": len(s)}
    elif (hq := parametric_parameters(s)) is not None:
        family = "parametric_two_block_closure"
        parameters = {"h": hq[0], "q": hq[1]}
    elif s in LOW_SEED:
        family = "low_seed_completion"
    elif s in LOW_TWO_STAGE:
        family = "low_two_stage_completion"
    elif s in HIGH_CLOSURE:
        family = "high_delta_closure"
    elif s in HIGH_LEAF_OBSTRUCTION:
        family = "high_delta_leaf_obstruction"
        parameters = {"forced_leaves": 8}
    else:
        raise AssertionError(f"unclassified certificate row {index}: {s}")
    return Row(index, list(s), len(s), min(s), family, parameters)


def build_manifest() -> dict[str, object]:
    exceptions = enumerate_exceptions()
    rows = [classify(i, s) for i, s in enumerate(exceptions, 1)]
    low = [r for r in rows if r.minimum_degree <= 3]
    assert len(exceptions) == 40
    assert len(low) == 22
    assert len({tuple(r.sequence) for r in rows}) == 40
    families = Counter(r.proof_family for r in rows)
    assert sum(families.values()) == 40
    payload = {
        "format": "WOWII217-degree-sequence-certificate-v1",
        "constraints": {
            "orders": [2, 14],
            "positive_degrees": True,
            "maximum_degree": 6,
            "havel_hakimi_residue": 2,
            "chvatal_path_criterion": False,
        },
        "counts": {
            "all": len(rows),
            "minimum_degree_at_most_3": len(low),
            "by_order": dict(sorted(Counter(r.order for r in rows).items())),
            "by_family": dict(sorted(families.items())),
        },
        "rows": [asdict(r) for r in rows],
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    payload["sha256_without_digest"] = sha256(canonical).hexdigest()
    return payload


def main() -> None:
    manifest = build_manifest()
    out = Path(__file__).with_name("c217_certificate.json")
    out.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(json.dumps(manifest["counts"], indent=2, sort_keys=True))
    print(f"wrote {out}")
    print(f"sha256_without_digest={manifest['sha256_without_digest']}")


if __name__ == "__main__":
    main()
