#!/usr/bin/env python3
"""Reverse Havel--Hakimi certificate for the C217 order bound.

Starting from the terminal state [0,0], enumerate every nonincreasing list with
entries in 0..6 whose next Havel--Hakimi state is already known to terminate
with residue two. The reverse tree stops at length 15. All length-15 states
have odd sum, so an actual graph degree sequence (even sum) has length <= 14.
"""
from __future__ import annotations

from hashlib import sha256
from itertools import combinations_with_replacement
import json
from pathlib import Path

MAX_DEGREE = 6


def hh_step(s: tuple[int, ...]) -> tuple[int, ...]:
    assert s and s[0] > 0
    d, *rest = s
    for i in range(min(d, len(rest))):
        rest[i] = max(0, rest[i] - 1)
    return tuple(sorted(rest, reverse=True))


def sorted_states(length: int):
    """All nonincreasing lists of the given length with entries in 0..6."""
    for asc in combinations_with_replacement(range(MAX_DEGREE + 1), length):
        yield tuple(reversed(asc))


def build() -> dict[str, object]:
    levels: dict[int, set[tuple[int, ...]]] = {2: {(0, 0)}}
    n = 3
    while True:
        previous = levels[n - 1]
        nxt = {
            s for s in sorted_states(n)
            if s[0] > 0 and hh_step(s) in previous
        }
        levels[n] = nxt
        if not nxt:
            break
        n += 1

    assert n == 16
    length15 = sorted(levels[15], reverse=True)
    assert len(length15) == 11
    assert all(sum(s) % 2 == 1 for s in length15)
    assert not levels[16]

    total_states = sum(len(v) for v in levels.values())
    payload: dict[str, object] = {
        "format": "WOWII217-order-bound-reverse-hh-v1",
        "maximum_degree": MAX_DEGREE,
        "terminal_state": [0, 0],
        "total_states": total_states,
        "counts_by_length": {str(k): len(v) for k, v in sorted(levels.items())},
        "even_sum_counts_by_length": {
            str(k): sum(sum(s) % 2 == 0 for s in v)
            for k, v in sorted(levels.items())
        },
        "length_15_states": [list(s) for s in length15],
        "length_16_states": [],
        "conclusion": {
            "residue_two_maximum_length": 15,
            "even_sum_residue_two_maximum_length": 14,
        },
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    payload["sha256_without_digest"] = sha256(canonical).hexdigest()
    return payload


def main() -> None:
    payload = build()
    out = Path(__file__).with_name("c217_order_bound_certificate.json")
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "total_states": payload["total_states"],
        "counts_by_length": payload["counts_by_length"],
        "even_sum_counts_by_length": payload["even_sum_counts_by_length"],
        "length_15_states": payload["length_15_states"],
        "conclusion": payload["conclusion"],
        "sha256_without_digest": payload["sha256_without_digest"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
