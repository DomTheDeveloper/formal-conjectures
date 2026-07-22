#!/usr/bin/env python3
"""Deterministically audit every symmetry reduction used by the N=6, D=3 proof.

No SAT solving occurs here. The script enumerates all 15 perfect matchings of
K6 and all 720 vertex permutations, then verifies:

* one active colour-0 matching may be normalized to M0;
* under Stab(M0), colour 1 has exactly the three orbit types
  same / four-plus-two / six-cycle;
* under Stab(M0,M1_six), colour 2 has exactly seven ordered-orbit types;
* five of those seven are already same/four-plus-two, one is the triangular
  prism factorisation, and one is the K3,3 factorisation;
* under the ordered K3,3 triple stabilizer, the three selected residual bits
  form one C3 orbit, with exactly four Boolean orbit representatives.
"""

from __future__ import annotations

import itertools
import json
from collections import defaultdict

from quantum_mod2_cnf import (
    M0,
    M1_CASES,
    color2_orbit_representatives,
    normalize_matching,
    perfect_matchings,
    permute_matching,
)

VERTICES = tuple(range(6))
ALL_PERMS = tuple(itertools.permutations(VERTICES))
ALL_MATCHINGS = tuple(sorted(set(perfect_matchings(VERTICES))))


def stabilizer(*matchings):
    normalized = tuple(normalize_matching(m) for m in matchings)
    return tuple(
        p for p in ALL_PERMS
        if all(permute_matching(m, p) == m for m in normalized)
    )


def orbits(items, group, action):
    unseen = set(items)
    result = []
    while unseen:
        rep = min(unseen)
        orb = {action(rep, p) for p in group}
        result.append((rep, tuple(sorted(orb))))
        unseen.difference_update(orb)
    return tuple(result)


def shared_edges(a, b):
    return len(set(normalize_matching(a)) & set(normalize_matching(b)))


def union_degrees(*matchings):
    degrees = [0] * 6
    for matching in matchings:
        for u, v in normalize_matching(matching):
            degrees[u] += 1
            degrees[v] += 1
    return tuple(degrees)


def bipartite_union(*matchings):
    adjacency = [set() for _ in range(6)]
    for matching in matchings:
        for u, v in normalize_matching(matching):
            adjacency[u].add(v)
            adjacency[v].add(u)
    colour = {}
    for start in range(6):
        if start in colour:
            continue
        colour[start] = 0
        stack = [start]
        while stack:
            u = stack.pop()
            for v in adjacency[u]:
                if v not in colour:
                    colour[v] = 1 - colour[u]
                    stack.append(v)
                elif colour[v] == colour[u]:
                    return False
    return True


def permute_edge(edge, p):
    u, v = edge
    return tuple(sorted((p[u], p[v])))


def main() -> None:
    assert len(ALL_MATCHINGS) == 15
    m0 = normalize_matching(M0)

    # S6 is transitive on perfect matchings.
    full_orbits = orbits(ALL_MATCHINGS, ALL_PERMS, permute_matching)
    assert len(full_orbits) == 1
    assert len(full_orbits[0][1]) == 15

    stab0 = stabilizer(m0)
    colour1_orbits = orbits(ALL_MATCHINGS, stab0, permute_matching)
    assert len(colour1_orbits) == 3
    c1_reps = tuple(rep for rep, _ in colour1_orbits)
    expected_c1 = tuple(sorted(normalize_matching(m) for m in M1_CASES.values()))
    assert tuple(sorted(c1_reps)) == expected_c1

    m1 = normalize_matching(M1_CASES["six_cycle"])
    c2_reps = tuple(color2_orbit_representatives("six_cycle"))
    assert len(c2_reps) == 7

    classification = []
    prism = None
    k33 = None
    for index, m2 in enumerate(c2_reps):
        s0 = shared_edges(m2, m0)
        s1 = shared_edges(m2, m1)
        if m2 == m0:
            kind = "same_as_color0"
        elif m2 == m1:
            kind = "same_as_color1"
        elif s0 or s1:
            kind = "four_plus_two"
        else:
            assert union_degrees(m0, m1, m2) == (3, 3, 3, 3, 3, 3)
            if bipartite_union(m0, m1, m2):
                kind = "K3,3"
                k33 = m2
            else:
                kind = "triangular_prism"
                prism = m2
        classification.append({
            "index": index,
            "matching": m2,
            "shared_with_color0": s0,
            "shared_with_color1": s1,
            "kind": kind,
        })

    assert [row["kind"] for row in classification] == [
        "same_as_color0",
        "four_plus_two",
        "four_plus_two",
        "same_as_color1",
        "four_plus_two",
        "triangular_prism",
        "K3,3",
    ]
    assert prism is not None and k33 is not None

    # Ordered triple stabilizer in the sole remaining K3,3 case.
    stab012 = stabilizer(m0, m1, k33)
    residual_edges = ((0, 2), (3, 5), (1, 4))
    residual_set = set(residual_edges)
    induced_actions = set()
    for p in stab012:
        image = tuple(permute_edge(e, p) for e in residual_edges)
        if set(image) == residual_set:
            induced_actions.add(tuple(residual_edges.index(e) for e in image))

    # The induced action contains the 3-cycle and is exactly C3 on this orbit.
    assert induced_actions == {(0, 1, 2), (1, 2, 0), (2, 0, 1)}

    patterns = tuple(itertools.product((0, 1), repeat=3))

    def act_pattern(pattern, action):
        out = [0, 0, 0]
        for old_index, new_index in enumerate(action):
            out[new_index] = pattern[old_index]
        return tuple(out)

    pattern_orbits = orbits(patterns, induced_actions, act_pattern)
    representatives = tuple(rep for rep, _ in pattern_orbits)
    assert representatives == ((0, 0, 0), (0, 0, 1), (0, 1, 1), (1, 1, 1))

    report = {
        "perfect_matching_count": len(ALL_MATCHINGS),
        "full_matching_orbits": len(full_orbits),
        "stabilizer_M0_size": len(stab0),
        "color1_orbit_representatives": c1_reps,
        "six_cycle_color2_classification": classification,
        "ordered_K33_stabilizer_size": len(stab012),
        "residual_edge_orbit": residual_edges,
        "induced_residual_actions": sorted(induced_actions),
        "boolean_orbit_representatives": representatives,
    }
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
