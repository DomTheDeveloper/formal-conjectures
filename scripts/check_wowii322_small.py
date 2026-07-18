#!/usr/bin/env python3
"""Independent small-order census for WOWII Graph Conjecture 322.

For n=5 and n=6, enumerate every labeled simple graph and verify that the only
connected graph whose every open neighborhood is a clique is K_n.  The Lean
proof establishes this for arbitrary finite n by propagation along paths; this
script is an independent finite regression check.
"""

from itertools import combinations


def is_connected(n: int, edge_set: set[tuple[int, int]]) -> bool:
    seen = {0}
    stack = [0]
    while stack:
        u = stack.pop()
        for v in range(n):
            if u == v:
                continue
            edge = (u, v) if u < v else (v, u)
            if edge in edge_set and v not in seen:
                seen.add(v)
                stack.append(v)
    return len(seen) == n


def all_neighborhoods_are_cliques(n: int, edge_set: set[tuple[int, int]]) -> bool:
    for v in range(n):
        neighbors = []
        for u in range(n):
            if u == v:
                continue
            edge = (u, v) if u < v else (v, u)
            if edge in edge_set:
                neighbors.append(u)
        for a, b in combinations(neighbors, 2):
            if (a, b) not in edge_set:
                return False
    return True


def census(n: int) -> tuple[int, int]:
    edges = list(combinations(range(n), 2))
    survivors = 0
    noncomplete_survivors = 0

    for mask in range(1 << len(edges)):
        edge_set = {edges[i] for i in range(len(edges)) if (mask >> i) & 1}
        if not is_connected(n, edge_set):
            continue
        if not all_neighborhoods_are_cliques(n, edge_set):
            continue
        survivors += 1
        if len(edge_set) != len(edges):
            noncomplete_survivors += 1

    return survivors, noncomplete_survivors


def main() -> None:
    for n in (5, 6):
        survivors, noncomplete = census(n)
        assert survivors == 1, (n, survivors)
        assert noncomplete == 0, (n, noncomplete)
        print(f"n={n}: survivors={survivors}, noncomplete={noncomplete}")


if __name__ == "__main__":
    main()
