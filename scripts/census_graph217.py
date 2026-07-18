#!/usr/bin/env python3
"""Exhaustively test WOWII Graph Conjecture 217 on graph8c."""
from __future__ import annotations

import itertools
import urllib.request

import networkx as nx

GRAPH8C = "https://raw.githubusercontent.com/balcilar/gnn-matlang/main/dataset/graph8c/raw/graph8c.g6"


def residue(g: nx.Graph) -> int:
    ds = sorted((d for _, d in g.degree()), reverse=True)
    while ds and ds[0] > 0:
        d = ds.pop(0)
        assert d <= len(ds)
        for i in range(d):
            ds[i] -= 1
        ds.sort(reverse=True)
    return len(ds)


def has_hamilton_path(g: nx.Graph) -> bool:
    n = len(g)
    adj = [sum(1 << w for w in g.neighbors(v)) for v in range(n)]
    dp = [0] * (1 << n)
    for v in range(n):
        dp[1 << v] = 1 << v
    for mask in range(1, 1 << n):
        ends = dp[mask]
        while ends:
            bit = ends & -ends
            v = bit.bit_length() - 1
            ends -= bit
            available = adj[v] & ~mask
            while available:
                wbit = available & -available
                available -= wbit
                dp[mask | wbit] |= wbit
    return dp[-1] != 0


def maximum_leaf_number(g: nx.Graph) -> int:
    """Use L(G) + gamma_c(G) = |V(G)| for connected |V| > 2."""
    n = len(g)
    all_vertices = set(g)
    for size in range(1, n + 1):
        for vertices in itertools.combinations(g.nodes(), size):
            chosen = set(vertices)
            if not nx.is_connected(g.subgraph(chosen)):
                continue
            dominated = chosen | set().union(*(set(g.neighbors(v)) for v in chosen))
            if dominated == all_vertices:
                return n - size
    raise AssertionError("connected dominating set not found")


def main() -> None:
    urllib.request.urlretrieve(GRAPH8C, "/tmp/graph8c.g6")
    graphs = nx.read_graph6("/tmp/graph8c.g6")
    total = residue_two = nontraceable = 0
    min_nontraceable_leaf = None
    violations: list[tuple[str, int, list[int]]] = []
    for g in graphs:
        total += 1
        if residue(g) != 2:
            continue
        residue_two += 1
        if has_hamilton_path(g):
            continue
        nontraceable += 1
        leaves = maximum_leaf_number(g)
        min_nontraceable_leaf = leaves if min_nontraceable_leaf is None else min(min_nontraceable_leaf, leaves)
        if leaves <= 6:
            code = nx.to_graph6_bytes(g, header=False).decode().strip()
            violations.append((code, leaves, sorted((d for _, d in g.degree()), reverse=True)))
    print(f"graphs={total}")
    print(f"residue_two={residue_two}")
    print(f"nontraceable_residue_two={nontraceable}")
    print(f"minimum_leaf_number_among_nontraceable_residue_two={min_nontraceable_leaf}")
    print(f"violations={violations}")
    if violations:
        raise SystemExit("Graph Conjecture 217 has an 8-vertex counterexample")


if __name__ == "__main__":
    main()
