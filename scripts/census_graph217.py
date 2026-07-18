#!/usr/bin/env python3
"""Exhaustively test WOWII Graph Conjecture 217 through order nine.

Every graph on n+1 vertices is obtained by adding one vertex to a graph on n
vertices.  NetworkX's graph atlas supplies every isomorphism class through
order seven.  We augment all seven-vertex atlas graphs to cover order eight,
then canonically deduplicate those augmentations and augment the resulting
8-vertex representatives to cover order nine.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from functools import lru_cache
import itertools

import networkx as nx


def graph_to_adj(g: nx.Graph) -> list[int]:
    adj = [0] * len(g)
    for u, v in g.edges():
        adj[u] |= 1 << v
        adj[v] |= 1 << u
    return adj


def adj_to_graph(adj: list[int]) -> nx.Graph:
    g = nx.Graph()
    g.add_nodes_from(range(len(adj)))
    for u in range(len(adj)):
        for v in range(u + 1, len(adj)):
            if adj[u] >> v & 1:
                g.add_edge(u, v)
    return g


def add_vertex(adj: list[int], neighborhood: int) -> list[int]:
    n = len(adj)
    out = adj.copy() + [0]
    for v in range(n):
        if neighborhood >> v & 1:
            out[v] |= 1 << n
            out[n] |= 1 << v
    return out


def connected(adj: list[int]) -> bool:
    seen = frontier = 1
    while frontier:
        neighbors = 0
        todo = frontier
        while todo:
            bit = todo & -todo
            todo -= bit
            neighbors |= adj[bit.bit_length() - 1]
        frontier = neighbors & ~seen
        seen |= frontier
    return seen == (1 << len(adj)) - 1


def residue(adj: list[int]) -> int:
    degrees = sorted((neighbors.bit_count() for neighbors in adj), reverse=True)
    while degrees and degrees[0] > 0:
        d = degrees.pop(0)
        assert d <= len(degrees)
        for i in range(d):
            degrees[i] -= 1
        degrees.sort(reverse=True)
    return len(degrees)


def has_hamilton_path(adj: list[int]) -> bool:
    n = len(adj)
    full = (1 << n) - 1

    @lru_cache(maxsize=None)
    def extend(last: int, visited: int) -> bool:
        if visited == full:
            return True
        available = adj[last] & ~visited
        candidates: list[tuple[int, int, int]] = []
        while available:
            bit = available & -available
            available -= bit
            v = bit.bit_length() - 1
            candidates.append(((adj[v] & ~(visited | bit)).bit_count(), v, bit))
        candidates.sort()
        return any(extend(v, visited | bit) for _, v, bit in candidates)

    return any(extend(v, 1 << v) for v in sorted(range(n), key=lambda x: adj[x].bit_count()))


def invariant_key(g: nx.Graph) -> tuple[object, ...]:
    """Strong isomorphism invariant; exact isomorphism is checked inside each bucket."""
    return (
        g.number_of_edges(),
        tuple(sorted((d for _, d in g.degree()), reverse=True)),
        tuple(sorted((len(c) for c in nx.connected_components(g)), reverse=True)),
        tuple(sorted(nx.triangles(g).values(), reverse=True)),
        nx.weisfeiler_lehman_graph_hash(g, iterations=8),
    )


def unique_eight_vertex_graphs(atlas7: list[nx.Graph]) -> list[list[int]]:
    buckets: dict[tuple[object, ...], list[nx.Graph]] = defaultdict(list)
    representatives: list[list[int]] = []
    for base in atlas7:
        base_adj = graph_to_adj(base)
        for neighborhood in range(1 << 7):
            adj = add_vertex(base_adj, neighborhood)
            g = adj_to_graph(adj)
            bucket = buckets[invariant_key(g)]
            if any(nx.is_isomorphic(g, old) for old in bucket):
                continue
            bucket.append(g)
            representatives.append(adj)
    assert len(representatives) == 12_346  # number of unlabeled graphs on eight vertices
    return representatives


def census(base_graphs: list[list[int]]) -> Counter[str]:
    stats: Counter[str] = Counter()
    for base in base_graphs:
        for neighborhood in range(1, 1 << len(base)):
            adj = add_vertex(base, neighborhood)
            stats["augmentations"] += 1
            if not connected(adj):
                continue
            stats["connected"] += 1
            if residue(adj) != 2:
                continue
            stats["residue_two"] += 1
            if not has_hamilton_path(adj):
                stats["nontraceable_residue_two"] += 1
                code = nx.to_graph6_bytes(adj_to_graph(adj), header=False).decode().strip()
                raise AssertionError(f"nontraceable residue-two graph found: {code}")
    return stats


def main() -> None:
    atlas7 = [g for g in nx.graph_atlas_g() if len(g) == 7]
    assert len(atlas7) == 1_044

    order8 = census([graph_to_adj(g) for g in atlas7])
    assert order8 == Counter(
        augmentations=132_588,
        connected=119_980,
        residue_two=42_434,
    )

    representatives8 = unique_eight_vertex_graphs(atlas7)
    order9 = census(representatives8)
    assert order9 == Counter(
        augmentations=3_148_230,
        connected=2_991_154,
        residue_two=925_296,
    )

    print(f"order8={dict(order8)}")
    print(f"order9={dict(order9)}")
    print("Every connected graph through order nine with Havel-Hakimi residue two is traceable.")


if __name__ == "__main__":
    main()
