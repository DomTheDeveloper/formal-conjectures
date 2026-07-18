# Fresh Formal-Conjectures attack

This branch attacks seven previously untouched targets:

- WOWII Graph Conjectures 103, 109, 145, 146, and 217;
- OEIS A067720;
- Erdős Problem 366.

Current mathematical results:

- Graph Conjecture 103 is false: an 11-vertex triangle with four private leaves at each of two triangle vertices has independence number 9, largest induced bipartite order 10, and average eccentricity 30/11.
- Graph Conjecture 109 is false: a connected 21-vertex three-gadget construction has independence number 15, largest induced bipartite order 18, and Havel--Hakimi residue 8.
- Graph Conjectures 145 and 146 have complete human proofs reducing the only exceptional case to a six-vertex induced-tree lemma in diameter four.
- `scripts/census_graph217.py` performs an exhaustive eight-vertex census for Graph Conjecture 217.

Lean formalization and the remaining two number-theory problems are in progress; this file intentionally makes no kernel-checked completion claim.
