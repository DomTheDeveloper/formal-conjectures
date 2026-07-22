# WOWII Conjecture 2 — proof architecture

Let

- `a(v) = α(G[N(v)])`,
- `S = Σ_v a(v)`,
- `n = |V(G)|`, and
- `M = max_{xy ∈ E(G)} |N(x) ∪ N(y)|`.

We prove

`2 * averageIndepNeighbors(G) ≤ M ≤ Ls(G) + 2`.

The desired inequality follows immediately.

## 1. Double-counting bound

For every vertex `v`, choose a maximum independent set

`I_v ⊆ N(v)`, with `|I_v| = a(v)`.

For each incidence `u ∈ I_v`, independence of `I_v` gives

`I_v ∩ N(u) = ∅`.

Since `I_v ⊆ N(v)`, this implies

`|N(v) ∪ N(u)| ≥ |I_v| + deg(u) = a(v) + deg(u)`.

Consequently, for every selected incidence,

`M ≥ a(v) + deg(u)`.

Sum this inequality over all pairs `(v,u)` with `u ∈ I_v`. Define

`c(u) = |{v : u ∈ I_v}|`.

Then

`M S ≥ Σ_v a(v)^2 + Σ_u c(u) deg(u)`.

Because `u ∈ I_v` implies `v ∈ N(u)`, we have `c(u) ≤ deg(u)`, and therefore

`c(u) deg(u) ≥ c(u)^2`.

Also, double counting gives

`Σ_u c(u) = Σ_v a(v) = S`.

Applying Cauchy twice,

`Σ_v a(v)^2 ≥ S^2/n`,

`Σ_u c(u)^2 ≥ S^2/n`.

Thus

`M S ≥ 2 S^2/n`.

For a connected nontrivial graph, `S > 0`, so cancellation yields

`M ≥ 2S/n = 2 * averageIndepNeighbors(G)`.

## 2. Spanning-tree bound

Choose an edge `xy` attaining `M`. Form the double-star seed containing

- the edge `xy`,
- every edge from `x` to `N(x) \ {y}`, and
- every edge from `y` to `N(y) \ (N(x) ∪ {x})`.

Every added vertex is attached for the first time, so this seed is acyclic. Its leaves are exactly the vertices of `N(x) ∪ N(y)` other than the two centers, hence it has at least

`|N(x) ∪ N(y)| - 2 = M - 2`

leaves.

Extend the seed to a spanning tree while retaining all seed edges. Equivalently, use the tree identity

`leaves(T) ≥ deg_T(x) + deg_T(y) - 2`.

The constructed tree preserves enough degree at the two centers to give

`Ls(G) ≥ M - 2`.

Therefore

`2 * (averageIndepNeighbors(G) - 1) ≤ Ls(G)`.

## Lean decomposition

1. `average_bound_core`: completed algebraic Cauchy/incidence endgame.
2. `chosenLocalIndep`: canonical maximum independent set in each neighborhood, with exact-cardinality, containment, adjacency, and independence lemmas.
3. Weighted selected-incidence reversal and `reverseCount ≤ degree`: completed in the counting core.
4. Formalize `|I_v| + degree(u) ≤ |N(v) ∪ N(u)|` for each selected incidence and sum it.
5. Reuse the acyclic leaf-attachment and spanning-tree extension machinery developed for corrected WOWII 160.
6. Assemble the exact upstream theorem and audit its axioms.
