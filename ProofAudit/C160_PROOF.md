# WOWII Conjecture 160 — proof

Let

- \(\lambda(v)=\alpha(G[N(v)])\),
- \(\tau(v)\) be the number of triangles containing \(v\),
- \(L=\max_v\lambda(v)\), and
- \(T=\max_v\tau(v)\).

Assume throughout that `G` is finite, simple, connected, nontrivial, and has no cycle of length four. We prove that `G` has a spanning tree with at least `L + T` leaves.

## 1. Local structure

For every vertex `v`, the graph induced by `N(v)` has maximum degree at most one. Indeed, if `u ∈ N(v)` had two distinct neighbors `p,q ∈ N(v)`, then

`p - u - q - v - p`

would be a four-cycle. Hence `G[N(v)]` is a disjoint union of edges and isolated vertices.

Every edge of `G[N(v)]` is exactly the edge opposite `v` in one triangle through `v`. Consequently `G[N(v)]` has exactly `τ(v)` edges. A matching with `m` edges and `r` isolated vertices has independence number `m+r`, so

`λ(v) + τ(v) = deg(v)`.                                                    (1)

In particular, `λ(v) ≥ τ(v)`.

Also, any two distinct vertices have at most one common neighbor: two distinct common neighbors would themselves give a four-cycle.

## 2. Tree leaf inequality and extension

For every finite nontrivial tree `R` and distinct vertices `a,b`,

`leaves(R) ≥ deg_R(a) + deg_R(b) - 2`.                                    (2)

This follows from the standard identity

`leaves(R) = 2 + Σ_{deg_R(z)≥2} (deg_R(z)-2)`.

We also use the standard forest-extension fact: every acyclic edge-subgraph of a connected graph extends to a spanning tree while retaining all of its edges. Therefore it is enough to construct an acyclic seed with the required leaf or center-degree bound.

A geodesic together with any collection of edges attaching previously unused vertices as leaves is acyclic. We use this repeatedly below.

## 3. The case `T = 0`

Choose `x` with `λ(x)=L`. By (1), `deg(x)=λ(x)=L`. The full star at `x` is acyclic and extends to a spanning tree preserving degree `L` at `x`. Every tree has at least its maximum vertex degree many leaves, so the resulting spanning tree has at least `L=L+T` leaves.

## 4. The case `T = 1`

This is the classical triangle-improvement bound `Ls(G) ≥ L+1`; here is a direct construction.

Choose `x` with `λ(x)=L`, and choose an independent set `S⊆N(x)` of cardinality `L`. Choose a triangle `{a,b,c}` and choose `a` in that triangle minimizing the distance from `x` to the triangle. Let `P` be a geodesic from `x` to `a`.

Start with the edges of `P`. Attach every vertex of `S` not already used by `P` or by `{b,c}` as a leaf at `x`. Finally attach `b` and `c` as leaves at `a`.

The seed is acyclic: a geodesic is a path, the selected members of `S` are fresh leaves, and minimality of `a` ensures that `b,c` do not occur earlier on `P`; duplicates with the `x`-leaves were explicitly omitted.

At most one member of `S` is lost before adding `b,c`:

- a geodesic contains at most one neighbor of its initial vertex, namely its first successor;
- if `dist(x,a)>1`, no triangle vertex is in `N(x)` by minimality;
- if `dist(x,a)≤1`, the three triangle vertices form a clique, so the independent set `S` meets them in at most one vertex.

Thus the seed has at least `(L-1)+2=L+1=L+T` leaves. Extend it to a spanning tree.

## 5. The case `T ≥ 2`

Choose `x` with `λ(x)=L` and `y` with `τ(y)=T`.

### 5.1. Coincident maximizers

If `x=y`, then by (1)

`deg(x)=λ(x)+τ(x)=L+T`.

The full star at `x` extends to a spanning tree with at least `L+T` leaves.

### 5.2. Distinct maximizers

Assume `x≠y`, and let `P` be a geodesic from `x` to `y`. Take the edge set of `P`, attach every unused neighbor of `x` as an `x`-leaf, and then attach every unused neighbor of `y` that has not already been attached as an `x`-leaf.

The resulting seed is acyclic: each added edge introduces a fresh leaf. Extend it to a spanning tree `R`.

If `dist(x,y)≥2`, both endpoint degrees are fully preserved. For distance greater than two there is no common neighbor. For distance two, the middle path vertex is a common neighbor already represented by both path edges, and a second common neighbor would create a four-cycle. Hence

`deg_R(x)≥deg_G(x)` and `deg_R(y)≥deg_G(y)`.

Using (1), (2), and `λ(y)≥τ(y)=T≥2`,

`leaves(R)`
`≥ deg_G(x)+deg_G(y)-2`
`= (L+τ(x))+(λ(y)+T)-2`
`≥ L+T`.

It remains to consider `dist(x,y)=1`. The construction preserves every edge at `x`. At `y`, it omits only edges to common neighbors of `x` and `y`; there is at most one such neighbor. Therefore

`deg_R(x)≥deg_G(x)`,
`deg_R(y)≥deg_G(y)-1`.

If there is no common neighbor, (2) and `λ(y)≥2` immediately give `leaves(R)≥L+T`.

If there is one common neighbor, then `x` lies in a triangle, so `τ(x)≥1`. By (1),

`deg_G(x)=L+τ(x)≥L+1`,
`deg_G(y)=λ(y)+T≥T+2`.

Consequently

`leaves(R)`
`≥ deg_R(x)+deg_R(y)-2`
`≥ deg_G(x)+deg_G(y)-3`
`≥ (L+1)+(T+2)-3`
`= L+T`.

This completes every case and proves the corrected C4-free form of WOWII Conjecture 160.
