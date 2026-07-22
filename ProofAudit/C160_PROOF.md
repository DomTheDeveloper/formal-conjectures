# WOWII Conjecture 160 — proof

Let

- `λ(v) = α(G[N(v)])`,
- `τ(v)` be the number of triangles containing `v`,
- `L = max_v λ(v)`, and
- `T = max_v τ(v)`.

Assume throughout that `G` is finite, simple, connected, nontrivial, and has no cycle of length four. We prove that `G` has a spanning tree with at least `L + T` leaves.

## 1. Triangle petals in a C4-free graph

For a triangle `C` containing a vertex `v`, call the two-element set `C \ {v}` its **petal at `v`**. Two distinct triangles through `v` have disjoint petals. Otherwise they share `v` and another vertex `z`; writing their two remaining vertices as `a` and `b`,

`a - v - b - z - a`

is a four-cycle.

Consequently, if `Q(v)` is the union of all petals of triangles through `v`, then

`|Q(v)| = 2 τ(v)`.                                                        (1)

Every petal is an edge. Therefore, for every independent set `S ⊆ N(v)`, at most one endpoint of each petal lies in `S`. Since the petals are disjoint,

`|S ∩ Q(v)| ≤ τ(v)`.                                                      (2)

We shall also use that two distinct vertices have at most one common neighbor: two distinct common neighbors immediately form a four-cycle.

## 2. Tree facts

For every finite nontrivial tree `R` and distinct vertices `a,b`,

`leaves(R) ≥ deg_R(a) + deg_R(b) - 2`.                                    (3)

This is the standard identity

`leaves(R) = 2 + Σ_{deg_R(z)≥2} (deg_R(z)-2)`.

Every acyclic edge-subgraph of a connected graph extends to a spanning tree while retaining all its edges. Thus we construct acyclic seeds and track center degrees, which cannot decrease under extension. A geodesic together with edges attaching previously unused vertices as leaves is acyclic.

## 3. The case `T = 0`

Choose `x` with `λ(x)=L` and an independent set `S⊆N(x)` of cardinality `L`. The star with center `x` and leaf set `S` is acyclic. Extend it to a spanning tree. The degree of `x` remains at least `L`, so the spanning tree has at least `L=L+T` leaves.

## 4. The case `T = 1`

Choose `x` with `λ(x)=L`, and choose an independent set `S⊆N(x)` of cardinality `L`. Choose a triangle `{a,b,c}` and choose `a` in that triangle minimizing the distance from `x` to the triangle. If `x` lies in the chosen triangle, take `a=x`. Let `P` be a geodesic from `x` to `a`.

### 4.1. The case `a=x`

Take the star at `x` on `S∪{b,c}`. Since `b` and `c` are adjacent and `S` is independent, `S` contains at most one of them. Hence the star has degree at least `L+1` at `x`. Extend it to a spanning tree, which therefore has at least `L+1=L+T` leaves.

### 4.2. The case `a≠x`

Start with the edges of `P`. Attach every member of `S` not already used by `P` or by `{b,c}` as a fresh leaf at `x`. Finally attach `b` and `c` as fresh leaves at `a`.

The seed is acyclic. Minimality of `a` ensures that `b,c` do not occur earlier on `P`. At most one member of `S` is omitted:

- a geodesic contains at most one neighbor of its initial vertex, namely its first successor;
- if `dist(x,a)>1`, no vertex of the chosen triangle is in `N(x)`;
- if `dist(x,a)=1`, the path successor is `a`, and the independent set `S` meets the triangle in at most one vertex.

Let `s≥L-1` be the number of retained members of `S`. Extend the seed to a spanning tree `R`. The retained edges give

`deg_R(x) ≥ s+1`,
`deg_R(a) ≥ 3`.

Since `x≠a`, (3) yields

`leaves(R) ≥ (s+1)+3-2 = s+2 ≥ L+1 = L+T`.

## 5. The case `T ≥ 2`

Choose `x` with `λ(x)=L`, an independent set `S⊆N(x)` with `|S|=L`, and choose `y` with `τ(y)=T`. Put `Q=Q(y)`, so `|Q|=2T` by (1).

### 5.1. Coincident maximizers

Suppose `x=y`. By (2), `|S∩Q|≤T`, and hence

`|S∪Q| = |S|+|Q|-|S∩Q| ≥ L+2T-T = L+T`.

Every vertex of `S∪Q` is adjacent to `x`. The corresponding star extends to a spanning tree preserving degree at least `L+T` at `x`, so it has at least `L+T` leaves.

### 5.2. Distinct maximizers: general construction

Assume `x≠y`, and let `P` be a geodesic from `x` to `y`.

Begin with the edges of `P`. Attach as leaves at `x` all vertices of `S` not already on `P`. Then attach as leaves at `y` all vertices of `Q` that are neither on `P` nor already attached at `x`. Every added vertex is fresh, so the seed is acyclic. Extend it to a spanning tree `R`.

A geodesic contains at most one member of `N(x)` and at most one member of `N(y)`. Thus at most one member of `S` is lost to `P`, giving

`deg_R(x) ≥ L`.                                                           (4)

Moreover, `Q⊆N(y)`. At most one member of `Q` lies on `P`, and at most one further member can have been attached at `x`, because such a vertex would be a common neighbor of `x` and `y`. Therefore

`deg_R(y) ≥ 1+(2T-2)=2T-1`.                                               (5)

If `T≥3`, equations (3)–(5) give

`leaves(R) ≥ L+(2T-1)-2 = L+2T-3 ≥ L+T`.

It remains only to sharpen the construction when `T=2`.

### 5.3. The case `T=2` and `dist(x,y)≥2`

If `dist(x,y)>2`, `x` and `y` have no common neighbor. If `dist(x,y)=2`, their unique possible common neighbor is the middle vertex of `P`; a second common neighbor would create a four-cycle. In either case the two possible exclusions counted in (5) cannot be distinct. Hence at most one member of `Q` is omitted, so

`deg_R(y) ≥ 1+(4-1)=4`.

Together with (4) and (3),

`leaves(R) ≥ L+4-2 = L+2 = L+T`.

### 5.4. The case `T=2` and `x` adjacent to `y`

Use the adjacent double-star seed: retain the central edge `xy`, every chosen edge from `x` to `S`, and every edge from `y` to a vertex of `Q` that is not already joined to `x` in the seed. It is acyclic, because every noncentral vertex is attached to only one center. Extend it to a spanning tree `R`.

If `x∉Q`, at most one member of `Q` is a common neighbor of `x,y`. Therefore `y` retains the central edge and at least three of the four `Q`-edges, so

`deg_R(y)≥4`, while `deg_R(x)≥L`.

If `x∈Q`, then one petal at `y` is `{x,z}` for a common neighbor `z`. The central edge accounts for `x`; only `z` can be lost at the `y` side. If `y∈S`, independence forces `z∉S`, so `x` has degree at least `L` and `y` has degree at least `4`. If `y∉S`, then `x` has the central edge in addition to all `L` chosen `S`-edges, so `deg_R(x)≥L+1`, while `deg_R(y)≥3`. In every subcase,

`deg_R(x)+deg_R(y)≥L+4`.

Equation (3) now gives

`leaves(R) ≥ L+4-2 = L+2 = L+T`.

This completes every case and proves the corrected C4-free form of WOWII Conjecture 160.
