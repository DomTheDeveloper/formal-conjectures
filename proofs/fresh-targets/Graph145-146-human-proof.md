# Human proofs for WOWII Graph Conjectures 145 and 146

Let `T(G)` be the maximum order of an induced tree, `D = diam(G)`, let `B` be the set of peripheral vertices, and put `E = eccSet(G,B)`.

Two elementary bounds will be used repeatedly.

1. A diametral geodesic is an induced path, so `T(G) >= D + 1`.
2. `E <= D - 1`: a vertex in `B` has distance zero from `B`, while a vertex outside `B` has eccentricity at most `D - 1`.

## Diameter-four lemma

If `D = 4` and `E = 3`, then `T(G) >= 6`.

Choose `x` at distance three from `B`, and choose peripheral vertices `a,b` with `d(a,b)=4`. Since `x` is not peripheral, `ecc(x) <= 3`; hence `d(x,a)=d(x,b)=3`.

Choose geodesics

`x-u-v-a` and `x-s-t-b`.

If `u=s`, the six vertices `x,u,v,a,t,b` induce a tree: every additional edge would shorten one of the three prescribed distances `d(x,a)=3`, `d(x,b)=3`, or `d(a,b)=4`.

Assume `u != s`. Among the seven vertices on the two geodesics, BFS-layer constraints and `d(a,b)=4` show that the only possible cross-edges are `us`, `ut`, and `vs`.

- If `ut` is present, delete `s`; the remaining six vertices induce a tree.
- Else, if `vs` is present, delete `u`; the remaining six vertices induce a tree.
- Else, if `us` is present, delete `x`; the remaining six vertices form the induced path `a-v-u-s-t-b`.
- Else, the union of both geodesics is already a seven-vertex tree; deleting either leaf gives an induced six-vertex tree.

Thus `T(G) >= 6`.

## Conjecture 146

Let `R = rad(G^2)`, assumed positive.

If `R >= 2`, then

`T(G) R >= 2(D+1) > 2(D-1) >= 2E`.

If `R=1`, some vertex is at distance at most two from every vertex of `G`, so `rad(G) <= 2` and `D <= 4`.

- If `E <= 2`, then `2E <= 4 <= T(G)` (the small-diameter cases are immediate from a geodesic).
- If `E=3`, then necessarily `D=4`, and the diameter-four lemma gives `T(G) >= 6 = 2E`.

Therefore `2E <= T(G)R`.

## Conjecture 145

Let `L` be the minimum, over vertices, of the local independence number in the complement, assumed positive.

If `L >= 2`, the same calculation gives

`T(G)L >= 2(D+1) > 2(D-1) >= 2E`.

Suppose `L=1`, and choose a vertex `c` attaining the minimum. The neighbors of `c` in the complement are precisely the non-neighbors of `c` in `G`. Independence number one in the complement says that these non-neighbors form an independent set in `G`.

Every non-neighbor `y` of `c` is therefore at distance exactly two from `c`: if a shortest `y-c` path had length at least three, its first two vertices would both be non-neighbors of `c` but adjacent in `G`, a contradiction. Hence `ecc_G(c) <= 2`, so `D <= 4`.

As above, `E <= 2` gives `T(G) >= 2E`, while `E=3` forces `D=4` and the diameter-four lemma gives `T(G) >= 6=2E`. Since `L=1`, this is exactly `2E <= T(G)L`.
