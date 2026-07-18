# Counterexample to WOWII Graph Conjecture 103

Let `G` have vertices `u,v,c`, with `u,v,c` spanning a triangle. Attach four private leaves to `u` and four private leaves to `v`. Thus `G` has eleven vertices.

- The eight leaves together with `c` form an independent set, so `alpha(G) >= 9`. Every independent set uses at most one of the triangle vertices, and choosing `u` or `v` excludes its four leaves; hence `alpha(G)=9`.
- Deleting `c` leaves a tree on ten vertices, so `b(G) >= 10`. The full graph contains a triangle, so `b(G) <= 10`. Therefore `b(G)=10`.
- Each of the eight leaves has eccentricity `3`; each of `u,v,c` has eccentricity `2`. Hence the average eccentricity is `(8*3+3*2)/11 = 30/11`.

Since `e < 30/11`, we have `log(30/11)>1`, and therefore

`floor(10-log(30/11)) <= 8 < 9 = alpha(G)`.

Thus Conjecture 103 is false.
