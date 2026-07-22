# WOWII 217 — no-Graffiti fallback

## Purpose

This proof route removes Graffiti.pc 190 entirely. It keeps the already-used
residue order bound, Chvátal's degree-sequence criterion, Bondy--Chvátal path
closure, and the connected-regular boundary theorem.

Under `residue(G)=2` and `Ls(G)<=6`, the degree bound gives `Delta(G)<=6`, and
the reciprocal-degree residue bound gives `|V(G)|<=14`. Enumerating every
positive graphical sequence with these constraints that fails Chvátal's path
criterion gives exactly the 40 rows in `scripts/c217_certificate.json`.

The rows split as follows:

* 1 impossible connected sequence;
* 5 regular boundary sequences;
* 15 instances of the parametric two-block closure lemma;
* 6 low-degree seed-completion instances;
* 1 low-degree two-stage instance;
* 11 high-degree closure instances; and
* 1 high-degree leaf obstruction.

The first 23 proof obligations (the 22-row direct remainder plus the extra
parametric rows) are covered in `MATHEMATICAL_PROOF.md`. This note proves the
remaining high-degree part.

## Closure seed lemma

Let the graph have order `2r+2`, and let its path closure contain a universal
set `A`. Suppose every vertex of `B=V\A` has closure degree at least `r`, and
some vertex of `B` has closure degree at least `r+1`. The seed joins every
other vertex of `B`, since `(r+1)+r=2r+1=n-1`. Every other vertex then has
degree at least `r+1`, so `B` becomes a clique. Hence the closure is complete.

## Order 10: rows 23--27

The threshold is nine. Let `A` be the vertices of degree at least five and
`B` the degree-four vertices. Every pair in `A` has degree sum at least ten,
and every `A`--`B` pair has sum at least nine, so `A` is universal in the path
closure.

For rows 23--26, if no vertex in `B` gained an edge, every `A`--`B` edge was
already present in the original graph. The required number of cross edges and
the total degree available in `A` are:

| row | sequence | required `A`--`B` edges | degree sum on `A` |
|---:|---|---:|---:|
| 23 | `[5^2,4^8]` | 16 | 10 |
| 24 | `[6,5^2,4^7]` | 21 | 16 |
| 25 | `[5^4,4^6]` | 24 | 20 |
| 26 | `[6^2,5^2,4^6]` | 24 | 22 |

Each inequality is impossible. Thus a degree-four vertex gains an edge and
becomes a degree-five seed. The closure seed lemma with `r=4` completes the
graph.

For row 27, `[6^4,4^6]`, the same argument has equality: 24 required cross
edges and degree sum 24 on `A`. Therefore either a vertex of `B` gains an edge,
in which case the seed lemma completes the closure, or every available degree
of `A` is used on `B`, no edge lies inside `A`, and the graph is exactly
`K_{4,6}`.

The latter graph violates the WOWII leaf hypothesis. Choose one vertex `a` in
the part of size four and one vertex `b` in the part of size six. Take all six
edges from `a` to the large part and the three edges from `b` to the other
vertices of the small part. This is a spanning tree with eight leaves. Hence
`Ls(K_{4,6})>=8>6`.

## Order 11: row 30

The sequence is `[6^4,5^2,4^5]`, and the closure threshold is ten. Let `A` be
the four degree-six vertices. Since `6+4=10`, `A` becomes universal.

Let `C` be the two degree-five vertices and `D` the five degree-four vertices.
If a vertex of `C` gains an `A`-edge, it reaches degree six, joins all of `C∪D`,
and starts the completion cascade. If a vertex of `D` misses two or more
original `A`-neighbors, the added `A`-edges also raise it to degree six and
start the same cascade.

Assume neither happens. Both vertices of `C` were originally adjacent to all
four vertices of `A`; because `5+5=10`, their mutual closure edge must also have
been original or would itself create a degree-six seed. Thus `A` sends eight
original cross edges to `C`. Every vertex of `D` has at least three original
neighbors in `A`, so `A` sends at least fifteen edges to `D`. The total is at
least 23. The degree sum on `A` is 24, and subtracting twice the number of
internal `A`-edges shows the cross-edge count is even. It is therefore 24.

Consequently `A` has no internal edges; the `A`--`D` degrees are `4,3,3,3,3`.
The four deficient vertices of `D` each have exactly one original edge outside
`A`, while the full vertex has none. The two degree-five vertices use all
their degree on `A` and on each other, so those four outside edges form a
matching inside `D`. Closure supplies the missing `A`-edge at every deficient
vertex, making those vertices degree five. Now every pair of degree-five
vertices has sum ten, so `C∪D` becomes a clique. The closure is complete.

## Order 12: rows 32--35 and 37--38

The threshold is eleven. Let `A` be the degree-six vertices, `C` the
degree-five vertices, and `D` the degree-four vertices.

Every `A`--`A` and `A`--`C` pair is forced. In rows 32--35, after these edges
are present, each vertex of `A` has known degree at least eight, nine, ten, and
ten respectively, so `A` also joins every vertex of `D`. Thus `A` is universal.
In rows 37--38 there is no `D`, and the same first closure step already makes
`A` universal.

For rows 37--38, if no vertex of `C` gains an edge then all `A`--`C` edges were
original. They require 20 and 32 incidences, while the degree sums on `A` are
12 and 24. This is impossible. Some degree-five vertex therefore reaches six,
joins every other degree-five vertex, and completes the closure.

For rows 32--35, count missing original edges between universal `A` and
`C∪D`. Since the degree sum on `A` is `6|A|`, at least

```text
|A|(|C|+|D|) - 6|A| = |A|(6-|A|)
```

such edges are added by closure. The lower bounds are respectively 5, 8, 9,
and 5. If a vertex of `C` misses an `A`-edge, its degree rises from five to
six. It then joins all of `C`; the resulting `C` clique has enough degree to
join `D`, and the closure completes. If a vertex of `D` misses at least two
`A`-edges, it rises from four to six, joins `C`, creates a degree-six vertex in
`C`, and triggers the same cascade.

If neither event occurs, no edge is missing at `C` and at most one is missing
at each vertex of `D`. The total number missing is then at most `|D|`, namely
3, 2, 1, and 1 in rows 32--35. This contradicts the lower bounds 5, 8, 9, and
5. Hence every one of these closures is complete.

## Remaining high rows

Rows 29, 31, and 39 are further instances of the parametric two-block lemma:

```text
[5^6,4^5], [6^7,4^5], [6^7,5^6].
```

Rows 22, 36, and 40 are the regular boundary sequences

```text
[4^10], [5^12], [6^14].
```

They are Hamiltonian by the connected `k`-regular theorem for order at most
`2k+2`.

Thus every one of the 40 no-Graffiti certificate rows is traceable or violates
`Ls(G)<=6`. Together with Chvátal's criterion, this proves the exceptional
residue-two branch without invoking Graffiti.pc 190.
