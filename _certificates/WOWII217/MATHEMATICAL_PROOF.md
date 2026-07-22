# WOWII Conjecture 217 — mathematical proof

## Status

The mathematics below proves the exact conjecture.  It does **not** claim that the
terminal Lean theorem has been kernel-verified yet.  The remaining work is to
formalize the cited ingredients and the finite degree-sequence reduction in the
pinned Formal Conjectures environment.

## Statement

For a finite connected simple graph `G`, define

```text
I(G) = 1 if residue(G) = 2, and I(G) = 0 otherwise.
```

If

```text
Ls(G) ≤ 4 I(G) + 2,
```

then `G` has a Hamiltonian path.

Here `Ls(G)` is the maximum number of leaves in a spanning tree and
`residue(G)` is the Havel–Hakimi residue.

## Standard ingredients

1. **Degree versus leaf number.**  For every vertex `v`, all edges incident with
   `v` form a forest and therefore extend to a spanning tree.  In a tree the
   number of leaves is at least the degree of every vertex.  Hence
   `degree_G(v) ≤ Ls(G)` and in particular `Delta(G) ≤ Ls(G)`.

2. **Graffiti.pc 190 (Mafuta–Mukwembi–Munyira).**  A connected graph satisfying
   `delta(G) ≥ (Ls(G) + 1) / 2` is traceable.

3. **Residue dominates Caro–Wei (Favaron–Mahéo–Saclé).**

   ```text
   residue(G) ≥ sum_{v in V(G)} 1 / (degree(v) + 1).
   ```

4. **Chvátal's path criterion.**  For an ascending degree sequence
   `d_1 ≤ ... ≤ d_n`, if for every `i < (n+1)/2`

   ```text
   d_i ≥ i  or  d_{n+1-i} ≥ n-i,
   ```

   then the graph is traceable.

5. **Bondy–Chvátal path closure.**  Repeatedly add a nonedge `uv` whenever
   `degree(u) + degree(v) ≥ n-1`.  The original graph is traceable if and only
   if its resulting path closure is traceable.

6. **Connected regular graphs (Cranston–O).**  Every connected `k`-regular graph
   on at most `2k+2` vertices is Hamiltonian.

## Proof

Let `r = residue(G)`.

### Case 1: `r ≠ 2`

The hypothesis gives `Ls(G) ≤ 2`, hence `Delta(G) ≤ 2`.  A finite connected
simple graph of maximum degree at most two is a path or a cycle, and therefore
is traceable.

### Case 2: `r = 2`

Now `Ls(G) ≤ 6`, so `Delta(G) ≤ 6`.

If `delta(G) ≥ 4`, then

```text
delta(G) ≥ 4 ≥ (Ls(G)+1)/2,
```

and Graffiti.pc 190 makes `G` traceable.  It remains to treat `delta(G) ≤ 3`.

By the residue–Caro–Wei inequality,

```text
2 = residue(G)
  ≥ sum_v 1/(degree(v)+1)
  ≥ |V(G)|/7.
```

Thus `n = |V(G)| ≤ 14`.

If the ascending degree sequence satisfies Chvátal's path criterion, the result
is immediate.  The deterministic enumeration in
`scripts/c217_enumerate_sequences.py` checks all positive graphical sequences
of length at most 14, maximum entry at most 6, minimum entry at most 3, residue
2, and failure of Chvátal's criterion.  It produces exactly the following 22
sequences (written in descending order):

```text
[1,1,1,1]
[2,2,2,1,1]
[3,3,3,3,1,1]
[2,2,2,2,2,2]
[3,3,2,2,2,2]
[4,4,4,4,4,1,1]
[3,3,3,3,2,2,2]
[5,5,5,5,5,5,1,1]
[4,4,4,4,4,2,2,2]
[4,4,4,3,3,3,3,2]
[3,3,3,3,3,3,3,3]
[4,4,3,3,3,3,3,3]
[5,4,4,3,3,3,3,3]
[6,6,6,6,6,6,6,1,1]
[5,5,5,5,5,5,2,2,2]
[4,4,4,4,4,3,3,3,3]
[6,6,6,6,6,6,6,2,2,2]
[5,5,5,5,5,5,3,3,3,3]
[5,5,5,5,4,4,4,4,3,3]
[5,5,5,4,4,4,4,4,4,3]
[6,5,5,5,4,4,4,4,4,3]
[6,6,6,6,6,6,6,3,3,3,3]
```

We now prove that every connected realization of every sequence on this list is
traceable.  No graph census is needed.

### Parametric closure lemma

Suppose a connected graph has degree sequence

```text
(h-1 repeated h times, q repeated q+1 times),
```

where `h ≥ q+2`.  Let `A` be the `h` high-degree vertices and `B` the `q+1`
low-degree vertices.  The order is `n=h+q+1`, so the path-closure threshold is
`h+q`.

Because `2(h-1) ≥ h+q`, the closure makes `A` a clique.  Let `A+` be the high
vertices having an original neighbor in `B`; connectedness gives `A+ ≠ ∅`.
A vertex of `A+` has closure degree at least `h`, so it becomes adjacent to all
of `B`.

If one of these new `A+`–`B` edges was not already present, its low endpoint now
has degree at least `q+1`.  Every high vertex outside `A+` has degree at least
`h-1`, hence joins that low vertex, reaches degree at least `h`, and then joins
all of `B`.  Thus `A` becomes complete to `B`.

Otherwise every edge in `A+ × B` was already present in the original graph.
Writing `s=|A+|`, each low vertex has degree `q`, so `s≤q`.  Every high vertex
outside `A+` has no low neighbor and degree `h-1`, hence was adjacent to every
other high vertex.  Consequently each vertex in `A+` had at least

```text
(h-s) + (q+1)
```

original neighbors.  Since its degree was `h-1`, this implies `s≥q+2`, a
contradiction.  Hence `A` is complete to `B` in all cases.

Every low vertex now has degree at least `h`; since `2h ≥ h+q`, the closure also
makes `B` a clique.  The path closure is complete, so the original graph is
traceable.

This lemma settles the following 12 sequences:

```text
[2^3,1^2], [3^4,1^2], [4^5,1^2], [5^6,1^2], [6^7,1^2],
[3^4,2^3], [4^5,2^3], [5^6,2^3], [6^7,2^3],
[4^5,3^4], [5^6,3^4], [6^7,3^4].
```

Here exponent notation denotes multiplicity.

### The impossible and regular sequences

* `[1^4]` has no connected realization.
* A connected realization of `[2^6]` is 2-regular on `2·2+2` vertices.
* A connected realization of `[3^8]` is 3-regular on `2·3+2` vertices.

The latter two are Hamiltonian by the connected-regular theorem.

### Seed-completion lemma

In a graph of order `2r+2`, suppose its path closure contains a universal set
`A`, every vertex outside `A` has degree at least `r`, and at least one outside
vertex has degree at least `r+1`.  The seed vertex joins every other outside
vertex because `(r+1)+r=2r+1=n-1`.  All outside degrees then become at least
`r+1`, so the outside set becomes a clique.  Hence the full closure is complete.

The following six sequences satisfy this lemma.  In each row, the displayed set
`A` first becomes universal by direct degree-sum closure.  If no outside vertex
were a seed, the stated number of original cross edges would be required, which
exceeds the sum of the original degrees in `A`.

| sequence | `A` | `r` | cross edges required without a seed | sum of degrees in `A` |
|---|---:|---:|---:|---:|
| `[3^2,2^4]` | the two 3-vertices | 2 | 8 | 6 |
| `[4^3,3^4,2]` | the three 4-vertices | 3 | 14 | 12 |
| `[4^2,3^6]` | the two 4-vertices | 3 | 12 | 8 |
| `[5,4^2,3^5]` | the 5-,4-,4-vertices | 3 | 15 | 13 |
| `[5^4,4^4,3^2]` | the four 5-vertices | 4 | 22 | 20 |
| `[6,5^3,4^5,3]` | the 6-,5-,5-,5-vertices | 4 | 23 | 21 |

Thus all six have complete path closure.

### The final irregular sequence

For `[5^3,4^6,3]`, let `A` be the three 5-vertices.  Closure first makes `A` a
clique and joins `A` to all six 4-vertices.  Each vertex of `A` then has degree
at least eight and therefore joins the 3-vertex, so `A` is universal.

If all six 4-vertices still had degree four, each would originally have been
adjacent to all three vertices of `A`, requiring 18 cross edges, more than the
total degree 15 available in `A`.  Hence some 4-vertex has closure degree at
least five.  It joins all other 4-vertices, reaches degree at least eight, and
then joins the 3-vertex.  The remaining outside edges are subsequently forced,
so the path closure is complete.

Every exceptional degree sequence is therefore traceable.  This completes the
proof of WOWII Conjecture 217.

## Formalization boundary

The existing Lean development already contains:

* the exact theorem statement;
* the `residue ≠ 2` branch;
* `degree(v) ≤ Ls(G)` for connected graphs;
* the maximum-degree-two traceability theorem;
* the graph-cone equivalence for Hamiltonian paths; and
* the one-edge and iterated Bondy–Chvátal path-closure machinery.

Still required for a no-`sorry` terminal theorem:

1. formalize or replace Graffiti.pc 190 for the `delta ≥ 4` branch;
2. formalize the residue–Caro–Wei order bound;
3. formalize Chvátal's path degree-sequence criterion and the 22-sequence
   certificate; and
4. formalize the parametric, seed, and connected-regular endgames above.
