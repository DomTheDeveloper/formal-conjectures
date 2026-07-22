# Connected cubic graphs on eight vertices are traceable

This note removes the only nontrivial regular-graph citation needed by the
22-row direct proof of WOWII Conjecture 217.

Let `G` be a connected 3-regular graph on eight vertices, and choose a longest
path

```text
P = v₁ v₂ ... v_m.
```

Every neighbor of either endpoint lies on `P`. Define subsets of
`{1, ..., m-1}` by

```text
A = { i : v₁ is adjacent to v_{i+1} },
B = { i : v_i is adjacent to v_m }.
```

Both sets have cardinality three. If `A ∩ B` contains `i`, then

```text
v₁ v₂ ... v_i v_m v_{m-1} ... v_{i+1} v₁
```

is a cycle through every vertex of `P`. If a longest path does not already
contain all graph vertices, connectedness supplies a path from outside this
cycle to it; breaking the cycle at the first attachment extends `P`, a
contradiction.

Therefore, if `P` is not Hamiltonian, `A` and `B` are disjoint. This is
impossible when `m-1 < 6`, so `m >= 7`. The only remaining case is `m=7`; let
`w` be the unique vertex outside `P`.

The endpoint path edges imply `1 ∈ A` and `6 ∈ B`. If `w` is adjacent to some
`v_j` with `j ∈ A`, then

```text
w v_j v_{j-1} ... v₁ v_{j+1} v_{j+2} ... v₇
```

is a Hamiltonian path. Hence, in a counterexample, all three neighbors of `w`
are indexed by `B`. Since `|B|=3`, they are exactly `{v_j : j ∈ B}`.

Now `B` consists of `6` and two elements of `{2,3,4,5}`. There are six cases.
Five contain the following explicit Hamiltonian paths:

| `B` | Hamiltonian path |
|---|---|
| `{2,3,6}` | `v₁ v₂ v₇ v₃ v₄ v₅ v₆ w` |
| `{2,5,6}` | `v₁ v₂ v₃ v₄ v₅ v₇ v₆ w` |
| `{3,4,6}` | `v₁ v₂ v₃ v₇ v₄ v₅ v₆ w` |
| `{3,5,6}` | `v₁ v₂ v₃ v₄ v₅ v₇ v₆ w` |
| `{4,5,6}` | `v₁ v₂ v₃ v₄ v₅ v₇ v₆ w` |

In the remaining case `B={2,4,6}`, its complement is `A={1,3,5}`. The vertex
`v₄` is then adjacent to

```text
v₃, v₅, v₁, v₇, w,
```

where the first two edges lie on `P`, `v₁v₄` comes from `3∈A`, and
`v₄v₇`, `wv₄` come from `4∈B`. Thus `degree(v₄) >= 5`, contradicting cubicity.

Every connected cubic graph on eight vertices therefore has a Hamiltonian
path (in fact the five isomorphism classes are Hamiltonian).
