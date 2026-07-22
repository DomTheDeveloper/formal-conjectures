# N = 6, D = 3 monochromatic quantum graph obstruction

This document records the exact reduction from the integer equation system to
four finite characteristic-two certificate instances.

## 1. Reduction from integers to characteristic two

The perfect-matching equations are polynomial identities using only addition,
multiplication, zero, and one. Therefore every ring homomorphism preserves the
equation system. In particular, a hypothetical integer solution maps through
`ℤ → 𝔽₂` to a characteristic-two solution.

The Lean file `ProofAudit/6_bridge.lean` formalizes this as:

- `pmSumN_map`;
- `EqSystemN.map`;
- `no_eqSystem6_d3_int_of_no_f2`.

Thus it is enough to prove that no `𝔽₂` solution exists for `N=6`, `D=3`.

## 2. Choosing active monochromatic matchings

For a constant coloring in any fixed color, the equation says that the parity
of the 15 perfect-matching monomials is one. Hence at least one monomial is one.
Over `𝔽₂`, a product is one only when all three of its edge weights are one.
Call such a perfect matching active.

Choose one active matching for each color. Vertex permutations and color
permutations preserve the equation system.

There are 15 perfect matchings of `K₆`, and `S₆` acts transitively on them, so
the active color-0 matching may be fixed as

`M0 = (01)(23)(45)`.

## 3. The three color-1 orbit types

The stabilizer of `M0` has exactly three orbits on perfect matchings:

1. `same`: `(01)(23)(45)`;
2. `four_plus_two`: `(02)(13)(45)`;
3. `six_cycle`: `(02)(14)(35)`.

The deterministic script `ProofAudit/quantum_symmetry_audit.py` enumerates all
15 matchings and all 720 vertex permutations and verifies this orbit statement.

The exact CNF instances for `same` and `four_plus_two` are UNSAT. CaDiCaL
produced DRAT certificates, and DRAT-trim independently reported `VERIFIED` for
both complete orbit families.

Therefore only `six_cycle` remains.

## 4. Color 2 inside the six-cycle case

Fix

`M1 = (02)(14)(35)`.

Under the ordered stabilizer of `(M0,M1)`, the active color-2 matching has seven
orbits. In canonical order they are classified as:

0. same as color 0;
1. shares an edge with a previous matching;
2. shares an edge with a previous matching;
3. same as color 1;
4. shares an edge with a previous matching;
5. three pairwise edge-disjoint matchings whose union is the triangular prism;
6. three pairwise edge-disjoint matchings whose union is `K₃,₃`.

Cases 0 and 3 reduce by a color permutation to the already-certified `same`
family. Cases 1, 2, and 4 reduce by choosing the appropriate previous color as
color 0 to the already-certified `four_plus_two` family. Case 5 has its own
independently verified DRAT certificate.

Thus only case 6 remains. A representative is

`M2 = (05)(13)(24)`.

## 5. The final residual cyclic symmetry

The ordered stabilizer of `(M0,M1,M2)` induces the cyclic group `C₃` on the
three residual color-0 diagonal bits

- `w_(02)^(00)`;
- `w_(35)^(00)`;
- `w_(14)^(00)`.

The eight Boolean assignments to these three bits have exactly four `C₃`
orbits, represented by

- `000`;
- `111`;
- `100`;
- `110`.

The symmetry-audit script checks the stabilizer action and these four orbits
by exhaustive enumeration.

Consequently, UNSAT certificates for these four instances exhaust every
possible characteristic-two solution.

## 6. Independent certificate routes

Two exact routes target the same four instances:

1. **CNF + DRAT** — the XOR equations are Tseitin-expanded, CaDiCaL emits a
   DRAT proof, and DRAT-trim checks it.
2. **Native XOR + FRAT-XOR/XLRUP** — the cubic monomials are Tseitin-encoded,
   but each 15-term parity equation remains a native XOR clause.
   CryptoMiniSat emits FRAT-XOR, `frat-xor` elaborates it to XLRUP, and the
   formally verified `cake_xlrup` checker must report `s VERIFIED`.

A SAT result in any branch would refute the obstruction and is treated as a
hard failure. Only independently checked UNSAT certificates authorize the final
nonexistence claim.

## 7. Consequence for all D ≥ 3

The already kernel-audited color-restriction theorem maps any `D`-color
solution with `D ≥ 3` to a 3-color solution by restricting to an injective copy
of the first three colors. Therefore nonexistence at `D=3` implies
nonexistence for every `D≥3`.

Combining the four final certificates, the integer-to-`𝔽₂` Lean bridge, and the
verified color-restriction theorem proves the full `N=6`, all-`D≥3` integer
obstruction.
