# The 2-adic limit for OEIS A363412

The Lean theorem `A363412Two.product_two_adic_slope` proves Peter Bala's conjecture for the coefficient of the square root of −3 in the quadratic product. It states that twice the exponent of 2 dividing the coefficient, divided by the index, tends to 1 in the rationals. The proof also determines the exact exponent at every positive index.

| Module | Result |
|---|---|
| [A363412Dyadic.lean](./A363412Dyadic.lean) | Checks the eight-factor polynomial identity and proves the valuation increases by one at each block doubling. |
| [A363412TwoAdic.lean](./A363412TwoAdic.lean) | Proves the exact formula in all residue classes modulo eight. |
| [A363412Growth.lean](./A363412Growth.lean) | Deduces convergence from the exact formulas. |
| [A363412Limit.lean](./A363412Limit.lean) | States and proves the limit directly for the finite product. |

With Lean installed through elan, run the following from this directory.

```sh
lake update
lake exe cache get
lake build
lake env lean A363412Limit.lean
```

The last command prints the axiom dependencies of the product theorem. The project pins Lean 4.19.0 and the corresponding mathlib release commit.

See [the written proof and independent million-index recurrence check](../A363412TwoAdic.md), [the extension to every parameter congruent to 3 modulo 8](../QuadraticTwoAdicFamily.md), and [the original OEIS entry](https://oeis.org/A363412). The [earlier trureturing work](https://www.trureturing.org/research/bala3634-valuations/) proved separate 3-adic assertions for this sequence. KitaKen1 previously handled the [related Gaussian-integer product](https://github.com/KitaKen1/oeis-a105751-two-adic/tree/a9692d90078c4dff1478acaaa70be2fba06a3ef9).

Codex developed this proof at Dominic Dabish's request.
