# Bala's row congruences and powers of two in lattice spheres

| Result | Scope | Proof |
|---|---|---|
| OEIS A363418 and A363419 | Cubic congruence in every positive row, a stronger exponent when the prime divides the row number, and every negative row of A363419. The final section identifies the Schröder generating function of A363418. | [Cubic rows](CubicRows.md) |
| OEIS A362724, A362725 and A362731 | Quadratic congruences at every iteration of two Apéry transforms for odd primes, and every iteration of the Franel transform for all primes. | [Iterated Apéry and Franel sequences](IteratedAperyFranel.md) |
| OEIS A035607 and A363418 | Exact 2-adic valuation at every positive dimension and distance, with exact valuations of successive even-index differences in A363418. | [Binary lattice spheres](BinaryLatticeSpheres.md) |
| OEIS A362727 and A362729 | The prime-index case for all primes at least five. The general prime-power conjectures remain open in this work. | [Prime indices](PrimeIndex.md) |

The arguments in the linked notes are full written proofs. The separate Lean files check the following parts.

| Lean source | Kernel-checked statements |
|---|---|
| [FramingLemmas.lean](FramingLemmas.lean) | Vanishing of the inverse-square sum modulo every positive power of every prime at least five, the integral row normalization identity for arbitrary integer power series and natural row numbers, and evenness of every positive Franel number. |
| [LatticeSphere.lean](LatticeSphere.lean) | Dimension–distance reciprocity from the finite binomial formula, exact sphere valuations in all odd dimensions or at all odd distances, and the valuation of a complete sum of odd squares. |
| [LatticeSphereRecurrence.lean](LatticeSphereRecurrence.lean) | The recurrence gives the count modulo four in every positive-radius sphere and gives explicit counts in dimensions two, three and four. This file only imports Lean core. |

The all-even general lattice case and the complete prime-power congruence arguments are in the written proofs. The named OEIS conjectures and earlier framing results are credited in their respective notes.

## Reproduction

Use Lean 4.33.1 with the Formal Conjectures mathlib pin `0df444a360eaa60ab8c11dca51a86af692955474`. In a checkout with the mathlib cache available, run the following from the repository root.

```sh
lake env lean research/bala-framing/FramingLemmas.lean
lake env lean research/bala-framing/LatticeSphere.lean
lake env lean research/bala-framing/LatticeSphereRecurrence.lean
python3 research/bala-framing/verify.py
```

The exact checker tests 3,822 cubic congruences, 1,176 iterated quadratic congruences, 16,384 lattice sphere valuations, 2,048 row-difference valuations, 120 Schröder generating-function coefficients, and the two odd-power transforms at every prime from 5 through 151. It also checks the OEIS prefixes and examples where the proposed exponents are attained.

[Google DeepMind Formal Conjectures issue 8390](https://github.com/google-deepmind/formal-conjectures/issues/8390)
