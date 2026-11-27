# Prime divisors of quadratic products

The real-part sequence OEIS A363415 has a missing prime in its conjectured list. The prime 139 divides no term. The corrected list through 197 is

    5, 11, 13, 31, 53, 79, 97, 113, 137, 139, 157, 179, 193, 197.

The same proof project verifies two other conjectured prefixes and answers the prime-divisor question in four companion entries.

## Reproduce the results

With Lean's Elan toolchain manager installed, extract the archive and run these commands from the directory containing this file. The manifest pins all Lake dependencies.

```sh
lake exe cache get Mathlib.NumberTheory.Zsqrtd.Basic Mathlib.NumberTheory.Padics.PadicVal.Basic Mathlib.Tactic.LinearCombination Mathlib.Tactic.Linarith Mathlib.Tactic.Ring Mathlib.Algebra.Field.ZMod
lake --wfail build
python3 check.py
```

Lean 4.33.1 checks the proofs. The `#print axioms` commands at the end of each source file report the dependencies of the main results. Finite computations use `decide +kernel`. The independent Python 3 script reproduces the two modular certificates and all three prime lists using only the standard library.

## Statements and sources

Set ω² = −d. Define A(d,n) and B(d,n) by expanding the product of (1 + kω) over 1 ≤ k ≤ n as A(d,n) + B(d,n)ω. At n = 0 the product is 1. For d > 0 the OEIS imaginary-coordinate entries use the imaginary part divided by √d, which equals B(d,n).

| Published assertion | Verified result |
| --- | --- |
| [A363409](https://oeis.org/A363409), real coordinate at d = 2 | Its proposed list of primes dividing no term is exact through 101. |
| [A363413](https://oeis.org/A363413), real coordinate at d = 4 | Its proposed list is exact through 79. |
| [A363415](https://oeis.org/A363415), real coordinate at d = 5 | The corrected list above includes precisely the primes through 197 that divide no term. |
| [A363410](https://oeis.org/A363410), [A363412](https://oeis.org/A363412), [A363414](https://oeis.org/A363414), [A363416](https://oeis.org/A363416) | For d = 2, 3, 4, 5 respectively, every positive m divides the nonzero term B(d,2m). The theorem holds for every integer d ≥ 2. |

### The general divisor theorem

Let T(n) = n(n+1)/2. The theorem `triangular_factor` gives an integer k with B(d,n) = T(n)(1 + dk). For d ≥ 2 and n > 0 the quotient is nonzero. At n = 2m, T(2m) = m(2m+1). For each prime p dividing d, the p-adic valuation of B(d,n) equals that of T(n) for n > 0.

An elementary proof compares the polynomial ∏(1 + kX) to its reflection at −X, once modulo n and once modulo n+1. The Lean implementation pairs interval endpoints to obtain the same divisibility. The required integrality of the odd elementary symmetric sums also follows from the classical Hultman-number formula of Miklós Bóna and Ryan Flynn, section 3. [Paper](https://arxiv.org/abs/0811.0740)

### How 139 was found and certified

The search scans the primes up to 197 and uses the recurrence (a,b) ↦ (a − dkb, b + ka) modulo each prime. After 2p steps, B(d,2p) = 0 modulo p. The 2p-step product therefore acts by multiplication by its real coordinate. If any real residue through 2p vanishes, p divides that term. If every residue is nonzero, the scalar is nonzero, so each subsequent block also consists of nonzero residues. The proved equivalence is `finite_test`. Applying it to each prime yields the three exact prefixes.

For p = 139 the shorter block of 139 suffices. After 138 steps the residues (a,b) are (2,0), and the product of the real residues at indices 0 through 138 is 20 modulo 139. The next factor is 1 modulo 139. Hence A(5,139q+r) = 2^q A(5,r) modulo 139 for 0 ≤ r < 139. This proves nondivisibility at all indices.

## Files

| File | Contents |
| --- | --- |
| QuadraticDivisors.lean | Quadratic-integer model, evaluation as a finite product, triangular factor, explicit nonzero multiple and valuation formula |
| RealPrimeLists.lean | Reduction to a finite test, certificate for 139, three exact prime lists |
| check.py | Modular certificates, prime enumeration and sample exact-integer checks |
| verification.txt | Toolchain, dependency revision and axiom output from the proof check |

The OEIS sources identify the conjectural assertions being addressed. Independent priority for the correction to A363415 has not been established.
