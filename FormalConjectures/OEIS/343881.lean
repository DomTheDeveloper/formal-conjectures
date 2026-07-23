/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjecturesUtil

/-!
# OEIS A343881 / Peter Kagey's Problem 16

For integers `n` and `k`, let `T(n, k)` be the least integer `m > k` for which
there are positive integers `c`, `x`, and `y`, with `x, y < n`, such that

`k ^ x * m ^ y = c ^ n`.

The OEIS entry conjectures that, for each fixed `k > 1`, one eventually has
`T(p, k) = k * rad(k)` as `p` ranges over sufficiently large primes.

The conjecture is false for `k = 12`. Its proposed value is `72`, but the
2-adic and 3-adic exponent equations force an allowed exponent to vanish
modulo `p`, contradicting its required range. Equivalently, the exponent
vectors `(2, 1)` and `(3, 2)` have determinant one.

*Reference:* [OEIS A343881](https://oeis.org/A343881)
-/

namespace OeisA343881

open scoped BigOperators

/-- `m` is an admissible candidate for `T(n, k)`. -/
def IsCandidate (n k m : ℕ) : Prop :=
  k < m ∧ ∃ c x y : ℕ,
    0 < c ∧ 0 < x ∧ x < n ∧ 0 < y ∧ y < n ∧ k ^ x * m ^ y = c ^ n

/-- Relational formulation saying that `m` is the least admissible candidate. -/
def IsTValue (n k m : ℕ) : Prop :=
  IsLeast {r : ℕ | IsCandidate n k r} m

/-- A064549: `k` times the product of the distinct prime factors of `k`. -/
def a064549 (k : ℕ) : ℕ :=
  k * ∏ q ∈ k.primeFactors, q

@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/DomTheDeveloper/formal-conjectures/blob/a0a0c32026e662e2661b126e7782dfc283c2c278/FormalConjectures/OEIS/343881.lean"]
theorem conjecture : answer(False) ↔
    ∀ k : ℕ, 1 < k → ∃ N : ℕ, ∀ p : ℕ, N ≤ p → p.Prime →
      IsTValue p k (a064549 k) := by
  sorry

end OeisA343881
