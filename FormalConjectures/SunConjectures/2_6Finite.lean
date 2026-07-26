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

import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic.NativeDecide

/-!
# Finite range for Zhi-Wei Sun's Conjecture 2.6

These two kernel-checked computations discharge exactly the finite remainder
needed by the elementary Chebyshev/totient proof architecture:

* every admissible pair with `n < 214`;
* every admissible pair with `214 ≤ n` and `k * n < 2401`.

The second bound `k < 12` is automatic in its range, because
`214 ≤ n` and `k * n < 2401` imply `k < 12`.
-/

namespace SunConjectures

open scoped Nat.Prime

/-- All admissible pairs with `5 ≤ n < 214`. -/
theorem conjecture_2_6_finite_small_n :
    ∀ n : Fin 214, ∀ k : Fin 214,
      4 < n.val → 1 ≤ k.val → k.val ≤ n.val →
        (π (k.val * n.val)) ^ (k.val + 1) >
          (π ((k.val + 1) * n.val)) ^ k.val := by
  native_decide

/-- All remaining admissible pairs below the analytic threshold `k * n = 2401`. -/
theorem conjecture_2_6_finite_small_x :
    ∀ n : Fin 2401, ∀ k : Fin 12,
      214 ≤ n.val → 1 ≤ k.val → k.val ≤ n.val → k.val * n.val < 2401 →
        (π (k.val * n.val)) ^ (k.val + 1) >
          (π ((k.val + 1) * n.val)) ^ k.val := by
  native_decide

#print axioms conjecture_2_6_finite_small_n
#print axioms conjecture_2_6_finite_small_x

end SunConjectures
