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

import FormalConjectures.Paper.VoronovskajaTypeFormula

/-!
# Counterexample for the formalized Bézier–Bernstein operator

The current definition samples `f (k / n)` using natural-number division.  Consequently it is not
an approximation operator: for `0 < n`, the identity function vanishes at every sample except
`k = n`.
-/

open Topology Filter Real unitInterval Polynomial

namespace VoronovskajaTypeFormula

/-- In the current definition, `k / n` is natural-number division, followed by coercion to `ℝ`. -/
theorem bezierBernstein_uses_nat_division
    (n : ℕ) (α : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    bezierBernstein n α f x =
      ∑ k ∈ Finset.range (n + 1),
        f ((k / n : ℕ) : ℝ) *
          ((bernsteinTail n k).eval x ^ α -
            (bernsteinTail n (k + 1)).eval x ^ α) := by
  rfl

/-- The last Bernstein tail is the last Bernstein basis polynomial. -/
theorem bernsteinTail_self_eval (n : ℕ) (x : ℝ) :
    (bernsteinTail n n).eval x = x ^ n := by
  simp [bernsteinTail, bernsteinPolynomial]

/-- The Bernstein tail starting strictly after `n` vanishes. -/
theorem bernsteinTail_succ_self (n : ℕ) : bernsteinTail n (n + 1) = 0 := by
  simp [bernsteinTail]

/-- Exact value of the currently formalized operator on the identity function. -/
theorem bezierBernstein_id_two_half (n : ℕ) (hn : 0 < n) :
    bezierBernstein n (2 : ℝ) id (1 / 2 : ℝ) = ((1 / 2 : ℝ) ^ n) ^ 2 := by
  rw [bezierBernstein]
  rw [Finset.sum_eq_single n]
  · simp [bernsteinTail_self_eval, bernsteinTail_succ_self, Nat.div_self hn.ne']
  · intro k hk hkn
    have hklt : k < n := by
      simp only [Finset.mem_range] at hk
      omega
    simp [Nat.div_eq_of_lt hklt]
  · simp

end VoronovskajaTypeFormula
