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
# Proof infrastructure for the Bézier–Bernstein Voronovskaja problem

This file records exact identities needed by the asymptotic proof.  In particular, it checks that
Lean elaborates the sampling point `k / n` in `bezierBernstein` as division in `ℝ`.
-/

open Topology Filter Real unitInterval Polynomial

namespace VoronovskajaTypeFormula

/-- The sampling point in the formalized operator is real division, as intended. -/
@[category API, AMS 26 40 47]
theorem bezierBernstein_uses_real_division
    (n : ℕ) (α : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    bezierBernstein n α f x =
      ∑ k ∈ Finset.range (n + 1),
        f ((k : ℝ) / (n : ℝ)) *
          ((bernsteinTail n k).eval x ^ α -
            (bernsteinTail n (k + 1)).eval x ^ α) := by
  rfl

/-- The final Bernstein tail is the final Bernstein basis polynomial. -/
@[category API, AMS 26 40 47]
theorem bernsteinTail_self_eval (n : ℕ) (x : ℝ) :
    (bernsteinTail n n).eval x = x ^ n := by
  simp [bernsteinTail, bernsteinPolynomial]

/-- The Bernstein tail beginning after the final index is zero. -/
@[category API, AMS 26 40 47]
theorem bernsteinTail_succ_self (n : ℕ) : bernsteinTail n (n + 1) = 0 := by
  simp [bernsteinTail]

end VoronovskajaTypeFormula
