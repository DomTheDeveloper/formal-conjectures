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
import FormalConjecturesForMathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-!
# Proof infrastructure for the Bézier–Bernstein Voronovskaja problem

This file records exact identities needed by the asymptotic proof. In particular, it checks that
Lean elaborates the sampling point `k / n` in `bezierBernstein` as division in `ℝ`, and proves that
the Bézier coefficients form a probability mass function.
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

/-- The initial Bernstein tail is the constant polynomial one. -/
@[category API, AMS 26 40 47]
theorem bernsteinTail_zero (n : ℕ) : bernsteinTail n 0 = 1 := by
  rw [bernsteinTail]
  have hIcc : Finset.Icc 0 n = Finset.range (n + 1) := by
    ext j
    simp
  rw [hIcc, bernsteinPolynomial.sum]

/-- Evaluation of a Bernstein tail as its explicit binomial-probability sum. -/
@[category API, AMS 26 40 47]
theorem bernsteinTail_eval_eq_sum (n k : ℕ) (x : ℝ) :
    (bernsteinTail n k).eval x =
      ∑ j ∈ Finset.Icc k n,
        (n.choose j : ℝ) * x ^ j * (1 - x) ^ (n - j) := by
  simp [bernsteinTail, bernsteinPolynomial]

/-- The Bézier mass attached to the sampling point `k / n`. -/
noncomputable def bezierWeight (n k : ℕ) (α x : ℝ) : ℝ :=
  (bernsteinTail n k).eval x ^ α - (bernsteinTail n (k + 1)).eval x ^ α

@[category API, AMS 26 40 47]
private theorem sum_range_succ_sub (a : ℕ → ℝ) (m : ℕ) :
    ∑ k ∈ Finset.range m, (a k - a (k + 1)) = a 0 - a m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- For positive shape parameter, the Bézier weights have total mass one. -/
@[category API, AMS 26 40 47]
theorem sum_bezierWeight (n : ℕ) {α : ℝ} (hα : 0 < α) (x : ℝ) :
    ∑ k ∈ Finset.range (n + 1), bezierWeight n k α x = 1 := by
  rw [show (∑ k ∈ Finset.range (n + 1), bezierWeight n k α x) =
      ∑ k ∈ Finset.range (n + 1),
        ((bernsteinTail n k).eval x ^ α -
          (bernsteinTail n (k + 1)).eval x ^ α) by rfl]
  rw [sum_range_succ_sub]
  simp [bernsteinTail_zero, bernsteinTail_succ_self, hα.ne']

end VoronovskajaTypeFormula
