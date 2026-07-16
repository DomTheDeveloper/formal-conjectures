/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Paper.VoronovskajaDefinitions
import FormalConjecturesForMathlib.Probability.CentralLimitTheorem
import FormalConjecturesForMathlib.Probability.Distributions.Binomial

/-!
# Proof infrastructure for the Bézier–Bernstein Voronovskaja problem

This file records exact identities needed by the asymptotic proof. In particular, it checks that
Lean elaborates the sampling point `k / n` in `bezierBernstein` as division in `ℝ`, proves that the
Bézier coefficients form a probability mass function, expresses their first centered moment as a
powered-binomial-tail sum, and splits the approximation error into its linear moment and
Taylor-remainder parts.
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

/-- A Bernstein tail is its first basis term plus the following tail. -/
@[category API, AMS 26 40 47]
theorem bernsteinTail_eval_eq_bernstein_add_succ
    (n k : ℕ) (hk : k ≤ n) (x : ℝ) :
    (bernsteinTail n k).eval x =
      (bernsteinPolynomial ℝ n k).eval x + (bernsteinTail n (k + 1)).eval x := by
  rw [bernsteinTail_eval_eq_sum, bernsteinTail_eval_eq_sum]
  rw [← Finset.insert_Icc_succ_left_eq_Icc hk, Finset.sum_insert]
  · simp [bernsteinPolynomial]
  · simp

/-- Every Bernstein basis polynomial is nonnegative on the unit interval. -/
@[category API, AMS 26 40 47]
theorem bernsteinPolynomial_eval_nonneg
    (n k : ℕ) {x : ℝ} (hx : x ∈ I) :
    0 ≤ (bernsteinPolynomial ℝ n k).eval x := by
  simp only [bernsteinPolynomial, Polynomial.eval_mul, Polynomial.eval_natCast,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one]
  have hx0 : 0 ≤ x := hx.1
  have hx1 : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
  positivity

/-- Every Bernstein tail is nonnegative on the unit interval. -/
@[category API, AMS 26 40 47]
theorem bernsteinTail_eval_nonneg
    (n k : ℕ) {x : ℝ} (hx : x ∈ I) :
    0 ≤ (bernsteinTail n k).eval x := by
  rw [bernsteinTail_eval_eq_sum]
  apply Finset.sum_nonneg
  intro j hj
  have hx0 : 0 ≤ x := hx.1
  have hx1 : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
  positivity

/-- Bernstein tails decrease with the starting index. -/
@[category API, AMS 26 40 47]
theorem bernsteinTail_succ_eval_le
    (n k : ℕ) (hk : k ≤ n) {x : ℝ} (hx : x ∈ I) :
    (bernsteinTail n (k + 1)).eval x ≤ (bernsteinTail n k).eval x := by
  rw [bernsteinTail_eval_eq_bernstein_add_succ n k hk x]
  exact le_add_of_nonneg_left (bernsteinPolynomial_eval_nonneg n k hx)

/-- Every Bernstein tail is at most one on the unit interval. -/
@[category API, AMS 26 40 47]
theorem bernsteinTail_eval_le_one
    (n k : ℕ) {x : ℝ} (hx : x ∈ I) :
    (bernsteinTail n k).eval x ≤ 1 := by
  rw [bernsteinTail_eval_eq_sum]
  calc
    (∑ j ∈ Finset.Icc k n,
        (n.choose j : ℝ) * x ^ j * (1 - x) ^ (n - j)) ≤
        ∑ j ∈ Finset.Icc 0 n,
          (n.choose j : ℝ) * x ^ j * (1 - x) ^ (n - j) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        simp only [Finset.mem_Icc] at hj ⊢
        exact ⟨Nat.zero_le j, hj.2⟩
      · intro j hj hnot
        have hx0 : 0 ≤ x := hx.1
        have hx1 : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
        positivity
    _ = (bernsteinTail n 0).eval x := by
      rw [bernsteinTail_eval_eq_sum]
    _ = 1 := by simp [bernsteinTail_zero]

/-- The Bézier mass attached to the sampling point `k / n`. -/
noncomputable def bezierWeight (n k : ℕ) (α x : ℝ) : ℝ :=
  (bernsteinTail n k).eval x ^ α - (bernsteinTail n (k + 1)).eval x ^ α

/-- For positive shape parameter, every Bézier weight is nonnegative on the unit interval. -/
@[category API, AMS 26 40 47]
theorem bezierWeight_nonneg
    (n k : ℕ) (hk : k ≤ n) {α x : ℝ} (hα : 0 < α) (hx : x ∈ I) :
    0 ≤ bezierWeight n k α x := by
  rw [bezierWeight]
  exact sub_nonneg.mpr <| Real.rpow_le_rpow
    (bernsteinTail_eval_nonneg n (k + 1) hx)
    (bernsteinTail_succ_eval_le n k hk hx) hα.le

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

/-- Discrete summation by parts for a first moment of successive differences. -/
@[category API, AMS 26 40 47]
private theorem sum_range_succ_cast_mul_sub (a : ℕ → ℝ) (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), (k : ℝ) * (a k - a (k + 1)) =
      ∑ k ∈ Finset.range m, a (k + 1) - (m : ℝ) * a (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      push_cast
      ring

/-- The uncentered first moment of the Bézier weights is the sum of the powered Bernstein tails. -/
@[category API, AMS 26 40 47]
theorem sum_cast_mul_bezierWeight (n : ℕ) {α : ℝ} (hα : 0 < α) (x : ℝ) :
    ∑ k ∈ Finset.range (n + 1), (k : ℝ) * bezierWeight n k α x =
      ∑ k ∈ Finset.range n, (bernsteinTail n (k + 1)).eval x ^ α := by
  rw [show (∑ k ∈ Finset.range (n + 1), (k : ℝ) * bezierWeight n k α x) =
      ∑ k ∈ Finset.range (n + 1), (k : ℝ) *
        ((bernsteinTail n k).eval x ^ α -
          (bernsteinTail n (k + 1)).eval x ^ α) by rfl]
  rw [sum_range_succ_cast_mul_sub]
  simp [bernsteinTail_succ_self, hα.ne']

/-- The first centered moment of the Bézier probability weights. -/
noncomputable def bezierCenteredMoment (n : ℕ) (α x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (((k : ℝ) / (n : ℝ)) - x) * bezierWeight n k α x

/-- Exact tail-sum formula for the centered first moment. -/
@[category API, AMS 26 40 47]
theorem bezierCenteredMoment_eq_tail_sum (n : ℕ) {α : ℝ} (hα : 0 < α) (x : ℝ) :
    bezierCenteredMoment n α x =
      (∑ k ∈ Finset.range n, (bernsteinTail n (k + 1)).eval x ^ α) / (n : ℝ) - x := by
  rw [bezierCenteredMoment]
  simp_rw [sub_mul, div_mul_eq_mul_div]
  rw [Finset.sum_sub_distrib, Finset.sum_div, ← Finset.mul_sum,
    sum_cast_mul_bezierWeight n hα x, sum_bezierWeight n hα x, mul_one]

/-- The weighted first-order Taylor remainder of `f` at `x`. -/
noncomputable def bezierTaylorRemainder
    (n : ℕ) (α : ℝ) (f : ℝ → ℝ) (x slope : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (f ((k : ℝ) / (n : ℝ)) - f x -
      slope * (((k : ℝ) / (n : ℝ)) - x)) * bezierWeight n k α x

/-- Exact decomposition of the Bézier approximation error into a centered first moment and a
Taylor-remainder term. -/
@[category API, AMS 26 40 47]
theorem bezierBernstein_sub_eq_moment_add_remainder
    (n : ℕ) {α : ℝ} (hα : 0 < α) (f : ℝ → ℝ) (x slope : ℝ) :
    bezierBernstein n α f x - f x =
      slope * bezierCenteredMoment n α x +
        bezierTaylorRemainder n α f x slope := by
  calc
    bezierBernstein n α f x - f x =
        ∑ k ∈ Finset.range (n + 1),
          (f ((k : ℝ) / (n : ℝ)) - f x) * bezierWeight n k α x := by
      rw [bezierBernstein_uses_real_division]
      simp_rw [bezierWeight, sub_mul]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_bezierWeight n hα x, mul_one]
    _ = ∑ k ∈ Finset.range (n + 1),
          (slope * ((((k : ℝ) / (n : ℝ)) - x) * bezierWeight n k α x) +
            (f ((k : ℝ) / (n : ℝ)) - f x -
              slope * (((k : ℝ) / (n : ℝ)) - x)) * bezierWeight n k α x) := by
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = slope * bezierCenteredMoment n α x +
        bezierTaylorRemainder n α f x slope := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      rfl

end VoronovskajaTypeFormula
