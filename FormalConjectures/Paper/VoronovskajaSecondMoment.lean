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
module

public import FormalConjectures.Paper.VoronovskajaSecondMomentExpectation

/-!
# The squared centered moment of Bézier weights

The squared centered moment of the Bézier weights is the powered standardized-binomial second moment
rescaled by `x(1-x)/n`.  Consequently, multiplication by `sqrt n` still gives a quantity tending to
zero.
-/

public section

noncomputable section

open Topology Filter Real unitInterval Polynomial
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory Topology unitInterval

namespace VoronovskajaTypeFormula

lemma sqrt_mul_sum_sq_centered_bezierWeight_eq
    (n : ℕ) (hn : 0 < n)
    (x : I) (hx0 : 0 < (x : ℝ)) (hx1 : (x : ℝ) < 1)
    (α : ℝ) (hα : 0 < α) :
    Real.sqrt n *
        (∑ k ∈ Finset.range (n + 1),
          ((((k : ℝ) / (n : ℝ)) - (x : ℝ)) ^ 2) *
            bezierWeight n k α (x : ℝ)) =
      (bernoulliStdDev x) ^ 2 *
        ((Real.sqrt n)⁻¹ *
          (∫ z : ℝ, z ^ 2
            ∂(poweredStandardizedBinomialProbability n x α hα : Measure ℝ))) := by
  rw [← standardizedBezierMeasure_eq_poweredStandardizedBinomial n α hα x]
  rw [integral_sq_standardizedBezierMeasure_eq_sum]
  rw [Fin.sum_univ_eq_sum_range]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := by
    rw [Real.sqrt_ne_zero']
    exact_mod_cast hn
  have hsd : bernoulliStdDev x ≠ 0 := (bernoulliStdDev_pos x hx0 hx1).ne'
  rw [standardizeBinomial]
  field_simp [hnR, hsqrt, hsd]
  rw [Real.sq_sqrt]
  · ring
  · positivity

lemma tendsto_sqrt_mul_sum_sq_centered_bezierWeight
    (x : I) (hx0 : 0 < (x : ℝ)) (hx1 : (x : ℝ) < 1)
    (α : ℝ) (hα : 0 < α) :
    Tendsto
      (fun n : ℕ ↦ Real.sqrt n *
        (∑ k ∈ Finset.range (n + 1),
          ((((k : ℝ) / (n : ℝ)) - (x : ℝ)) ^ 2) *
            bezierWeight n k α (x : ℝ)))
      atTop (𝓝 0) := by
  have hsecond :=
    tendsto_inv_sqrt_mul_integral_sq_poweredStandardizedBinomial
      x hx0 hx1 α hα
  have hscaled : Tendsto
      (fun n : ℕ ↦ (bernoulliStdDev x) ^ 2 *
        ((Real.sqrt n)⁻¹ *
          (∫ z : ℝ, z ^ 2
            ∂(poweredStandardizedBinomialProbability n x α hα : Measure ℝ))))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hsecond)
  have hnpos : ∀ᶠ n : ℕ in atTop, 0 < n :=
    eventually_atTop.2 ⟨1, fun n hn ↦ hn⟩
  refine hscaled.congr' ?_
  filter_upwards [hnpos] with n hn
  exact (sqrt_mul_sum_sq_centered_bezierWeight_eq
    n hn x hx0 hx1 α hα).symm

end VoronovskajaTypeFormula
