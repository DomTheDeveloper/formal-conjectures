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

public import FormalConjectures.Paper.VoronovskajaExpectation

/-!
# The centered first-moment asymptotic for Bézier--Bernstein weights

The standardized powered law has a convergent first moment.  This file identifies that moment
algebraically with `sqrt n` times the first centered moment of the Bézier weights.
-/

public section

noncomputable section

open Topology Filter Real unitInterval Polynomial
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory Topology unitInterval

namespace VoronovskajaTypeFormula

/-- Exact algebraic identification of the scaled centered moment with the standardized expectation. -/
lemma sqrt_mul_bezierCenteredMoment_eq_stdDev_mul_integral
    (n : ℕ) (hn : 0 < n)
    (x : I) (hx0 : 0 < (x : ℝ)) (hx1 : (x : ℝ) < 1)
    (α : ℝ) (hα : 0 < α) :
    Real.sqrt n * bezierCenteredMoment n α (x : ℝ) =
      bernoulliStdDev x *
        (∫ z : ℝ, z
          ∂(poweredStandardizedBinomialProbability n x α hα : Measure ℝ)) := by
  rw [← standardizedBezierMeasure_eq_poweredStandardizedBinomial n α hα x]
  rw [integral_id_standardizedBezierMeasure_eq_sum]
  rw [bezierCenteredMoment, Finset.mul_sum, Finset.mul_sum]
  have hsum :
      (∑ k : Fin (n + 1),
        bernoulliStdDev x *
          (bezierWeight n (k : ℕ) α (x : ℝ) *
            standardizeBinomial n x ((k : ℕ) : ℝ))) =
        ∑ k ∈ Finset.range (n + 1),
          bernoulliStdDev x *
            (bezierWeight n k α (x : ℝ) *
              standardizeBinomial n x (k : ℝ)) := by
    simpa using (Fin.sum_univ_eq_sum_range
      (f := fun k : ℕ =>
        bernoulliStdDev x *
          (bezierWeight n k α (x : ℝ) *
            standardizeBinomial n x (k : ℝ))) (n + 1))
  rw [hsum]
  apply Finset.sum_congr rfl
  intro k hk
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := by
    rw [Real.sqrt_ne_zero']
    exact_mod_cast hn
  have hsd : bernoulliStdDev x ≠ 0 := (bernoulliStdDev_pos x hx0 hx1).ne'
  rw [standardizeBinomial]
  field_simp [hnR, hsqrt, hsd]
  rw [Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ))]

/-- Exact centered first-moment asymptotic at every interior point. -/
lemma tendsto_sqrt_mul_bezierCenteredMoment
    (x : I) (hx0 : 0 < (x : ℝ)) (hx1 : (x : ℝ) < 1)
    (α : ℝ) (hα : 0 < α) :
    Tendsto
      (fun n : ℕ ↦ Real.sqrt n * bezierCenteredMoment n α (x : ℝ))
      atTop
      (𝓝 (bernoulliStdDev x * poweredGaussianFirstMomentConstant α)) := by
  have hmean := tendsto_integral_id_poweredStandardizedBinomial x hx0 hx1 α hα
  have hscaled :
      Tendsto
        (fun n : ℕ ↦ bernoulliStdDev x *
          (∫ z : ℝ, z
            ∂(poweredStandardizedBinomialProbability n x α hα : Measure ℝ)))
        atTop
        (𝓝 (bernoulliStdDev x * poweredGaussianFirstMomentConstant α)) :=
    tendsto_const_nhds.mul hmean
  have hnpos : ∀ᶠ n : ℕ in atTop, 0 < n :=
    eventually_atTop.2 ⟨1, fun n hn ↦ hn⟩
  refine hscaled.congr' ?_
  filter_upwards [hnpos] with n hn
  exact (sqrt_mul_bezierCenteredMoment_eq_stdDev_mul_integral
    n hn x hx0 hx1 α hα).symm

end VoronovskajaTypeFormula
