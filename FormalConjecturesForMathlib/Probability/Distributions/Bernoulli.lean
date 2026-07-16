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

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction
public import Mathlib.Probability.Distributions.Bernoulli

/-!
# Standardized Bernoulli probability measures

Mathlib already supplies `bernoulliMeasure`, its probability-measure instance, and its integral
formula.  This file adds only the centering and normalization API used by the binomial CLT and tail
bounds in the Voronovskaja proof.
-/

public section

open MeasureTheory Measure unitInterval Complex
open scoped ENNReal

namespace ProbabilityTheory

section Standardized

/-- Standard deviation of a nondegenerate Bernoulli variable with success probability `p`. -/
@[expose]
noncomputable def bernoulliStdDev (p : I) : ℝ := Real.sqrt ((p : ℝ) * (1 - p))

/-- Center and normalize a real Bernoulli variable. -/
@[expose]
noncomputable def standardizedBernoulli (p : I) (z : ℝ) : ℝ :=
  (z - p) / bernoulliStdDev p

@[fun_prop]
lemma continuous_standardizedBernoulli (p : I) : Continuous (standardizedBernoulli p) := by
  unfold standardizedBernoulli
  fun_prop

lemma bernoulliStdDev_pos (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    0 < bernoulliStdDev p := by
  rw [bernoulliStdDev, Real.sqrt_pos]
  exact mul_pos hp0 (sub_pos.mpr hp1)

lemma integral_standardizedBernoulli (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∫ z, standardizedBernoulli p z ∂Ber((1 : ℝ), 0, p) = 0 := by
  rw [integral_bernoulliMeasure]
  simp only [smul_eq_mul, standardizedBernoulli]
  have hs : bernoulliStdDev p ≠ 0 := (bernoulliStdDev_pos p hp0 hp1).ne'
  field_simp [hs]
  ring

lemma integral_sq_standardizedBernoulli
    (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∫ z, standardizedBernoulli p z ^ 2 ∂Ber((1 : ℝ), 0, p) = 1 := by
  rw [integral_bernoulliMeasure]
  simp only [smul_eq_mul, standardizedBernoulli]
  have hvar : 0 ≤ (p : ℝ) * (1 - p) :=
    (mul_pos hp0 (sub_pos.mpr hp1)).le
  rw [div_pow, div_pow, bernoulliStdDev, Real.sq_sqrt hvar]
  have hq : 1 - (p : ℝ) ≠ 0 := sub_ne_zero.mpr hp1.ne.symm
  field_simp [hp0.ne', hq]
  ring

lemma charFun_standardizedBernoulli
    (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (t : ℝ) :
    charFun (Ber((1 : ℝ), 0, p).map (standardizedBernoulli p)) t =
      (p : ℂ) * exp (t * ((1 - (p : ℝ)) / bernoulliStdDev p) * Complex.I) +
        ((1 - (p : ℝ) : ℝ) : ℂ) *
          exp (t * (-(p : ℝ) / bernoulliStdDev p) * Complex.I) := by
  rw [charFun_apply_real, integral_map]
  · rw [integral_bernoulliMeasure]
    simp only [RCLike.real_smul_eq_coe_mul, standardizedBernoulli, sub_zero, zero_sub]
    push_cast
    congr 1 <;> ring
  · exact (continuous_standardizedBernoulli p).aemeasurable
  · fun_prop

end Standardized

end ProbabilityTheory
