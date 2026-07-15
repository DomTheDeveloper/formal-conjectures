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

import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Powered survival distributions

For a real probability distribution with CDF `F` and `α > 0`, the function
`x ↦ 1 - (1 - F x) ^ α` is again a CDF.  Applied to the standard Gaussian, this is the limit law
for the standardized Bézier–Bernstein weights.
-/

open Filter MeasureTheory Set Topology
open scoped Topology

namespace ProbabilityTheory

/-- The CDF obtained by raising the survival function of `μ` to the positive power `α`. -/
noncomputable def poweredCDF (μ : Measure ℝ) (α : ℝ) (hα : 0 < α) :
    StieltjesFunction ℝ where
  toFun x := 1 - (1 - cdf μ x) ^ α
  mono' := by
    intro a b hab
    have hCDF : cdf μ a ≤ cdf μ b := monotone_cdf μ hab
    have hbase : 1 - cdf μ b ≤ 1 - cdf μ a := sub_le_sub_left hCDF 1
    have hp : (1 - cdf μ b) ^ α ≤ (1 - cdf μ a) ^ α :=
      Real.rpow_le_rpow (sub_nonneg.mpr (cdf_le_one μ b)) hbase hα.le
    linarith
  right_continuous' := by
    intro x
    exact continuousWithinAt_const.sub
      ((continuousWithinAt_const.sub ((cdf μ).right_continuous x)).rpow_const (.inr hα.le))

@[simp]
lemma poweredCDF_apply (μ : Measure ℝ) (α : ℝ) (hα : 0 < α) (x : ℝ) :
    poweredCDF μ α hα x = 1 - (1 - cdf μ x) ^ α := rfl

lemma tendsto_poweredCDF_atBot (μ : Measure ℝ) (α : ℝ) (hα : 0 < α) :
    Tendsto (poweredCDF μ α hα) atBot (𝓝 0) := by
  change Tendsto (fun x : ℝ ↦ 1 - (1 - cdf μ x) ^ α) atBot (𝓝 0)
  have hbase : Tendsto (fun x : ℝ ↦ 1 - cdf μ x) atBot (𝓝 1) := by
    convert tendsto_const_nhds.sub (tendsto_cdf_atBot μ) using 1 <;> simp
  have hp : Tendsto (fun x : ℝ ↦ (1 - cdf μ x) ^ α) atBot (𝓝 1) := by
    convert hbase.rpow_const (.inl one_ne_zero) using 1 <;> simp
  convert tendsto_const_nhds.sub hp using 1 <;> simp

lemma tendsto_poweredCDF_atTop (μ : Measure ℝ) (α : ℝ) (hα : 0 < α) :
    Tendsto (poweredCDF μ α hα) atTop (𝓝 1) := by
  change Tendsto (fun x : ℝ ↦ 1 - (1 - cdf μ x) ^ α) atTop (𝓝 1)
  have hbase : Tendsto (fun x : ℝ ↦ 1 - cdf μ x) atTop (𝓝 0) := by
    convert tendsto_const_nhds.sub (tendsto_cdf_atTop μ) using 1 <;> simp
  have hp : Tendsto (fun x : ℝ ↦ (1 - cdf μ x) ^ α) atTop (𝓝 0) := by
    convert hbase.rpow_const (.inr hα.le) using 1 <;> simp [Real.zero_rpow hα.ne']
  convert tendsto_const_nhds.sub hp using 1 <;> simp

/-- The probability measure associated to `poweredCDF`. -/
noncomputable def poweredMeasure (μ : Measure ℝ) (α : ℝ) (hα : 0 < α) : Measure ℝ :=
  (poweredCDF μ α hα).measure

instance isProbabilityMeasure_poweredMeasure
    (μ : Measure ℝ) (α : ℝ) (hα : 0 < α) :
    IsProbabilityMeasure (poweredMeasure μ α hα) := by
  constructor
  rw [poweredMeasure, StieltjesFunction.measure_univ _
    (tendsto_poweredCDF_atBot μ α hα) (tendsto_poweredCDF_atTop μ α hα)]
  simp

lemma cdf_poweredMeasure (μ : Measure ℝ) (α : ℝ) (hα : 0 < α) :
    cdf (poweredMeasure μ α hα) = poweredCDF μ α hα := by
  exact cdf_measure_stieltjesFunction _
    (tendsto_poweredCDF_atBot μ α hα) (tendsto_poweredCDF_atTop μ α hα)

/-- The powered-survival transform of the standard Gaussian distribution. -/
noncomputable def poweredGaussianMeasure (α : ℝ) (hα : 0 < α) : Measure ℝ :=
  poweredMeasure (gaussianReal 0 1) α hα

instance isProbabilityMeasure_poweredGaussianMeasure (α : ℝ) (hα : 0 < α) :
    IsProbabilityMeasure (poweredGaussianMeasure α hα) :=
  isProbabilityMeasure_poweredMeasure _ _ _

lemma cdf_poweredGaussianMeasure (α : ℝ) (hα : 0 < α) (x : ℝ) :
    cdf (poweredGaussianMeasure α hα) x =
      1 - (1 - cdf (gaussianReal 0 1) x) ^ α := by
  rw [poweredGaussianMeasure, cdf_poweredMeasure]
  rfl

end ProbabilityTheory
