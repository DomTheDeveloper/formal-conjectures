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

public import FormalConjecturesForMathlib.Probability.CDFConvergence
public import FormalConjecturesForMathlib.Probability.Distributions.PoweredGaussian
public import FormalConjecturesForMathlib.Probability.Distributions.StandardizedBinomial

/-!
# Powered standardized binomial limits

The standardized binomial law converges weakly to the standard Gaussian.  Applying the continuous
transformation `F ↦ 1 - (1 - F)^α` to the cumulative distribution functions therefore gives weak
convergence of the powered laws to the powered Gaussian law.
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology unitInterval

namespace ProbabilityTheory

/-- Wrap the powered-CDF transform of a probability measure as a probability measure. -/
@[expose]
noncomputable def poweredProbability
    (μ : ProbabilityMeasure ℝ) (α : ℝ) (hα : 0 < α) : ProbabilityMeasure ℝ :=
  ⟨poweredMeasure (μ : Measure ℝ) α hα, inferInstance⟩

/-- Powered standardized binomial probability law. -/
@[expose]
noncomputable def poweredStandardizedBinomialProbability
    (n : ℕ) (p : I) (α : ℝ) (hα : 0 < α) : ProbabilityMeasure ℝ :=
  poweredProbability (standardizedBinomialProbability n p) α hα

/-- Powered standard Gaussian probability law. -/
@[expose]
noncomputable def poweredGaussianProbability
    (α : ℝ) (hα : 0 < α) : ProbabilityMeasure ℝ :=
  ⟨poweredGaussianMeasure α hα, inferInstance⟩

lemma tendsto_cdf_standardizedBinomialProbability
    (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (x : ℝ) :
    Tendsto (fun n ↦ cdf (standardizedBinomialMeasure n p) x) atTop
      (𝓝 (cdf (gaussianReal 0 1) x)) := by
  have hweak := tendsto_standardizedBinomialProbability p hp0 hp1
  have hnull : standardGaussianProbability (frontier (Iic x)) = 0 := by
    rw [frontier_Iic]
    have hgauss : gaussianReal 0 1 {x} = 0 := by
      letI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal (by norm_num)
      simp
    simpa [standardGaussianProbability] using hgauss
  have hmass :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hweak hnull
  have hreal : Tendsto
      (fun n ↦ ((standardizedBinomialProbability n p) (Iic x) : ℝ)) atTop
      (𝓝 ((standardGaussianProbability (Iic x) : ℝ))) :=
    NNReal.tendsto_coe.mpr hmass
  simpa only [cdf_eq_real, ProbabilityMeasure.measureReal_eq_coe_coeFn,
    standardizedBinomialProbability, standardGaussianProbability,
    ProbabilityMeasure.coe_mk] using hreal

lemma tendsto_poweredStandardizedBinomialProbability
    (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (α : ℝ) (hα : 0 < α) :
    Tendsto (fun n ↦ poweredStandardizedBinomialProbability n p α hα) atTop
      (𝓝 (poweredGaussianProbability α hα)) := by
  apply ProbabilityMeasure.tendsto_of_tendsto_cdf
  intro x
  have hcdf := tendsto_cdf_standardizedBinomialProbability p hp0 hp1 x
  have hbase : Tendsto
      (fun n ↦ 1 - cdf (standardizedBinomialMeasure n p) x) atTop
      (𝓝 (1 - cdf (gaussianReal 0 1) x)) :=
    tendsto_const_nhds.sub hcdf
  have hpow : Tendsto
      (fun n ↦ (1 - cdf (standardizedBinomialMeasure n p) x) ^ α) atTop
      (𝓝 ((1 - cdf (gaussianReal 0 1) x) ^ α)) :=
    hbase.rpow_const (.inr hα.le)
  have hfinal : Tendsto
      (fun n ↦ 1 - (1 - cdf (standardizedBinomialMeasure n p) x) ^ α) atTop
      (𝓝 (1 - (1 - cdf (gaussianReal 0 1) x) ^ α)) :=
    tendsto_const_nhds.sub hpow
  simpa only [poweredStandardizedBinomialProbability, poweredProbability,
    poweredGaussianProbability, ProbabilityMeasure.coe_mk,
    cdf_poweredMeasure, poweredCDF_apply, cdf_poweredGaussianMeasure] using hfinal

end ProbabilityTheory
