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

public import FormalConjecturesForMathlib.Probability.CentralLimitTheorem
public import FormalConjecturesForMathlib.Probability.Distributions.Bernoulli
public import FormalConjecturesForMathlib.Probability.Distributions.Binomial
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Standardized binomial laws

This file identifies the characteristic function of a centered and normalized binomial law with
an `n`th power of a centered Bernoulli characteristic function. The one-dimensional CLT then gives
weak convergence to the standard Gaussian.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology unitInterval

namespace ProbabilityTheory

/-- Center and normalize a real binomial value. -/
@[expose]
noncomputable def standardizeBinomial (n : ℕ) (p : I) (z : ℝ) : ℝ :=
  (Real.sqrt n)⁻¹ * ((z - n * (p : ℝ)) / bernoulliStdDev p)

@[fun_prop]
lemma continuous_standardizeBinomial (n : ℕ) (p : I) : Continuous (standardizeBinomial n p) := by
  unfold standardizeBinomial
  fun_prop

/-- The centered, variance-one binomial law. -/
@[expose]
noncomputable def standardizedBinomialMeasure (n : ℕ) (p : I) : Measure ℝ :=
  Bin(ℝ, n, p).map (standardizeBinomial n p)

instance isProbabilityMeasure_standardizedBinomialMeasure (n : ℕ) (p : I) :
    IsProbabilityMeasure (standardizedBinomialMeasure n p) :=
  isProbabilityMeasure_map (continuous_standardizeBinomial n p).aemeasurable

/-- The probability-measure wrapper of the standardized binomial law. -/
@[expose]
noncomputable def standardizedBinomialProbability (n : ℕ) (p : I) : ProbabilityMeasure ℝ :=
  ⟨standardizedBinomialMeasure n p, inferInstance⟩

/-- The standard Gaussian as a probability measure. -/
@[expose]
noncomputable def standardGaussianProbability : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 1, inferInstance⟩

lemma charFun_standardizedBinomialMeasure
    (n : ℕ) (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (t : ℝ) :
    charFun (standardizedBinomialMeasure n p) t =
      (charFun (Ber((1 : ℝ), 0, p).map (standardizedBernoulli p))
        ((Real.sqrt n)⁻¹ * t)) ^ n := by
  rw [standardizedBinomialMeasure, charFun_apply_real, integral_map]
  · have hsplit (z : ℝ) :
        exp (t * standardizeBinomial n p z * Complex.I) =
          exp (((Real.sqrt n)⁻¹ * t / bernoulliStdDev p) * z * Complex.I) *
            exp (-((Real.sqrt n)⁻¹ * t / bernoulliStdDev p) *
              (n * (p : ℝ)) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      rw [standardizeBinomial]
      push_cast
      ring
    simp_rw [hsplit]
    rw [integral_mul_const, ← charFun_apply_real, charFun_map_cast_binomial]
    rw [charFun_standardizedBernoulli p hp0 hp1]
    let s : ℝ := (Real.sqrt n)⁻¹ * t
    let a : ℝ := s / bernoulliStdDev p
    have hfactor :
        (p : ℂ) * exp (s * ((1 - (p : ℝ)) / bernoulliStdDev p) * Complex.I) +
            ((1 - (p : ℝ) : ℝ) : ℂ) *
              exp (s * (-(p : ℝ) / bernoulliStdDev p) * Complex.I) =
          (((1 - (p : ℝ) : ℝ) : ℂ) + (p : ℂ) * exp (a * Complex.I)) *
            exp (-(a * (p : ℝ)) * Complex.I) := by
      have hexp :
          exp (s * ((1 - (p : ℝ)) / bernoulliStdDev p) * Complex.I) =
            exp (a * Complex.I) * exp (-(a * (p : ℝ)) * Complex.I) := by
        rw [← Complex.exp_add]
        congr 1
        dsimp [a]
        ring
      have hneg :
          exp (s * (-(p : ℝ) / bernoulliStdDev p) * Complex.I) =
            exp (-(a * (p : ℝ)) * Complex.I) := by
        congr 1
        dsimp [a]
        ring
      rw [hexp, hneg]
      ring
    rw [hfactor, mul_pow, ← Complex.exp_nat_mul]
    dsimp [a, s]
    congr 1
    · congr 1
      congr 2
      ring
    · congr 1
      push_cast
      ring
  · exact (continuous_standardizeBinomial n p).aemeasurable
  · fun_prop

lemma tendsto_standardizedBinomialProbability
    (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Tendsto (fun n ↦ standardizedBinomialProbability n p) atTop
      (𝓝 standardGaussianProbability) := by
  refine ProbabilityMeasure.tendsto_of_tendsto_charFun fun t ↦ ?_
  change Tendsto (fun n ↦ charFun (standardizedBinomialMeasure n p) t) atTop
    (𝓝 (charFun (gaussianReal 0 1) t))
  simp_rw [charFun_standardizedBinomialMeasure n p hp0 hp1 t]
  simpa [charFun_gaussianReal, neg_div] using
    tendsto_charFun_inv_sqrt_mul_pow
      (P := Ber((1 : ℝ), 0, p))
      (X := standardizedBernoulli p)
      (continuous_standardizedBernoulli p).aemeasurable
      (integral_standardizedBernoulli p hp0 hp1)
      (by simpa only [Pi.pow_apply] using integral_sq_standardizedBernoulli p hp0 hp1)
      t

end ProbabilityTheory
