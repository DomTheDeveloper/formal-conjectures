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

public import FormalConjecturesForMathlib.Probability.Distributions.StandardizedBinomial
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Uniform tails for standardized binomial laws

This file develops the concentration estimate needed to upgrade weak convergence of standardized
binomial laws to convergence of their first moments.  The first step is Hoeffding's lemma for one
standardized Bernoulli variable; the exact binomial MGF power identity will then make the resulting
sub-Gaussian parameter independent of the number of trials.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set unitInterval
open scoped ENNReal NNReal ProbabilityTheory Topology unitInterval

namespace ProbabilityTheory

/-- Hoeffding's sub-Gaussian parameter for one standardized Bernoulli variable. -/
@[expose]
noncomputable def standardizedBernoulliSubgaussianParameter (p : I) : ℝ≥0 :=
  ((‖((1 - (p : ℝ)) / bernoulliStdDev p) -
      (-(p : ℝ) / bernoulliStdDev p)‖₊) / 2) ^ 2

private lemma ae_standardizedBernoulli_mem_Icc
    (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∀ᵐ z ∂Ber((1 : ℝ), 0, p),
      standardizedBernoulli p z ∈
        Icc (-(p : ℝ) / bernoulliStdDev p)
          ((1 - (p : ℝ)) / bernoulliStdDev p) := by
  have hs : 0 < bernoulliStdDev p := bernoulliStdDev_pos p hp0 hp1
  have hle :
      -(p : ℝ) / bernoulliStdDev p ≤
        (1 - (p : ℝ)) / bernoulliStdDev p := by
    rw [div_le_div_iff_of_pos_right hs]
    linarith
  have hOne :
      standardizedBernoulli p (1 : ℝ) ∈
        Icc (-(p : ℝ) / bernoulliStdDev p)
          ((1 - (p : ℝ)) / bernoulliStdDev p) := by
    constructor
    · simpa [standardizedBernoulli] using hle
    · simp [standardizedBernoulli]
  have hZero :
      standardizedBernoulli p (0 : ℝ) ∈
        Icc (-(p : ℝ) / bernoulliStdDev p)
          ((1 - (p : ℝ)) / bernoulliStdDev p) := by
    constructor
    · simp [standardizedBernoulli]
    · simpa [standardizedBernoulli] using hle
  rw [Filter.Eventually, mem_ae_iff]
  rw [bernoulliMeasure_def]
  simp [hOne, hZero]

/-- A centered and variance-one Bernoulli variable is sub-Gaussian, with the explicit Hoeffding
parameter coming from the width of its two-point support. -/
lemma hasSubgaussianMGF_standardizedBernoulli
    (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    HasSubgaussianMGF (standardizedBernoulli p)
      (standardizedBernoulliSubgaussianParameter p)
      Ber((1 : ℝ), 0, p) := by
  rw [standardizedBernoulliSubgaussianParameter]
  exact hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (continuous_standardizedBernoulli p).aemeasurable
    (ae_standardizedBernoulli_mem_Icc p hp0 hp1)
    (integral_standardizedBernoulli p hp0 hp1)

end ProbabilityTheory
