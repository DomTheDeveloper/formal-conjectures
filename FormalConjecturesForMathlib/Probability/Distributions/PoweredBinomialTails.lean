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

public import FormalConjecturesForMathlib.Probability.Distributions.PoweredBinomialLimit
public import FormalConjecturesForMathlib.Probability.Distributions.StandardizedBinomialMGF

import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Tail identities for powered distributions

The powered-survival construction was defined through its cumulative distribution function. This
file records the corresponding exact left- and right-tail formulas in terms of real-valued measures.
These identities are the bridge from sub-Gaussian bounds for the base standardized binomial law to
uniform tail bounds for the powered law.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal ProbabilityTheory Topology unitInterval

namespace ProbabilityTheory

/-- For `0 ≤ α ≤ 1`, the left tail of the powered-survival transform is bounded by the
`α`th power of the original left tail. -/
lemma one_sub_one_sub_rpow_le_rpow {u α : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    1 - (1 - u) ^ α ≤ u ^ α := by
  have hsub : 0 ≤ 1 - u := sub_nonneg.mpr hu1
  have h := Real.rpow_add_le_add_rpow hu0 hsub hα0 hα1
  have hone : (u + (1 - u)) ^ α = 1 := by simp
  rw [hone] at h
  linarith

/-- For `1 ≤ α`, the left tail of the powered-survival transform is at most `α` times the
original left tail. -/
lemma one_sub_one_sub_rpow_le_mul {u α : ℝ} (hu1 : u ≤ 1) (hα1 : 1 ≤ α) :
    1 - (1 - u) ^ α ≤ α * u := by
  have hs : -1 ≤ -u := by linarith
  have h := one_add_mul_self_le_rpow_one_add (s := -u) hs hα1
  have hsub : 1 + -u = 1 - u := by ring
  rw [hsub] at h
  linarith

/-- The survival function of a real probability measure is the real mass of the open right ray. -/
lemma one_sub_cdf_eq_measureReal_Ioi (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    1 - cdf μ x = μ.real (Ioi x) := by
  have hsum : μ.real (Iic x) + μ.real (Ioi x) = 1 := by
    simpa using (measureReal_add_measureReal_compl (μ := μ) measurableSet_Iic)
  rw [← cdf_eq_real μ x]
  linarith

/-- Exact left-tail formula for the powered-survival probability measure. -/
lemma measureReal_Iic_poweredMeasure
    (μ : Measure ℝ) (α : ℝ) (hα : 0 < α) (x : ℝ) :
    (poweredMeasure μ α hα).real (Iic x) =
      1 - (1 - cdf μ x) ^ α := by
  rw [← cdf_eq_real]
  rw [cdf_poweredMeasure]
  rfl

/-- Exact right-tail formula for the powered-survival probability measure. -/
lemma measureReal_Ioi_poweredMeasure
    (μ : Measure ℝ) (α : ℝ) (hα : 0 < α) (x : ℝ) :
    (poweredMeasure μ α hα).real (Ioi x) =
      (1 - cdf μ x) ^ α := by
  have hsum :
      (poweredMeasure μ α hα).real (Iic x) +
        (poweredMeasure μ α hα).real (Ioi x) = 1 := by
    simpa using
      (measureReal_add_measureReal_compl
        (μ := poweredMeasure μ α hα) measurableSet_Iic)
  rw [measureReal_Iic_poweredMeasure] at hsum
  linarith

/-- Left-tail formula specialized to the powered standardized binomial probability law. -/
lemma measureReal_Iic_poweredStandardizedBinomialProbability
    (n : ℕ) (p : unitInterval) (α : ℝ) (hα : 0 < α) (x : ℝ) :
    (poweredStandardizedBinomialProbability n p α hα : Measure ℝ).real (Iic x) =
      1 - (1 - cdf (standardizedBinomialMeasure n p) x) ^ α := by
  exact measureReal_Iic_poweredMeasure (standardizedBinomialMeasure n p) α hα x

/-- Right-tail formula specialized to the powered standardized binomial probability law. -/
lemma measureReal_Ioi_poweredStandardizedBinomialProbability
    (n : ℕ) (p : unitInterval) (α : ℝ) (hα : 0 < α) (x : ℝ) :
    (poweredStandardizedBinomialProbability n p α hα : Measure ℝ).real (Ioi x) =
      (1 - cdf (standardizedBinomialMeasure n p) x) ^ α := by
  exact measureReal_Ioi_poweredMeasure (standardizedBinomialMeasure n p) α hα x

/-- Uniform right-tail bound for standardized binomial laws. -/
lemma measureReal_Ioi_standardizedBinomialMeasure_le_exp
    (n : ℕ) (hn : 0 < n) (p : unitInterval)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (t : ℝ) (ht : 0 ≤ t) :
    (standardizedBinomialMeasure n p).real (Ioi t) ≤
      exp (-t ^ 2 / (2 * (standardizedBernoulliSubgaussianParameter p : ℝ))) := by
  calc
    (standardizedBinomialMeasure n p).real (Ioi t) ≤
        (standardizedBinomialMeasure n p).real (Ici t) :=
      measureReal_mono Ioi_subset_Ici_self
    _ ≤ exp (-t ^ 2 / (2 * (standardizedBernoulliSubgaussianParameter p : ℝ))) := by
      simpa only [id_eq] using
        (hasSubgaussianMGF_standardizedBinomialMeasure n hn p hp0 hp1).measure_ge_le ht

/-- Uniform left-tail bound for standardized binomial laws. -/
lemma measureReal_Iic_standardizedBinomialMeasure_le_exp
    (n : ℕ) (hn : 0 < n) (p : unitInterval)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (t : ℝ) (ht : 0 ≤ t) :
    (standardizedBinomialMeasure n p).real (Iic (-t)) ≤
      exp (-t ^ 2 / (2 * (standardizedBernoulliSubgaussianParameter p : ℝ))) := by
  have h :=
    ((hasSubgaussianMGF_standardizedBinomialMeasure n hn p hp0 hp1).neg).measure_ge_le ht
  convert h using 1
  ext z
  simp

/-- The right tail of every powered standardized binomial law has a uniform Gaussian bound. -/
lemma measureReal_Ioi_poweredStandardizedBinomialProbability_le_exp_rpow
    (n : ℕ) (hn : 0 < n) (p : unitInterval)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (α : ℝ) (hα : 0 < α) (t : ℝ) (ht : 0 ≤ t) :
    (poweredStandardizedBinomialProbability n p α hα : Measure ℝ).real (Ioi t) ≤
      (exp (-t ^ 2 / (2 * (standardizedBernoulliSubgaussianParameter p : ℝ)))) ^ α := by
  rw [measureReal_Ioi_poweredStandardizedBinomialProbability]
  rw [one_sub_cdf_eq_measureReal_Ioi]
  exact Real.rpow_le_rpow measureReal_nonneg
    (measureReal_Ioi_standardizedBinomialMeasure_le_exp n hn p hp0 hp1 t ht) hα.le

/-- For `0 < α ≤ 1`, the left tail of every powered standardized binomial law has the same
uniform Gaussian-power bound as the right tail. -/
lemma measureReal_Iic_poweredStandardizedBinomialProbability_le_exp_rpow
    (n : ℕ) (hn : 0 < n) (p : unitInterval)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (t : ℝ) (ht : 0 ≤ t) :
    (poweredStandardizedBinomialProbability n p α hα : Measure ℝ).real (Iic (-t)) ≤
      (exp (-t ^ 2 / (2 * (standardizedBernoulliSubgaussianParameter p : ℝ)))) ^ α := by
  rw [measureReal_Iic_poweredStandardizedBinomialProbability]
  rw [cdf_eq_real]
  calc
    1 - (1 - (standardizedBinomialMeasure n p).real (Iic (-t))) ^ α ≤
        ((standardizedBinomialMeasure n p).real (Iic (-t))) ^ α :=
      one_sub_one_sub_rpow_le_rpow measureReal_nonneg measureReal_le_one hα.le hα1
    _ ≤ (exp (-t ^ 2 / (2 * (standardizedBernoulliSubgaussianParameter p : ℝ)))) ^ α :=
      Real.rpow_le_rpow measureReal_nonneg
        (measureReal_Iic_standardizedBinomialMeasure_le_exp n hn p hp0 hp1 t ht) hα.le

/-- For `1 ≤ α`, the left tail of every powered standardized binomial law is bounded by `α`
times the original Gaussian tail bound. -/
lemma measureReal_Iic_poweredStandardizedBinomialProbability_le_mul_exp
    (n : ℕ) (hn : 0 < n) (p : unitInterval)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (α : ℝ) (hα : 0 < α) (hα1 : 1 ≤ α) (t : ℝ) (ht : 0 ≤ t) :
    (poweredStandardizedBinomialProbability n p α hα : Measure ℝ).real (Iic (-t)) ≤
      α * exp (-t ^ 2 / (2 * (standardizedBernoulliSubgaussianParameter p : ℝ))) := by
  rw [measureReal_Iic_poweredStandardizedBinomialProbability]
  rw [cdf_eq_real]
  calc
    1 - (1 - (standardizedBinomialMeasure n p).real (Iic (-t))) ^ α ≤
        α * (standardizedBinomialMeasure n p).real (Iic (-t)) :=
      one_sub_one_sub_rpow_le_mul measureReal_le_one hα1
    _ ≤ α * exp (-t ^ 2 / (2 * (standardizedBernoulliSubgaussianParameter p : ℝ))) := by
      gcongr
      exact measureReal_Iic_standardizedBinomialMeasure_le_exp n hn p hp0 hp1 t ht

end ProbabilityTheory
