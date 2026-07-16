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

/-!
# Tail identities for powered distributions

The powered-survival construction was defined through its cumulative distribution function.  This
file records the corresponding exact left- and right-tail formulas in terms of real-valued measures.
These identities are the bridge from sub-Gaussian bounds for the base standardized binomial law to
uniform tail bounds for the powered law.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal ProbabilityTheory Topology unitInterval

namespace ProbabilityTheory

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

end ProbabilityTheory
