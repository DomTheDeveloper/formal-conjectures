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

public import FormalConjectures.Paper.VoronovskajaMomentLimit
public import FormalConjecturesForMathlib.Probability.Distributions.PoweredBinomialSecondMoment
public import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Second moments of powered standardized-binomial laws

This file identifies the layer-cake second-moment tail integral with the actual second moment.
-/

public section

noncomputable section

open Topology Filter Real unitInterval Polynomial
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory Topology unitInterval

namespace VoronovskajaTypeFormula

lemma integrable_sq_standardizedBezierMeasure
    (n : ℕ) (α : ℝ) (hα : 0 < α) (x : I) :
    Integrable (fun z : ℝ ↦ z ^ 2) (standardizedBezierMeasure n α hα x) := by
  rw [standardizedBezierMeasure, standardizedBezierPMF]
  rw [← PMF.toMeasure_map (p := bezierPMF n α hα x)
    (f := fun k : Fin (n + 1) => standardizeBinomial n x ((k : ℕ) : ℝ))
    Measurable.of_discrete]
  rw [integrable_map_measure (by fun_prop) Measurable.of_discrete.aemeasurable]
  exact .of_finite

lemma integrable_sq_poweredStandardizedBinomial
    (n : ℕ) (α : ℝ) (hα : 0 < α) (x : I) :
    Integrable (fun z : ℝ ↦ z ^ 2)
      (poweredStandardizedBinomialProbability n x α hα : Measure ℝ) := by
  rw [← standardizedBezierMeasure_eq_poweredStandardizedBinomial n α hα x]
  exact integrable_sq_standardizedBezierMeasure n α hα x

lemma integral_sq_poweredStandardizedBinomial_eq_secondMomentTail
    (n : ℕ) (α : ℝ) (hα : 0 < α) (x : I) :
    (∫ z : ℝ, z ^ 2
      ∂(poweredStandardizedBinomialProbability n x α hα : Measure ℝ)) =
      ∫ t in Ioi 0,
        poweredStandardizedBinomialSecondMomentTail n x α hα t := by
  have hsq := integrable_sq_poweredStandardizedBinomial n α hα x
  simpa [poweredStandardizedBinomialSecondMomentTail] using
    hsq.integral_eq_integral_meas_lt
      (Eventually.of_forall fun z : ℝ ↦ sq_nonneg z)

lemma tendsto_inv_sqrt_mul_integral_sq_poweredStandardizedBinomial
    (x : I) (hx0 : 0 < (x : ℝ)) (hx1 : (x : ℝ) < 1)
    (α : ℝ) (hα : 0 < α) :
    Tendsto
      (fun n : ℕ ↦ (Real.sqrt n)⁻¹ *
        (∫ z : ℝ, z ^ 2
          ∂(poweredStandardizedBinomialProbability n x α hα : Measure ℝ)))
      atTop (𝓝 0) := by
  have htail :=
    tendsto_inv_sqrt_mul_integral_poweredStandardizedBinomialSecondMomentTail
      x hx0 hx1 α hα
  refine htail.congr' ?_
  filter_upwards with n
  rw [integral_sq_poweredStandardizedBinomial_eq_secondMomentTail]
  rw [integral_const_mul]

lemma integral_sq_standardizedBezierMeasure_eq_sum
    (n : ℕ) (α : ℝ) (hα : 0 < α) (x : I) :
    (∫ z : ℝ, z ^ 2 ∂(standardizedBezierMeasure n α hα x)) =
      ∑ k : Fin (n + 1),
        bezierWeight n k α (x : ℝ) *
          (standardizeBinomial n x ((k : ℕ) : ℝ)) ^ 2 := by
  rw [standardizedBezierMeasure, standardizedBezierPMF]
  rw [← PMF.toMeasure_map (p := bezierPMF n α hα x)
    (f := fun k : Fin (n + 1) => standardizeBinomial n x ((k : ℕ) : ℝ))
    Measurable.of_discrete]
  rw [integral_map Measurable.of_discrete.aemeasurable (by fun_prop)]
  rw [PMF.integral_eq_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hw : 0 ≤ bezierWeight n k α (x : ℝ) :=
    bezierWeight_nonneg n k (Nat.le_of_lt_succ k.isLt) hα x.property
  rw [bezierPMF_apply, ENNReal.toReal_ofReal hw]
  simp only [smul_eq_mul]

end VoronovskajaTypeFormula
