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

public import FormalConjectures.Paper.VoronovskajaDiscreteLaw
public import FormalConjecturesForMathlib.Probability.Distributions.PoweredBinomialTailIntegrability
public import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Expectations of powered standardized-binomial laws

This file converts the powered tail-integral limit into convergence of the actual first moments.
-/

public section

noncomputable section

open Topology Filter Real unitInterval Polynomial
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory Topology unitInterval

namespace VoronovskajaTypeFormula

private lemma setOf_lt_coe_toNNReal_eq_Ioi {t : ℝ} (ht : 0 < t) :
    {z : ℝ | t < (Real.toNNReal z : ℝ)} = Ioi t := by
  ext z
  simp only [Set.mem_setOf_eq, mem_Ioi]
  rw [Real.coe_toNNReal']
  constructor
  · intro h
    rcases lt_max_iff.mp h with h | h
    · exact h
    · exact (ht.not_lt h).elim
  · intro h
    exact h.trans_le (le_max_left z 0)

private lemma setOf_le_coe_toNNReal_neg_eq_Iic {t : ℝ} (ht : 0 < t) :
    {z : ℝ | t ≤ (Real.toNNReal (-z) : ℝ)} = Iic (-t) := by
  ext z
  simp only [Set.mem_setOf_eq, mem_Iic]
  rw [Real.coe_toNNReal']
  constructor
  · intro h
    rcases le_max_iff.mp h with h | h
    · linarith
    · exact (not_le_of_gt ht h).elim
  · intro h
    have h' : t ≤ -z := by linarith
    exact h'.trans (le_max_left (-z) 0)

/-- The identity is integrable against a standardized Bézier law because it is a map of a PMF on
`Fin (n + 1)`. -/
lemma integrable_id_standardizedBezierMeasure
    (n : ℕ) (α : ℝ) (hα : 0 < α) (x : I) :
    Integrable id (standardizedBezierMeasure n α hα x) := by
  rw [standardizedBezierMeasure, standardizedBezierPMF]
  rw [← PMF.toMeasure_map (p := bezierPMF n α hα x)
    (f := fun k : Fin (n + 1) => standardizeBinomial n x ((k : ℕ) : ℝ))
    Measurable.of_discrete]
  rw [integrable_map_measure (by fun_prop) Measurable.of_discrete.aemeasurable]
  exact .of_finite

/-- Exact finite-sum formula for the mean of a standardized Bézier law. -/
lemma integral_id_standardizedBezierMeasure_eq_sum
    (n : ℕ) (α : ℝ) (hα : 0 < α) (x : I) :
    (∫ z : ℝ, z ∂(standardizedBezierMeasure n α hα x)) =
      ∑ k : Fin (n + 1),
        bezierWeight n k α (x : ℝ) *
          standardizeBinomial n x ((k : ℕ) : ℝ) := by
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
  simp only [id_eq, smul_eq_mul]

lemma integrable_id_poweredStandardizedBinomial
    (n : ℕ) (α : ℝ) (hα : 0 < α) (x : I) :
    Integrable id
      (poweredStandardizedBinomialProbability n x α hα : Measure ℝ) := by
  rw [← standardizedBezierMeasure_eq_poweredStandardizedBinomial n α hα x]
  exact integrable_id_standardizedBezierMeasure n α hα x

/-- For positive `n`, the mean is the integral of the difference of the positive and negative tails. -/
lemma integral_id_poweredStandardizedBinomial_eq_tailDifference
    (n : ℕ) (hn : 0 < n)
    (x : I) (hx0 : 0 < (x : ℝ)) (hx1 : (x : ℝ) < 1)
    (α : ℝ) (hα : 0 < α) :
    (∫ z : ℝ, z
      ∂(poweredStandardizedBinomialProbability n x α hα : Measure ℝ)) =
      ∫ t in Ioi 0, poweredStandardizedBinomialTailDifference n x α hα t := by
  let μ : Measure ℝ :=
    (poweredStandardizedBinomialProbability n x α hα : Measure ℝ)
  have hid : Integrable id μ := by
    simpa [μ] using integrable_id_poweredStandardizedBinomial n α hα x
  have hright : Integrable (fun t : ℝ ↦ μ.real (Ioi t))
      (volume.restrict (Ioi 0)) := by
    simpa [μ] using
      integrable_poweredStandardizedBinomialRightTail n hn x hx0 hx1 α hα
  have hleft : Integrable (fun t : ℝ ↦ μ.real (Iic (-t)))
      (volume.restrict (Ioi 0)) := by
    simpa [μ] using
      integrable_poweredStandardizedBinomialLeftTail n hn x hx0 hx1 α hα
  have hposEq :
      (fun t : ℝ ↦ μ.real {z : ℝ | t < (Real.toNNReal z : ℝ)}) =ᵐ[
        volume.restrict (Ioi 0)]
      (fun t : ℝ ↦ μ.real (Ioi t)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact congrArg μ.real (setOf_lt_coe_toNNReal_eq_Ioi ht)
  have hnegEq :
      (fun t : ℝ ↦ μ.real {z : ℝ | t ≤ (Real.toNNReal (-z) : ℝ)}) =ᵐ[
        volume.restrict (Ioi 0)]
      (fun t : ℝ ↦ μ.real (Iic (-t))) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact congrArg μ.real (setOf_le_coe_toNNReal_neg_eq_Iic ht)
  calc
    (∫ z : ℝ, z ∂μ) =
        (∫ z : ℝ, (Real.toNNReal z : ℝ) ∂μ) -
          ∫ z : ℝ, (Real.toNNReal (-z) : ℝ) ∂μ := by
      simpa only [id_eq, Pi.neg_apply] using
        (integral_eq_integral_pos_part_sub_integral_neg_part hid)
    _ =
        (∫ t in Ioi 0, μ.real {z : ℝ | t < (Real.toNNReal z : ℝ)}) -
          ∫ t in Ioi 0, μ.real {z : ℝ | t ≤ (Real.toNNReal (-z) : ℝ)} := by
      rw [(hid.real_toNNReal).integral_eq_integral_meas_lt
          (Eventually.of_forall fun z ↦ by positivity)]
      rw [(hid.neg.real_toNNReal).integral_eq_integral_meas_le
          (Eventually.of_forall fun z ↦ by positivity)]
    _ = (∫ t in Ioi 0, μ.real (Ioi t)) -
          ∫ t in Ioi 0, μ.real (Iic (-t)) := by
      rw [integral_congr_ae hposEq, integral_congr_ae hnegEq]
    _ = ∫ t in Ioi 0, μ.real (Ioi t) - μ.real (Iic (-t)) := by
      rw [integral_sub hright hleft]
    _ = ∫ t in Ioi 0, poweredStandardizedBinomialTailDifference n x α hα t := by
      apply integral_congr_ae
      filter_upwards with t
      rfl

/-- The actual powered standardized-binomial means converge to the explicit Gaussian constant. -/
lemma tendsto_integral_id_poweredStandardizedBinomial
    (x : I) (hx0 : 0 < (x : ℝ)) (hx1 : (x : ℝ) < 1)
    (α : ℝ) (hα : 0 < α) :
    Tendsto
      (fun n : ℕ ↦ ∫ z : ℝ, z
        ∂(poweredStandardizedBinomialProbability n x α hα : Measure ℝ))
      atTop (𝓝 (poweredGaussianFirstMomentConstant α)) := by
  have htail :=
    tendsto_integral_poweredStandardizedBinomialTailDifference x hx0 hx1 α hα
  refine htail.congr' ?_
  filter_upwards [eventually_atTop.2 ⟨1, fun n hn ↦ hn⟩] with n hn
  exact (integral_id_poweredStandardizedBinomial_eq_tailDifference
    n hn x hx0 hx1 α hα).symm

end VoronovskajaTypeFormula
