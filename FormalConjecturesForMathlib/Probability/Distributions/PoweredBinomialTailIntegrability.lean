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

public import FormalConjecturesForMathlib.Probability.Distributions.PoweredBinomialMoments

/-!
# Integrability of powered standardized-binomial tails

The first-moment layer-cake formula needs the positive and negative tail functions to be integrable
separately.  The uniform sub-Gaussian estimates prove this directly.  Keeping these facts as named
lemmas makes the subsequent identification of the tail integral with the actual expectation small
and reusable.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped Topology unitInterval

namespace ProbabilityTheory

private lemma measurable_poweredRightTail
    (n : ℕ) (p : I) (α : ℝ) (hα : 0 < α) :
    Measurable (fun t : ℝ ↦
      (poweredStandardizedBinomialProbability n p α hα : Measure ℝ).real (Ioi t)) := by
  apply Antitone.measurable
  intro a b hab
  exact measureReal_mono fun z hz ↦ hab.trans_lt hz

private lemma measurable_poweredLeftTail
    (n : ℕ) (p : I) (α : ℝ) (hα : 0 < α) :
    Measurable (fun t : ℝ ↦
      (poweredStandardizedBinomialProbability n p α hα : Measure ℝ).real (Iic (-t))) := by
  apply Antitone.measurable
  intro a b hab
  exact measureReal_mono fun z hz ↦ hz.trans (neg_le_neg hab)

private lemma standardizedBernoulliSubgaussianParameter_pos'
    (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    0 < (standardizedBernoulliSubgaussianParameter p : ℝ) := by
  have hs : 0 < bernoulliStdDev p := bernoulliStdDev_pos p hp0 hp1
  have hwidth :
      ((1 - (p : ℝ)) / bernoulliStdDev p) -
          (-(p : ℝ) / bernoulliStdDev p) =
        1 / bernoulliStdDev p := by
    field_simp [hs.ne']
    ring
  rw [standardizedBernoulliSubgaussianParameter]
  simp only [hwidth]
  have hinv : 0 < 1 / bernoulliStdDev p := one_div_pos.mpr hs
  have hnormNN : 0 < ‖(1 / bernoulliStdDev p : ℝ)‖₊ := by
    exact_mod_cast (norm_pos_iff.mpr (one_div_ne_zero (ne_of_gt hs)))
  positivity

private lemma exp_rpow_tail_eq'
    {c α t : ℝ} (hc : c ≠ 0) :
    (exp (-t ^ 2 / (2 * c))) ^ α =
      exp (-(α / (2 * c)) * t ^ 2) := by
  rw [← Real.exp_mul]
  congr 1
  field_simp [hc]

/-- The right-tail function of a powered standardized-binomial law is integrable on the positive
half-line. -/
lemma integrable_poweredStandardizedBinomialRightTail
    (n : ℕ) (hn : 0 < n)
    (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (α : ℝ) (hα : 0 < α) :
    Integrable
      (fun t : ℝ ↦
        (poweredStandardizedBinomialProbability n p α hα : Measure ℝ).real (Ioi t))
      (volume.restrict (Ioi 0)) := by
  let c : ℝ := standardizedBernoulliSubgaussianParameter p
  have hc : 0 < c := standardizedBernoulliSubgaussianParameter_pos' p hp0 hp1
  have hc0 : c ≠ 0 := hc.ne'
  let b : ℝ := α / (2 * c)
  have hb : 0 < b := div_pos hα (mul_pos two_pos hc)
  let g : ℝ → ℝ := fun t ↦ exp (-b * t ^ 2)
  have hg : Integrable g (volume.restrict (Ioi 0)) := by
    exact (integrable_exp_neg_mul_sq hb).integrableOn
  refine hg.mono' (measurable_poweredRightTail n p α hα).aestronglyMeasurable ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  have ht0 : 0 ≤ t := le_of_lt ht
  have htail :=
    measureReal_Ioi_poweredStandardizedBinomialProbability_le_exp_rpow
      n hn p hp0 hp1 α hα t ht0
  have htail' :
      (poweredStandardizedBinomialProbability n p α hα : Measure ℝ).real (Ioi t) ≤
        (exp (-t ^ 2 / (2 * c))) ^ α := by
    simpa [c] using htail
  have heq : (exp (-t ^ 2 / (2 * c))) ^ α = exp (-b * t ^ 2) := by
    simpa [b] using exp_rpow_tail_eq' (α := α) (t := t) hc0
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact htail'.trans_eq heq

/-- The left-tail function of a powered standardized-binomial law is integrable on the positive
half-line. -/
lemma integrable_poweredStandardizedBinomialLeftTail
    (n : ℕ) (hn : 0 < n)
    (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (α : ℝ) (hα : 0 < α) :
    Integrable
      (fun t : ℝ ↦
        (poweredStandardizedBinomialProbability n p α hα : Measure ℝ).real (Iic (-t)))
      (volume.restrict (Ioi 0)) := by
  let c : ℝ := standardizedBernoulliSubgaussianParameter p
  have hc : 0 < c := standardizedBernoulliSubgaussianParameter_pos' p hp0 hp1
  have hc0 : c ≠ 0 := hc.ne'
  rcases le_total α 1 with hα1 | h1α
  · let b : ℝ := α / (2 * c)
    have hb : 0 < b := div_pos hα (mul_pos two_pos hc)
    let g : ℝ → ℝ := fun t ↦ exp (-b * t ^ 2)
    have hg : Integrable g (volume.restrict (Ioi 0)) := by
      exact (integrable_exp_neg_mul_sq hb).integrableOn
    refine hg.mono' (measurable_poweredLeftTail n p α hα).aestronglyMeasurable ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := le_of_lt ht
    have htail :=
      measureReal_Iic_poweredStandardizedBinomialProbability_le_exp_rpow
        n hn p hp0 hp1 α hα hα1 t ht0
    have htail' :
        (poweredStandardizedBinomialProbability n p α hα : Measure ℝ).real (Iic (-t)) ≤
          (exp (-t ^ 2 / (2 * c))) ^ α := by
      simpa [c] using htail
    have heq : (exp (-t ^ 2 / (2 * c))) ^ α = exp (-b * t ^ 2) := by
      simpa [b] using exp_rpow_tail_eq' (α := α) (t := t) hc0
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact htail'.trans_eq heq
  · let b : ℝ := 1 / (2 * c)
    have hb : 0 < b := one_div_pos.mpr (mul_pos two_pos hc)
    let g : ℝ → ℝ := fun t ↦ α * exp (-b * t ^ 2)
    have hg : Integrable g (volume.restrict (Ioi 0)) := by
      exact ((integrable_exp_neg_mul_sq hb).const_mul α).integrableOn
    refine hg.mono' (measurable_poweredLeftTail n p α hα).aestronglyMeasurable ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := le_of_lt ht
    have htail :=
      measureReal_Iic_poweredStandardizedBinomialProbability_le_mul_exp
        n hn p hp0 hp1 α hα h1α t ht0
    have htail' :
        (poweredStandardizedBinomialProbability n p α hα : Measure ℝ).real (Iic (-t)) ≤
          α * exp (-t ^ 2 / (2 * c)) := by
      simpa [c] using htail
    have heq : exp (-t ^ 2 / (2 * c)) = exp (-b * t ^ 2) := by
      congr 1
      dsimp [b]
      field_simp [hc0]
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact htail'.trans_eq (by rw [heq])

/-- The signed tail-difference integrand used in the powered first-moment limit is integrable. -/
lemma integrable_poweredStandardizedBinomialTailDifference
    (n : ℕ) (hn : 0 < n)
    (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (α : ℝ) (hα : 0 < α) :
    Integrable (poweredStandardizedBinomialTailDifference n p α hα)
      (volume.restrict (Ioi 0)) := by
  simpa [poweredStandardizedBinomialTailDifference] using
    (integrable_poweredStandardizedBinomialRightTail n hn p hp0 hp1 α hα).sub
      (integrable_poweredStandardizedBinomialLeftTail n hn p hp0 hp1 α hα)

end ProbabilityTheory
