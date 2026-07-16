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
public import FormalConjecturesForMathlib.Probability.Distributions.PoweredBinomialTails
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# First moments of powered binomial laws

Weak convergence alone does not control the unbounded identity function.  This file first records
convergence of clipped identities, and then proves the exact untruncated first-moment limit by the
tail-probability formula and dominated convergence.  The domination is supplied by the uniform
sub-Gaussian tail estimates from `PoweredBinomialTails`.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped Topology unitInterval BoundedContinuousFunction

namespace ProbabilityTheory

/-- The identity on `[-R,R]`, clipped to stay in that interval outside it. -/
@[expose]
noncomputable def clippedIdentity (R : ℝ) (hR : 0 ≤ R) : ℝ →ᵇ ℝ where
  toFun z := max (-R) (min z R)
  continuous_toFun := continuous_const.max (continuous_id.min continuous_const)
  map_bounded' := by
    refine ⟨2 * R, fun x y ↦ ?_⟩
    rw [Real.dist_eq, abs_le]
    have hxlo : -R ≤ max (-R) (min x R) := le_max_left _ _
    have hylo : -R ≤ max (-R) (min y R) := le_max_left _ _
    have hxhi : max (-R) (min x R) ≤ R := by
      exact max_le (by linarith) (min_le_right _ _)
    have hyhi : max (-R) (min y R) ≤ R := by
      exact max_le (by linarith) (min_le_right _ _)
    constructor <;> linarith

@[simp]
lemma clippedIdentity_apply (R : ℝ) (hR : 0 ≤ R) (z : ℝ) :
    clippedIdentity R hR z = max (-R) (min z R) := rfl

lemma clippedIdentity_eq_self {R z : ℝ} (hR : 0 ≤ R) (hz : z ∈ Icc (-R) R) :
    clippedIdentity R hR z = z := by
  simp [clippedIdentity, hz.1, hz.2]

lemma abs_clippedIdentity_le (R : ℝ) (hR : 0 ≤ R) (z : ℝ) :
    |clippedIdentity R hR z| ≤ R := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

/-- Every fixed clipped first moment of the powered standardized binomial law converges to the
corresponding clipped moment of the powered Gaussian law. -/
lemma tendsto_integral_clippedIdentity_poweredStandardizedBinomial
    (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (α : ℝ) (hα : 0 < α) (R : ℝ) (hR : 0 ≤ R) :
    Tendsto
      (fun n ↦ ∫ z, clippedIdentity R hR z
        ∂(poweredStandardizedBinomialProbability n p α hα : Measure ℝ))
      atTop
      (𝓝 (∫ z, clippedIdentity R hR z
        ∂(poweredGaussianProbability α hα : Measure ℝ))) := by
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (tendsto_poweredStandardizedBinomialProbability p hp0 hp1 α hα))
    (clippedIdentity R hR)

/-- The exact first-moment constant of the powered Gaussian limit law, written as the difference of
its positive and negative tail integrals. -/
@[expose]
noncomputable def poweredGaussianFirstMomentConstant (α : ℝ) : ℝ :=
  ∫ t in Ioi 0,
    (1 - cdf (gaussianReal 0 1) t) ^ α +
      cdf (gaussianReal 0 1) t ^ α - 1

/-- The tail-difference integrand whose integral is the mean of an integrable real law. -/
@[expose]
noncomputable def poweredStandardizedBinomialTailDifference
    (n : ℕ) (p : I) (α : ℝ) (hα : 0 < α) (t : ℝ) : ℝ :=
  (poweredStandardizedBinomialProbability n p α hα : Measure ℝ).real (Ioi t) -
    (poweredStandardizedBinomialProbability n p α hα : Measure ℝ).real (Iic (-t))

private lemma measurable_measureReal_Ioi (μ : Measure ℝ) :
    Measurable (fun t : ℝ ↦ μ.real (Ioi t)) := by
  apply Antitone.measurable
  intro a b hab
  exact measureReal_mono fun z hz ↦ hab.trans_lt hz

private lemma measurable_measureReal_Iic_neg (μ : Measure ℝ) :
    Measurable (fun t : ℝ ↦ μ.real (Iic (-t))) := by
  apply Antitone.measurable
  intro a b hab
  exact measureReal_mono fun z hz ↦ hz.trans (neg_le_neg hab)

private lemma measurable_poweredStandardizedBinomialTailDifference
    (n : ℕ) (p : I) (α : ℝ) (hα : 0 < α) :
    Measurable (poweredStandardizedBinomialTailDifference n p α hα) := by
  exact (measurable_measureReal_Ioi _).sub (measurable_measureReal_Iic_neg _)

private lemma standardizedBernoulliSubgaussianParameter_pos
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
  positivity

private lemma tendsto_poweredStandardizedBinomialTailDifference
    (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (α : ℝ) (hα : 0 < α) (t : ℝ) :
    Tendsto
      (fun n ↦ poweredStandardizedBinomialTailDifference n p α hα t)
      atTop
      (𝓝 ((1 - cdf (gaussianReal 0 1) t) ^ α +
        cdf (gaussianReal 0 1) t ^ α - 1)) := by
  have hcdfRight := tendsto_cdf_standardizedBinomialProbability p hp0 hp1 t
  have hright : Tendsto
      (fun n ↦
        (poweredStandardizedBinomialProbability n p α hα : Measure ℝ).real (Ioi t))
      atTop (𝓝 ((1 - cdf (gaussianReal 0 1) t) ^ α)) := by
    have hbase : Tendsto
        (fun n ↦ 1 - cdf (standardizedBinomialMeasure n p) t)
        atTop (𝓝 (1 - cdf (gaussianReal 0 1) t)) :=
      tendsto_const_nhds.sub hcdfRight
    have hpow := hbase.rpow_const (.inr hα.le)
    simpa only [measureReal_Ioi_poweredStandardizedBinomialProbability] using hpow
  have hcdfLeft := tendsto_cdf_standardizedBinomialProbability p hp0 hp1 (-t)
  have hleft : Tendsto
      (fun n ↦
        (poweredStandardizedBinomialProbability n p α hα : Measure ℝ).real (Iic (-t)))
      atTop (𝓝 (1 - cdf (gaussianReal 0 1) t ^ α)) := by
    have hbase : Tendsto
        (fun n ↦ 1 - cdf (standardizedBinomialMeasure n p) (-t))
        atTop (𝓝 (1 - cdf (gaussianReal 0 1) (-t))) :=
      tendsto_const_nhds.sub hcdfLeft
    have hpow := hbase.rpow_const (.inr hα.le)
    have hfinal := tendsto_const_nhds.sub hpow
    simpa only [measureReal_Iic_poweredStandardizedBinomialProbability,
      cdf_gaussianReal_zero_one_neg, sub_sub_cancel] using hfinal
  change Tendsto
    (fun n ↦
      (poweredStandardizedBinomialProbability n p α hα : Measure ℝ).real (Ioi t) -
        (poweredStandardizedBinomialProbability n p α hα : Measure ℝ).real (Iic (-t)))
    atTop _
  convert hright.sub hleft using 1 <;> ring

private lemma exp_rpow_tail_eq
    {c α t : ℝ} (hc : c ≠ 0) :
    (exp (-t ^ 2 / (2 * c))) ^ α =
      exp (-(α / (2 * c)) * t ^ 2) := by
  rw [← Real.exp_mul]
  congr 1
  field_simp [hc]
  ring

/-- The integrated difference of the powered right and left tails converges to the exact powered
Gaussian first-moment constant.  This is the uniform-integrability step missing from weak
convergence alone. -/
lemma tendsto_integral_poweredStandardizedBinomialTailDifference
    (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (α : ℝ) (hα : 0 < α) :
    Tendsto
      (fun n ↦ ∫ t in Ioi 0,
        poweredStandardizedBinomialTailDifference n p α hα t)
      atTop (𝓝 (poweredGaussianFirstMomentConstant α)) := by
  let c : ℝ := standardizedBernoulliSubgaussianParameter p
  have hc : 0 < c := standardizedBernoulliSubgaussianParameter_pos p hp0 hp1
  have hc0 : c ≠ 0 := hc.ne'
  rcases le_total α 1 with hα1 | h1α
  · let b : ℝ := α / (2 * c)
    have hb : 0 < b := div_pos hα (mul_pos two_pos hc)
    let g : ℝ → ℝ := fun t ↦ 2 * exp (-b * t ^ 2)
    have hg : Integrable g (volume.restrict (Ioi 0)) := by
      exact ((integrable_exp_neg_mul_sq hb).const_mul 2).integrableOn
    refine tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict (Ioi 0)) g ?_ ?_ hg ?_
    · exact Eventually.of_forall fun n ↦
        (measurable_poweredStandardizedBinomialTailDifference n p α hα).aestronglyMeasurable
    · refine eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      have hn0 : 0 < n := by omega
      have ht0 : 0 ≤ t := le_of_lt ht
      have hright :=
        measureReal_Ioi_poweredStandardizedBinomialProbability_le_exp_rpow
          n hn0 p hp0 hp1 α hα t ht0
      have hleft :=
        measureReal_Iic_poweredStandardizedBinomialProbability_le_exp_rpow
          n hn0 p hp0 hp1 α hα hα1 t ht0
      have heq :
          (exp (-t ^ 2 / (2 * c))) ^ α = exp (-b * t ^ 2) := by
        simpa [b, c] using exp_rpow_tail_eq (α := α) (t := t) hc0
      rw [Real.norm_eq_abs]
      calc
        |poweredStandardizedBinomialTailDifference n p α hα t| ≤
            (poweredStandardizedBinomialProbability n p α hα : Measure ℝ).real (Ioi t) +
              (poweredStandardizedBinomialProbability n p α hα : Measure ℝ).real (Iic (-t)) := by
                rw [poweredStandardizedBinomialTailDifference]
                exact abs_sub_le _ _
        _ ≤ (exp (-t ^ 2 / (2 * c))) ^ α +
              (exp (-t ^ 2 / (2 * c))) ^ α := add_le_add hright hleft
        _ = g t := by rw [heq]; simp [g]
    · filter_upwards with t
      exact tendsto_poweredStandardizedBinomialTailDifference p hp0 hp1 α hα t
  · let b : ℝ := 1 / (2 * c)
    have hb : 0 < b := one_div_pos.mpr (mul_pos two_pos hc)
    let g : ℝ → ℝ := fun t ↦ (1 + α) * exp (-b * t ^ 2)
    have hg : Integrable g (volume.restrict (Ioi 0)) := by
      exact ((integrable_exp_neg_mul_sq hb).const_mul (1 + α)).integrableOn
    refine tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict (Ioi 0)) g ?_ ?_ hg ?_
    · exact Eventually.of_forall fun n ↦
        (measurable_poweredStandardizedBinomialTailDifference n p α hα).aestronglyMeasurable
    · refine eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      have hn0 : 0 < n := by omega
      have ht0 : 0 ≤ t := le_of_lt ht
      let q : ℝ := exp (-t ^ 2 / (2 * c))
      have hq0 : 0 ≤ q := exp_nonneg _
      have hq1 : q ≤ 1 := by
        rw [q, exp_le_one_iff]
        positivity
      have hright0 :=
        measureReal_Ioi_poweredStandardizedBinomialProbability_le_exp_rpow
          n hn0 p hp0 hp1 α hα t ht0
      have hright :
          (poweredStandardizedBinomialProbability n p α hα : Measure ℝ).real (Ioi t) ≤ q :=
        hright0.trans (Real.rpow_le_self_of_le_one hq0 hq1 h1α)
      have hleft :=
        measureReal_Iic_poweredStandardizedBinomialProbability_le_mul_exp
          n hn0 p hp0 hp1 α hα h1α t ht0
      have heq : exp (-t ^ 2 / (2 * c)) = exp (-b * t ^ 2) := by
        congr 1
        field_simp [hc0]
        ring
      rw [Real.norm_eq_abs]
      calc
        |poweredStandardizedBinomialTailDifference n p α hα t| ≤
            (poweredStandardizedBinomialProbability n p α hα : Measure ℝ).real (Ioi t) +
              (poweredStandardizedBinomialProbability n p α hα : Measure ℝ).real (Iic (-t)) := by
                rw [poweredStandardizedBinomialTailDifference]
                exact abs_sub_le _ _
        _ ≤ q + α * q := add_le_add hright (by simpa [q] using hleft)
        _ = g t := by rw [q, heq]; simp [g]; ring
    · filter_upwards with t
      exact tendsto_poweredStandardizedBinomialTailDifference p hp0 hp1 α hα t

end ProbabilityTheory
