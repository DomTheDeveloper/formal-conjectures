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

public import FormalConjecturesForMathlib.Probability.Distributions.PoweredBinomialTails
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Scaled second moments of powered standardized-binomial laws

The event `t < z^2` is contained in the union of the right tail beyond `sqrt t` and the left tail
beyond `-sqrt t`.  The powered sub-Gaussian estimates therefore give an exponential integrable
envelope in the layer-cake variable `t`.  Dominated convergence then shows that the second-moment
tail integral divided by `sqrt n` tends to zero.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped Topology unitInterval

namespace ProbabilityTheory

/-- The layer-cake tail function for the second moment of a powered standardized-binomial law. -/
@[expose]
noncomputable def poweredStandardizedBinomialSecondMomentTail
    (n : ℕ) (p : I) (α : ℝ) (hα : 0 < α) (t : ℝ) : ℝ :=
  (poweredStandardizedBinomialProbability n p α hα : Measure ℝ).real
    {z : ℝ | t < z ^ 2}

private lemma measurable_poweredStandardizedBinomialSecondMomentTail
    (n : ℕ) (p : I) (α : ℝ) (hα : 0 < α) :
    Measurable (poweredStandardizedBinomialSecondMomentTail n p α hα) := by
  apply Antitone.measurable
  intro a b hab
  exact measureReal_mono fun z hz ↦ hab.trans_lt hz

private lemma standardizedBernoulliSubgaussianParameter_pos_second
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

private lemma secondMoment_event_subset_tails {t z : ℝ} (ht : 0 ≤ t) (hz : t < z ^ 2) :
    z ∈ Ioi (Real.sqrt t) ∪ Iic (-Real.sqrt t) := by
  by_cases hright : Real.sqrt t < z
  · exact Or.inl hright
  · by_cases hleft : z ≤ -Real.sqrt t
    · exact Or.inr hleft
    · have hzle : z ≤ Real.sqrt t := le_of_not_gt hright
      have hleft' : -Real.sqrt t < z := lt_of_not_ge hleft
      have hsquare : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht
      exfalso
      nlinarith

private lemma secondMomentTail_le_add_tails
    (n : ℕ) (p : I) (α : ℝ) (hα : 0 < α) (t : ℝ) (ht : 0 ≤ t) :
    poweredStandardizedBinomialSecondMomentTail n p α hα t ≤
      (poweredStandardizedBinomialProbability n p α hα : Measure ℝ).real
          (Ioi (Real.sqrt t)) +
        (poweredStandardizedBinomialProbability n p α hα : Measure ℝ).real
          (Iic (-Real.sqrt t)) := by
  calc
    poweredStandardizedBinomialSecondMomentTail n p α hα t ≤
        (poweredStandardizedBinomialProbability n p α hα : Measure ℝ).real
          (Ioi (Real.sqrt t) ∪ Iic (-Real.sqrt t)) :=
      measureReal_mono fun z hz ↦ secondMoment_event_subset_tails ht hz
    _ ≤ _ := measureReal_union_le _ _

private lemma exp_rpow_secondTail_eq
    {c α t : ℝ} (hc : c ≠ 0) :
    (exp (-t / (2 * c))) ^ α = exp (-(α / (2 * c)) * t) := by
  rw [← Real.exp_mul]
  congr 1
  field_simp [hc]

private lemma integrableOn_exp_neg_mul_linear {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t : ℝ ↦ exp (-b * t)) (Ioi 0) := by
  simpa using
    (integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (0 : ℝ)) (b := b)
      (by norm_num) (by norm_num) hb)

private lemma secondMomentTail_le_exp_of_alpha_le_one
    (n : ℕ) (hn : 0 < n)
    (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (t : ℝ) (ht : 0 ≤ t) :
    poweredStandardizedBinomialSecondMomentTail n p α hα t ≤
      2 * exp (-(α / (2 * (standardizedBernoulliSubgaussianParameter p : ℝ))) * t) := by
  let c : ℝ := standardizedBernoulliSubgaussianParameter p
  have hc : 0 < c := standardizedBernoulliSubgaussianParameter_pos_second p hp0 hp1
  have hc0 : c ≠ 0 := hc.ne'
  have hright :=
    measureReal_Ioi_poweredStandardizedBinomialProbability_le_exp_rpow
      n hn p hp0 hp1 α hα (Real.sqrt t) (Real.sqrt_nonneg t)
  have hleft :=
    measureReal_Iic_poweredStandardizedBinomialProbability_le_exp_rpow
      n hn p hp0 hp1 α hα hα1 (Real.sqrt t) (Real.sqrt_nonneg t)
  have hsquare : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht
  have heq :
      (exp (-t / (2 * c))) ^ α = exp (-(α / (2 * c)) * t) :=
    exp_rpow_secondTail_eq hc0
  calc
    poweredStandardizedBinomialSecondMomentTail n p α hα t ≤
        (poweredStandardizedBinomialProbability n p α hα : Measure ℝ).real
            (Ioi (Real.sqrt t)) +
          (poweredStandardizedBinomialProbability n p α hα : Measure ℝ).real
            (Iic (-Real.sqrt t)) :=
      secondMomentTail_le_add_tails n p α hα t ht
    _ ≤ (exp (-t / (2 * c))) ^ α + (exp (-t / (2 * c))) ^ α := by
      simpa [c, hsquare] using add_le_add hright hleft
    _ = 2 * exp (-(α / (2 * c)) * t) := by rw [heq]; ring
    _ = 2 * exp (-(α / (2 * (standardizedBernoulliSubgaussianParameter p : ℝ))) * t) := by
      rfl

private lemma secondMomentTail_le_exp_of_one_le_alpha
    (n : ℕ) (hn : 0 < n)
    (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (α : ℝ) (hα : 0 < α) (h1α : 1 ≤ α)
    (t : ℝ) (ht : 0 ≤ t) :
    poweredStandardizedBinomialSecondMomentTail n p α hα t ≤
      (1 + α) * exp (-(1 / (2 * (standardizedBernoulliSubgaussianParameter p : ℝ))) * t) := by
  let c : ℝ := standardizedBernoulliSubgaussianParameter p
  have hc : 0 < c := standardizedBernoulliSubgaussianParameter_pos_second p hp0 hp1
  have hright0 :=
    measureReal_Ioi_poweredStandardizedBinomialProbability_le_exp_rpow
      n hn p hp0 hp1 α hα (Real.sqrt t) (Real.sqrt_nonneg t)
  have hleft :=
    measureReal_Iic_poweredStandardizedBinomialProbability_le_mul_exp
      n hn p hp0 hp1 α hα h1α (Real.sqrt t) (Real.sqrt_nonneg t)
  have hsquare : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht
  let q : ℝ := exp (-t / (2 * c))
  have hq0 : 0 ≤ q := exp_nonneg _
  have hq1 : q ≤ 1 := by
    dsimp [q]
    exact exp_le_one_iff.mpr (by
      have hfrac : 0 ≤ t / (2 * c) := by positivity
      simpa [neg_div] using neg_nonpos.mpr hfrac)
  have hright :
      (poweredStandardizedBinomialProbability n p α hα : Measure ℝ).real
          (Ioi (Real.sqrt t)) ≤ q := by
    have hright0' :
        (poweredStandardizedBinomialProbability n p α hα : Measure ℝ).real
            (Ioi (Real.sqrt t)) ≤ q ^ α := by
      simpa [q, c, hsquare] using hright0
    exact hright0'.trans (Real.rpow_le_self_of_le_one hq0 hq1 h1α)
  calc
    poweredStandardizedBinomialSecondMomentTail n p α hα t ≤
        (poweredStandardizedBinomialProbability n p α hα : Measure ℝ).real
            (Ioi (Real.sqrt t)) +
          (poweredStandardizedBinomialProbability n p α hα : Measure ℝ).real
            (Iic (-Real.sqrt t)) :=
      secondMomentTail_le_add_tails n p α hα t ht
    _ ≤ q + α * q := add_le_add hright (by simpa [q, c, hsquare] using hleft)
    _ = (1 + α) * exp (-(1 / (2 * c)) * t) := by dsimp [q]; ring_nf
    _ = (1 + α) *
        exp (-(1 / (2 * (standardizedBernoulliSubgaussianParameter p : ℝ))) * t) := by
      rfl

/-- The layer-cake second-moment integral, divided by `sqrt n`, tends to zero. -/
lemma tendsto_inv_sqrt_mul_integral_poweredStandardizedBinomialSecondMomentTail
    (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (α : ℝ) (hα : 0 < α) :
    Tendsto
      (fun n : ℕ ↦ ∫ t in Ioi 0,
        (Real.sqrt n)⁻¹ * poweredStandardizedBinomialSecondMomentTail n p α hα t)
      atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ ↦ (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hpoint (t : ℝ) : Tendsto
      (fun n : ℕ ↦ (Real.sqrt n)⁻¹ *
        poweredStandardizedBinomialSecondMomentTail n p α hα t)
      atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun n ↦
        mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg n)) measureReal_nonneg
    · exact Eventually.of_forall fun n ↦ by
        calc
          (Real.sqrt n)⁻¹ * poweredStandardizedBinomialSecondMomentTail n p α hα t ≤
              (Real.sqrt n)⁻¹ * 1 := by
                gcongr
                exact measureReal_le_one
          _ = (Real.sqrt n)⁻¹ := mul_one _
    · exact hinv
  rcases le_total α 1 with hα1 | h1α
  · let b : ℝ := α / (2 * (standardizedBernoulliSubgaussianParameter p : ℝ))
    have hc : 0 < (standardizedBernoulliSubgaussianParameter p : ℝ) :=
      standardizedBernoulliSubgaussianParameter_pos_second p hp0 hp1
    have hb : 0 < b := div_pos hα (mul_pos two_pos hc)
    let g : ℝ → ℝ := fun t ↦ 2 * exp (-b * t)
    have hg : Integrable g (volume.restrict (Ioi 0)) := by
      simpa [g] using (integrableOn_exp_neg_mul_linear hb).const_mul 2
    have hmeas : ∀ᶠ n : ℕ in atTop,
        AEStronglyMeasurable
          (fun t : ℝ ↦ (Real.sqrt n)⁻¹ *
            poweredStandardizedBinomialSecondMomentTail n p α hα t)
          (volume.restrict (Ioi 0)) :=
      Eventually.of_forall fun n ↦
        ((measurable_const.mul
          (measurable_poweredStandardizedBinomialSecondMomentTail n p α hα))).aestronglyMeasurable
    have hbound : ∀ᶠ n : ℕ in atTop, ∀ᵐ t ∂volume.restrict (Ioi 0),
        ‖(Real.sqrt n)⁻¹ * poweredStandardizedBinomialSecondMomentTail n p α hα t‖ ≤ g t := by
      refine eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      have hn0 : 0 < n := hn
      have ht0 : 0 ≤ t := le_of_lt ht
      have hsqrt_one : 1 ≤ Real.sqrt (n : ℝ) := by
        rw [← Real.sqrt_one]
        gcongr
        exact_mod_cast hn
      have hinv_one : (Real.sqrt (n : ℝ))⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ hsqrt_one
      have hprod0 : 0 ≤ (Real.sqrt n)⁻¹ *
          poweredStandardizedBinomialSecondMomentTail n p α hα t :=
        mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg n)) measureReal_nonneg
      rw [Real.norm_eq_abs, abs_of_nonneg hprod0]
      calc
        (Real.sqrt n)⁻¹ * poweredStandardizedBinomialSecondMomentTail n p α hα t ≤
            poweredStandardizedBinomialSecondMomentTail n p α hα t := by
          have htail0 : 0 ≤ poweredStandardizedBinomialSecondMomentTail n p α hα t :=
            measureReal_nonneg
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hinv_one htail0
        _ ≤ 2 * exp (-b * t) := by
          simpa [b] using
            secondMomentTail_le_exp_of_alpha_le_one
              n hn0 p hp0 hp1 α hα hα1 t ht0
        _ = g t := rfl
    have hlim : ∀ᵐ t ∂volume.restrict (Ioi 0), Tendsto
        (fun n : ℕ ↦ (Real.sqrt n)⁻¹ *
          poweredStandardizedBinomialSecondMomentTail n p α hα t)
        atTop (𝓝 0) := ae_of_all _ hpoint
    simpa using
      (tendsto_integral_filter_of_dominated_convergence
        (l := atTop)
        (F := fun n : ℕ ↦ fun t : ℝ ↦ (Real.sqrt n)⁻¹ *
          poweredStandardizedBinomialSecondMomentTail n p α hα t)
        (f := fun _ : ℝ ↦ 0)
        (μ := volume.restrict (Ioi 0))
        g hmeas hbound hg hlim)
  · let b : ℝ := 1 / (2 * (standardizedBernoulliSubgaussianParameter p : ℝ))
    have hc : 0 < (standardizedBernoulliSubgaussianParameter p : ℝ) :=
      standardizedBernoulliSubgaussianParameter_pos_second p hp0 hp1
    have hb : 0 < b := one_div_pos.mpr (mul_pos two_pos hc)
    let g : ℝ → ℝ := fun t ↦ (1 + α) * exp (-b * t)
    have hg : Integrable g (volume.restrict (Ioi 0)) := by
      simpa [g] using (integrableOn_exp_neg_mul_linear hb).const_mul (1 + α)
    have hmeas : ∀ᶠ n : ℕ in atTop,
        AEStronglyMeasurable
          (fun t : ℝ ↦ (Real.sqrt n)⁻¹ *
            poweredStandardizedBinomialSecondMomentTail n p α hα t)
          (volume.restrict (Ioi 0)) :=
      Eventually.of_forall fun n ↦
        ((measurable_const.mul
          (measurable_poweredStandardizedBinomialSecondMomentTail n p α hα))).aestronglyMeasurable
    have hbound : ∀ᶠ n : ℕ in atTop, ∀ᵐ t ∂volume.restrict (Ioi 0),
        ‖(Real.sqrt n)⁻¹ * poweredStandardizedBinomialSecondMomentTail n p α hα t‖ ≤ g t := by
      refine eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      have hn0 : 0 < n := hn
      have ht0 : 0 ≤ t := le_of_lt ht
      have hsqrt_one : 1 ≤ Real.sqrt (n : ℝ) := by
        rw [← Real.sqrt_one]
        gcongr
        exact_mod_cast hn
      have hinv_one : (Real.sqrt (n : ℝ))⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ hsqrt_one
      have hprod0 : 0 ≤ (Real.sqrt n)⁻¹ *
          poweredStandardizedBinomialSecondMomentTail n p α hα t :=
        mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg n)) measureReal_nonneg
      rw [Real.norm_eq_abs, abs_of_nonneg hprod0]
      calc
        (Real.sqrt n)⁻¹ * poweredStandardizedBinomialSecondMomentTail n p α hα t ≤
            poweredStandardizedBinomialSecondMomentTail n p α hα t := by
          have htail0 : 0 ≤ poweredStandardizedBinomialSecondMomentTail n p α hα t :=
            measureReal_nonneg
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hinv_one htail0
        _ ≤ (1 + α) * exp (-b * t) := by
          simpa [b] using
            secondMomentTail_le_exp_of_one_le_alpha
              n hn0 p hp0 hp1 α hα h1α t ht0
        _ = g t := rfl
    have hlim : ∀ᵐ t ∂volume.restrict (Ioi 0), Tendsto
        (fun n : ℕ ↦ (Real.sqrt n)⁻¹ *
          poweredStandardizedBinomialSecondMomentTail n p α hα t)
        atTop (𝓝 0) := ae_of_all _ hpoint
    simpa using
      (tendsto_integral_filter_of_dominated_convergence
        (l := atTop)
        (F := fun n : ℕ ↦ fun t : ℝ ↦ (Real.sqrt n)⁻¹ *
          poweredStandardizedBinomialSecondMomentTail n p α hα t)
        (f := fun _ : ℝ ↦ 0)
        (μ := volume.restrict (Ioi 0))
        g hmeas hbound hg hlim)

end ProbabilityTheory
