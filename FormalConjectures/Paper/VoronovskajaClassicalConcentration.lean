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

public import FormalConjectures.Paper.VoronovskajaClassicalTaylor
public import FormalConjecturesForMathlib.Probability.Distributions.PoweredBinomialTails

/-!
# Exponential concentration of classical Bernstein weights

For an interior parameter `x`, the standardized classical Bernstein law is sub-Gaussian.  Hence the
mass of sampling points outside any fixed neighborhood of `x` decays exponentially, and multiplying
that mass by `n` still gives a sequence tending to zero.
-/

public section

noncomputable section

open Topology Filter Real unitInterval Polynomial
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory Topology unitInterval

namespace VoronovskajaTypeFormula

/-- Classical Bernstein mass outside the open `δ`-neighborhood of `x`. -/
@[expose]
noncomputable def classicalFarMass (n : ℕ) (x : I) (δ : ℝ) : ℝ :=
  ∑ k : Fin (n + 1),
    if δ ≤ |((k : ℝ) / (n : ℝ)) - (x : ℝ)| then
      bezierWeight n k 1 (x : ℝ)
    else 0

private lemma standardizeBinomial_eq_scale_frequency
    (n : ℕ) (hn : 0 < n) (x : I) (k : Fin (n + 1)) :
    standardizeBinomial n x ((k : ℕ) : ℝ) =
      Real.sqrt n / bernoulliStdDev x *
        (((k : ℝ) / (n : ℝ)) - (x : ℝ)) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := by
    rw [Real.sqrt_ne_zero']
    exact_mod_cast hn
  rw [standardizeBinomial]
  field_simp [hnR, hsqrt]
  rw [Real.sq_sqrt]
  · ring
  · positivity

private lemma far_index_maps_to_two_tails
    (n : ℕ) (hn : 0 < n)
    (x : I) (hx0 : 0 < (x : ℝ)) (hx1 : (x : ℝ) < 1)
    {δ : ℝ} (hδ : 0 < δ) (k : Fin (n + 1))
    (hk : δ ≤ |((k : ℝ) / (n : ℝ)) - (x : ℝ)|) :
    standardizeBinomial n x ((k : ℕ) : ℝ) ∈
      Ioi (Real.sqrt n * δ / (2 * bernoulliStdDev x)) ∪
        Iic (-(Real.sqrt n * δ / (2 * bernoulliStdDev x))) := by
  have hs : 0 < bernoulliStdDev x := bernoulliStdDev_pos x hx0 hx1
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  rw [standardizeBinomial_eq_scale_frequency n hn x k]
  have hscale : 0 < Real.sqrt n / bernoulliStdDev x := div_pos hsqrt hs
  have habs :
      Real.sqrt n * δ / bernoulliStdDev x ≤
        |Real.sqrt n / bernoulliStdDev x *
          (((k : ℝ) / (n : ℝ)) - (x : ℝ))| := by
    rw [abs_mul, abs_of_pos hscale]
    have := mul_le_mul_of_nonneg_left hk hscale.le
    convert this using 1 <;> field_simp [hs.ne'] <;> ring
  by_cases hz : Real.sqrt n / bernoulliStdDev x *
      (((k : ℝ) / (n : ℝ)) - (x : ℝ)) > 0
  · left
    rw [abs_of_pos hz] at habs
    have hhalf :
        Real.sqrt n * δ / (2 * bernoulliStdDev x) <
          Real.sqrt n * δ / bernoulliStdDev x := by
      have hp : 0 < Real.sqrt n * δ / bernoulliStdDev x := by positivity
      linarith
    exact hhalf.trans_le habs
  · right
    have hz0 : Real.sqrt n / bernoulliStdDev x *
        (((k : ℝ) / (n : ℝ)) - (x : ℝ)) ≤ 0 := le_of_not_gt hz
    rw [abs_of_nonpos hz0] at habs
    have hhalf :
        Real.sqrt n * δ / (2 * bernoulliStdDev x) <
          Real.sqrt n * δ / bernoulliStdDev x := by
      have hp : 0 < Real.sqrt n * δ / bernoulliStdDev x := by positivity
      linarith
    linarith

private lemma classicalFarMass_le_measure_tails
    (n : ℕ) (hn : 0 < n)
    (x : I) (hx0 : 0 < (x : ℝ)) (hx1 : (x : ℝ) < 1)
    {δ : ℝ} (hδ : 0 < δ) :
    classicalFarMass n x δ ≤
      (standardizedBezierMeasure n 1 one_pos x).real
        (Ioi (Real.sqrt n * δ / (2 * bernoulliStdDev x)) ∪
          Iic (-(Real.sqrt n * δ / (2 * bernoulliStdDev x)))) := by
  rw [classicalFarMass, standardizedBezierMeasure, standardizedBezierPMF,
    measureReal_def]
  rw [PMF.toMeasure_map_apply _ _ _ (by fun_prop)
    (measurableSet_Ioi.union measurableSet_Iic)]
  rw [PMF.toMeasure_apply_fintype, ENNReal.toReal_sum]
  · apply Finset.sum_le_sum
    intro k hk
    by_cases hfar : δ ≤ |((k : ℝ) / (n : ℝ)) - (x : ℝ)|
    · have hmem := far_index_maps_to_two_tails n hn x hx0 hx1 hδ k hfar
      have hw : 0 ≤ bezierWeight n k 1 (x : ℝ) :=
        bezierWeight_nonneg n k (Nat.le_of_lt_succ k.isLt) one_pos x.property
      simp [hfar, hmem, bezierPMF_apply, ENNReal.toReal_ofReal hw]
    · simp [hfar]
  · intro k hk
    by_cases hmem : standardizeBinomial n x ((k : ℕ) : ℝ) ∈
        Ioi (Real.sqrt n * δ / (2 * bernoulliStdDev x)) ∪
          Iic (-(Real.sqrt n * δ / (2 * bernoulliStdDev x)))
    · simp [hmem, (bezierPMF n 1 one_pos x).apply_ne_top]
    · simp [hmem]

private lemma classicalFarMass_le_exp
    (n : ℕ) (hn : 0 < n)
    (x : I) (hx0 : 0 < (x : ℝ)) (hx1 : (x : ℝ) < 1)
    {δ : ℝ} (hδ : 0 < δ) :
    classicalFarMass n x δ ≤
      2 * exp (-
        ((n : ℝ) * δ ^ 2 /
          (8 * (standardizedBernoulliSubgaussianParameter x : ℝ) *
            (bernoulliStdDev x) ^ 2))) := by
  let t : ℝ := Real.sqrt n * δ / (2 * bernoulliStdDev x)
  have ht : 0 ≤ t := by
    dsimp [t]
    positivity
  have hmass := classicalFarMass_le_measure_tails n hn x hx0 hx1 hδ
  rw [standardizedBezierMeasure_eq_poweredStandardizedBinomial n 1 one_pos x] at hmass
  have hright :=
    measureReal_Ioi_poweredStandardizedBinomialProbability_le_exp_rpow
      n hn x hx0 hx1 1 one_pos t ht
  have hleft :=
    measureReal_Iic_poweredStandardizedBinomialProbability_le_exp_rpow
      n hn x hx0 hx1 1 one_pos le_rfl t ht
  have hunion := measureReal_union_le
    (μ := (poweredStandardizedBinomialProbability n x 1 one_pos : Measure ℝ))
    (Ioi t) (Iic (-t))
  have hs : bernoulliStdDev x ≠ 0 := (bernoulliStdDev_pos x hx0 hx1).ne'
  have hc : (standardizedBernoulliSubgaussianParameter x : ℝ) ≠ 0 := by
    have hp : 0 < (standardizedBernoulliSubgaussianParameter x : ℝ) := by
      rw [standardizedBernoulliSubgaussianParameter]
      positivity
    exact hp.ne'
  have hsquare : t ^ 2 =
      (n : ℝ) * δ ^ 2 / (4 * (bernoulliStdDev x) ^ 2) := by
    dsimp [t]
    rw [div_pow, mul_pow, Real.sq_sqrt]
    · field_simp [hs]
      ring
    · positivity
  calc
    classicalFarMass n x δ ≤
        (poweredStandardizedBinomialProbability n x 1 one_pos : Measure ℝ).real
          (Ioi t ∪ Iic (-t)) := hmass
    _ ≤ (poweredStandardizedBinomialProbability n x 1 one_pos : Measure ℝ).real (Ioi t) +
        (poweredStandardizedBinomialProbability n x 1 one_pos : Measure ℝ).real (Iic (-t)) :=
      hunion
    _ ≤ (exp (-t ^ 2 /
          (2 * (standardizedBernoulliSubgaussianParameter x : ℝ)))) ^ (1 : ℝ) +
        (exp (-t ^ 2 /
          (2 * (standardizedBernoulliSubgaussianParameter x : ℝ)))) ^ (1 : ℝ) :=
      add_le_add hright hleft
    _ = 2 * exp (-
        ((n : ℝ) * δ ^ 2 /
          (8 * (standardizedBernoulliSubgaussianParameter x : ℝ) *
            (bernoulliStdDev x) ^ 2))) := by
      rw [Real.rpow_one, hsquare]
      congr 1
      field_simp [hc, hs]
      ring

/-- Multiplying the far mass by `n` still gives a sequence tending to zero. -/
lemma tendsto_nat_mul_classicalFarMass
    (x : I) (hx0 : 0 < (x : ℝ)) (hx1 : (x : ℝ) < 1)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * classicalFarMass n x δ) atTop (𝓝 0) := by
  let r : ℝ := δ ^ 2 /
    (8 * (standardizedBernoulliSubgaussianParameter x : ℝ) *
      (bernoulliStdDev x) ^ 2)
  have hc : 0 < (standardizedBernoulliSubgaussianParameter x : ℝ) := by
    rw [standardizedBernoulliSubgaussianParameter]
    positivity
  have hs : 0 < bernoulliStdDev x := bernoulliStdDev_pos x hx0 hx1
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hbound : ∀ᶠ n : ℕ in atTop,
      0 ≤ (n : ℝ) * classicalFarMass n x δ ∧
      (n : ℝ) * classicalFarMass n x δ ≤
        2 * ((n : ℝ) * exp (-r * (n : ℝ))) := by
    refine eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩
    have hn0 : 0 < n := hn
    have hmass := classicalFarMass_le_exp n hn0 x hx0 hx1 hδ
    constructor
    · exact mul_nonneg (Nat.cast_nonneg n) <| Finset.sum_nonneg fun k hk ↦ by
        split_ifs <;> positivity
    · calc
        (n : ℝ) * classicalFarMass n x δ ≤
            (n : ℝ) * (2 * exp (-r * (n : ℝ))) :=
          mul_le_mul_of_nonneg_left (by simpa [r] using hmass) (Nat.cast_nonneg n)
        _ = 2 * ((n : ℝ) * exp (-r * (n : ℝ))) := by ring
  have hgeom : Tendsto
      (fun n : ℕ ↦ (n : ℝ) * exp (-r * (n : ℝ))) atTop (𝓝 0) := by
    exact (Real.summable_pow_mul_exp_neg_nat_mul 1 hr).tendsto_atTop_zero
  apply squeeze_zero'
  · exact hbound.mono fun n hn ↦ hn.1
  · exact hbound.mono fun n hn ↦ hn.2
  · simpa using (tendsto_const_nhds.mul hgeom)

end VoronovskajaTypeFormula
