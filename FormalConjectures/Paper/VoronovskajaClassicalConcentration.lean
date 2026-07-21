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

For an interior parameter `x`, the standardized classical Bernstein law is sub-Gaussian. Hence the
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
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  rw [standardizeBinomial]
  field_simp [hnR, hsqrt]
  rw [Real.sq_sqrt hn0]
  ring

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
  have hhalf :
      Real.sqrt n * δ / (2 * bernoulliStdDev x) <
        Real.sqrt n * δ / bernoulliStdDev x := by
    have hp : 0 < Real.sqrt n * δ / bernoulliStdDev x := by positivity
    have heq :
        Real.sqrt n * δ / (2 * bernoulliStdDev x) =
          (Real.sqrt n * δ / bernoulliStdDev x) / 2 := by
      field_simp [hs.ne']
    rw [heq]
    linarith
  by_cases hz : Real.sqrt n / bernoulliStdDev x *
      (((k : ℝ) / (n : ℝ)) - (x : ℝ)) > 0
  · left
    rw [abs_of_pos hz] at habs
    exact hhalf.trans_le habs
  · right
    have hz0 : Real.sqrt n / bernoulliStdDev x *
        (((k : ℝ) / (n : ℝ)) - (x : ℝ)) ≤ 0 := le_of_not_gt hz
    rw [abs_of_nonpos hz0] at habs
    have hzle :
        Real.sqrt n / bernoulliStdDev x *
            (((k : ℝ) / (n : ℝ)) - (x : ℝ)) ≤
          -(Real.sqrt n * δ / bernoulliStdDev x) := by
      linarith
    have hneg :
        -(Real.sqrt n * δ / bernoulliStdDev x) ≤
          -(Real.sqrt n * δ / (2 * bernoulliStdDev x)) := by
      linarith
    exact hzle.trans hneg

private lemma classicalFarMass_le_measure_tails
    (n : ℕ) (hn : 0 < n)
    (x : I) (hx0 : 0 < (x : ℝ)) (hx1 : (x : ℝ) < 1)
    {δ : ℝ} (hδ : 0 < δ) :
    classicalFarMass n x δ ≤
      (standardizedBezierMeasure n 1 one_pos x).real
        (Ioi (Real.sqrt n * δ / (2 * bernoulliStdDev x)) ∪
          Iic (-(Real.sqrt n * δ / (2 * bernoulliStdDev x)))) := by
  let tails : Set ℝ :=
    Ioi (Real.sqrt n * δ / (2 * bernoulliStdDev x)) ∪
      Iic (-(Real.sqrt n * δ / (2 * bernoulliStdDev x)))
  rw [classicalFarMass, standardizedBezierMeasure, standardizedBezierPMF,
    measureReal_def]
  rw [PMF.toMeasure_map_apply _ _ _ (by fun_prop)
    (measurableSet_Ioi.union measurableSet_Iic)]
  rw [PMF.toMeasure_apply_fintype, ENNReal.toReal_sum]
  · apply Finset.sum_le_sum
    intro k hk
    by_cases hfar : δ ≤ |((k : ℝ) / (n : ℝ)) - (x : ℝ)|
    · have hmem := far_index_maps_to_two_tails n hn x hx0 hx1 hδ k hfar
      have hpre : k ∈ (fun j : Fin (n + 1) ↦
          standardizeBinomial n x ((j : ℕ) : ℝ)) ⁻¹' tails := hmem
      have hw : 0 ≤ bezierWeight n k 1 (x : ℝ) :=
        bezierWeight_nonneg n k (Nat.le_of_lt_succ k.isLt) one_pos x.property
      rw [if_pos hfar, Set.indicator_of_mem hpre]
      simp [bezierPMF_apply, ENNReal.toReal_ofReal hw]
    · rw [if_neg hfar]
      exact ENNReal.toReal_nonneg
  · intro k hk
    by_cases hmem : standardizeBinomial n x ((k : ℕ) : ℝ) ∈ tails
    · have hpre : k ∈ (fun j : Fin (n + 1) ↦
          standardizeBinomial n x ((j : ℕ) : ℝ)) ⁻¹' tails := hmem
      rw [Set.indicator_of_mem hpre]
      exact (bezierPMF n 1 one_pos x).apply_ne_top k
    · simp [hmem]

private lemma standardizedBernoulliSubgaussianParameter_pos
    (x : I) (hx0 : 0 < (x : ℝ)) (hx1 : (x : ℝ) < 1) :
    0 < (standardizedBernoulliSubgaussianParameter x : ℝ) := by
  have hs : 0 < bernoulliStdDev x := bernoulliStdDev_pos x hx0 hx1
  have hwidth :
      ((1 - (x : ℝ)) / bernoulliStdDev x) -
          (-(x : ℝ) / bernoulliStdDev x) =
        1 / bernoulliStdDev x := by
    field_simp [hs.ne']
    ring
  have hdiff :
      ((1 - (x : ℝ)) / bernoulliStdDev x) -
          (-(x : ℝ) / bernoulliStdDev x) ≠ 0 := by
    rw [hwidth]
    exact one_div_ne_zero hs.ne'
  have hnorm :
      0 < ‖((1 - (x : ℝ)) / bernoulliStdDev x) -
          (-(x : ℝ) / bernoulliStdDev x)‖₊ :=
    nnnorm_pos.mpr hdiff
  rw [standardizedBernoulliSubgaussianParameter]
  exact_mod_cast (sq_pos_of_pos (div_pos hnorm (by norm_num : (0 : ℝ≥0) < 2)))

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
  have hspos : 0 < bernoulliStdDev x := bernoulliStdDev_pos x hx0 hx1
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
  have hs : bernoulliStdDev x ≠ 0 := hspos.ne'
  have hcpos := standardizedBernoulliSubgaussianParameter_pos x hx0 hx1
  have hc : (standardizedBernoulliSubgaussianParameter x : ℝ) ≠ 0 := hcpos.ne'
  have hsquare : t ^ 2 =
      (n : ℝ) * δ ^ 2 / (4 * (bernoulliStdDev x) ^ 2) := by
    dsimp [t]
    rw [div_pow, mul_pow, Real.sq_sqrt]
    · field_simp [hs]
      ring_nf
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
      ring_nf

/-- Multiplying the far mass by `n` still gives a sequence tending to zero. -/
lemma tendsto_nat_mul_classicalFarMass
    (x : I) (hx0 : 0 < (x : ℝ)) (hx1 : (x : ℝ) < 1)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * classicalFarMass n x δ) atTop (𝓝 0) := by
  let r : ℝ := δ ^ 2 /
    (8 * (standardizedBernoulliSubgaussianParameter x : ℝ) *
      (bernoulliStdDev x) ^ 2)
  have hs : 0 < bernoulliStdDev x := bernoulliStdDev_pos x hx0 hx1
  have hc := standardizedBernoulliSubgaussianParameter_pos x hx0 hx1
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
    have hmass' : classicalFarMass n x δ ≤ 2 * exp (-r * (n : ℝ)) := by
      convert hmass using 1
      dsimp [r]
      ring_nf
    constructor
    · have hfar0 : 0 ≤ classicalFarMass n x δ := by
        apply Finset.sum_nonneg
        intro k hk
        split_ifs
        · exact bezierWeight_nonneg n k (Nat.le_of_lt_succ k.isLt) one_pos x.property
        · exact le_rfl
      exact mul_nonneg (Nat.cast_nonneg n) hfar0
    · calc
        (n : ℝ) * classicalFarMass n x δ ≤
            (n : ℝ) * (2 * exp (-r * (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hmass' (Nat.cast_nonneg n)
        _ = 2 * ((n : ℝ) * exp (-r * (n : ℝ))) := by ring
  have hgeom : Tendsto
      (fun n : ℕ ↦ (n : ℝ) * exp (-r * (n : ℝ))) atTop (𝓝 0) := by
    simpa [pow_one] using
      (Real.summable_pow_mul_exp_neg_nat_mul 1 hr).tendsto_atTop_zero
  apply squeeze_zero'
  · exact hbound.mono fun n hn ↦ hn.1
  · exact hbound.mono fun n hn ↦ hn.2
  · simpa using (tendsto_const_nhds.mul hgeom)

end VoronovskajaTypeFormula
