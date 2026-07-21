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

public import FormalConjectures.Paper.VoronovskajaSecondMoment
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.Order.Compact

/-!
# A quadratic Taylor bound on the unit interval

A `C^2` real function on `[0,1]` has bounded second within-derivative.  The first within-derivative is
therefore Lipschitz.  Applying the mean-value inequality once more to the affine Taylor remainder
gives a global quadratic estimate with the derivative convention used by the original conjecture.
-/

public section

noncomputable section

open Topology Filter Real unitInterval Polynomial
open Set

namespace VoronovskajaTypeFormula

private lemma derivWithin_iteratedDerivWithin_one_eq_two
    (f : ℝ → ℝ) (y : ℝ) :
    derivWithin (iteratedDerivWithin 1 f I) I y =
      iteratedDerivWithin 2 f I y := by
  simpa using
    (iteratedDerivWithin_succ (n := 1) (f := f) (s := I) (x := y)).symm

/-- The second within-derivative of a `C^2` function is uniformly bounded on `[0,1]`. -/
lemma exists_bound_iteratedDerivWithin_two
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f I) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ y ∈ I, ‖iteratedDerivWithin 2 f I y‖ ≤ M := by
  have hI : UniqueDiffOn ℝ I := uniqueDiffOn_Icc zero_lt_one
  have hcont : ContinuousOn
      (fun y : ℝ ↦ ‖iteratedDerivWithin 2 f I y‖) I :=
    (hf.continuousOn_iteratedDerivWithin (by norm_num) hI).norm
  obtain ⟨y, hy, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr zero_le_one) hcont
  refine ⟨‖iteratedDerivWithin 2 f I y‖, norm_nonneg _, ?_⟩
  intro z hz
  exact hmax hz

private lemma hasDerivWithinAt_iteratedDerivWithin_one
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f I)
    (y : ℝ) (hy : y ∈ I) :
    HasDerivWithinAt (iteratedDerivWithin 1 f I)
      (iteratedDerivWithin 2 f I y) I y := by
  have hI : UniqueDiffOn ℝ I := uniqueDiffOn_Icc zero_lt_one
  have hd : DifferentiableOn ℝ (iteratedDerivWithin 1 f I) I :=
    hf.differentiableOn_iteratedDerivWithin (by norm_num) hI
  have h := (hd y hy).hasDerivWithinAt
  rw [derivWithin_iteratedDerivWithin_one_eq_two] at h
  exact h

private lemma hasDerivWithinAt_first
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f I)
    (y : ℝ) (hy : y ∈ I) :
    HasDerivWithinAt f (iteratedDerivWithin 1 f I y) I y := by
  have hd : DifferentiableOn ℝ f I := hf.differentiableOn (by norm_num)
  simpa only [iteratedDerivWithin_one] using (hd y hy).hasDerivWithinAt

/-- A uniform second-derivative bound makes the first within-derivative Lipschitz on `[0,1]`. -/
lemma norm_iteratedDerivWithin_one_sub_le
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f I)
    (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ y ∈ I, ‖iteratedDerivWithin 2 f I y‖ ≤ M)
    {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) :
    ‖iteratedDerivWithin 1 f I y - iteratedDerivWithin 1 f I x‖ ≤
      M * ‖y - x‖ := by
  rcases le_total x y with hxy | hyx
  · have hsub : Icc x y ⊆ I := Icc_subset_Icc hx.1 hy.2
    have hder : ∀ z ∈ Icc x y,
        HasDerivWithinAt (iteratedDerivWithin 1 f I)
          (iteratedDerivWithin 2 f I z) (Icc x y) z := by
      intro z hz
      exact (hasDerivWithinAt_iteratedDerivWithin_one f hf z (hsub hz)).mono hsub
    have hbound : ∀ z ∈ Ico x y,
        ‖iteratedDerivWithin 2 f I z‖ ≤ M := by
      intro z hz
      exact hM z (hsub (Ico_subset_Icc_self hz))
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      hder hbound y (right_mem_Icc.2 hxy)
    simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hxy)] using h
  · have hsub : Icc y x ⊆ I := Icc_subset_Icc hy.1 hx.2
    have hder : ∀ z ∈ Icc y x,
        HasDerivWithinAt (iteratedDerivWithin 1 f I)
          (iteratedDerivWithin 2 f I z) (Icc y x) z := by
      intro z hz
      exact (hasDerivWithinAt_iteratedDerivWithin_one f hf z (hsub hz)).mono hsub
    have hbound : ∀ z ∈ Ico y x,
        ‖iteratedDerivWithin 2 f I z‖ ≤ M := by
      intro z hz
      exact hM z (hsub (Ico_subset_Icc_self hz))
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      hder hbound x (right_mem_Icc.2 hyx)
    calc
      ‖iteratedDerivWithin 1 f I y - iteratedDerivWithin 1 f I x‖ =
          ‖iteratedDerivWithin 1 f I x - iteratedDerivWithin 1 f I y‖ :=
        norm_sub_rev _ _
      _ ≤ M * (x - y) := h
      _ = M * ‖y - x‖ := by
        rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hyx)]
        ring

/-- Global first-order Taylor remainder estimate on `[0,1]`. -/
lemma norm_sub_linearization_le_sq
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f I)
    (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ y ∈ I, ‖iteratedDerivWithin 2 f I y‖ ≤ M)
    {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) :
    ‖f y - f x - iteratedDerivWithin 1 f I x * (y - x)‖ ≤
      M * (y - x) ^ 2 := by
  let d : ℝ → ℝ := iteratedDerivWithin 1 f I
  let g : ℝ → ℝ := fun z ↦ f z - f x - d x * (z - x)
  rcases le_total x y with hxy | hyx
  · have hsub : Icc x y ⊆ I := Icc_subset_Icc hx.1 hy.2
    have hg : ∀ z ∈ Icc x y,
        HasDerivWithinAt g (d z - d x) (Icc x y) z := by
      intro z hz
      have hfz := (hasDerivWithinAt_first f hf z (hsub hz)).mono hsub
      have hc : HasDerivWithinAt (fun _ : ℝ ↦ f x) 0 (Icc x y) z :=
        (hasDerivAt_const z (f x)).hasDerivWithinAt
      have hl : HasDerivWithinAt (fun w : ℝ ↦ d x * (w - x)) (d x) (Icc x y) z := by
        convert (((hasDerivAt_id z).sub_const x).const_mul (d x)).hasDerivWithinAt using 1 <;>
          ring
      convert (hfz.sub hc).sub hl using 1 <;> simp [g, d]
    have hbound : ∀ z ∈ Ico x y, ‖d z - d x‖ ≤ M * (y - x) := by
      intro z hz
      have hzI : z ∈ I := hsub (Ico_subset_Icc_self hz)
      have hL := norm_iteratedDerivWithin_one_sub_le f hf M hM0 hM hx hzI
      have hzx : ‖z - x‖ = z - x := by
        rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hz.1)]
      dsimp [d] at hL
      rw [hzx] at hL
      exact hL.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right hz.2.le x) hM0)
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      hg hbound y (right_mem_Icc.2 hxy)
    have hgx : g x = 0 := by simp [g]
    rw [hgx, sub_zero] at h
    simpa [g, d, pow_two, mul_assoc] using h
  · have hsub : Icc y x ⊆ I := Icc_subset_Icc hy.1 hx.2
    have hg : ∀ z ∈ Icc y x,
        HasDerivWithinAt g (d z - d x) (Icc y x) z := by
      intro z hz
      have hfz := (hasDerivWithinAt_first f hf z (hsub hz)).mono hsub
      have hc : HasDerivWithinAt (fun _ : ℝ ↦ f x) 0 (Icc y x) z :=
        (hasDerivAt_const z (f x)).hasDerivWithinAt
      have hl : HasDerivWithinAt (fun w : ℝ ↦ d x * (w - x)) (d x) (Icc y x) z := by
        convert (((hasDerivAt_id z).sub_const x).const_mul (d x)).hasDerivWithinAt using 1 <;>
          ring
      convert (hfz.sub hc).sub hl using 1 <;> simp [g, d]
    have hbound : ∀ z ∈ Ico y x, ‖d z - d x‖ ≤ M * (x - y) := by
      intro z hz
      have hzI : z ∈ I := hsub (Ico_subset_Icc_self hz)
      have hL := norm_iteratedDerivWithin_one_sub_le f hf M hM0 hM hx hzI
      have hzx : ‖z - x‖ = x - z := by
        rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hz.2.le)]
        ring
      dsimp [d] at hL
      rw [hzx] at hL
      exact hL.trans (mul_le_mul_of_nonneg_left (sub_le_sub_left hz.1 x) hM0)
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      hg hbound x (right_mem_Icc.2 hyx)
    have hgx : g x = 0 := by simp [g]
    rw [hgx, zero_sub, norm_neg] at h
    calc
      ‖f y - f x - iteratedDerivWithin 1 f I x * (y - x)‖ ≤
          M * (x - y) * (x - y) := by
        simpa [g, d] using h
      _ = M * (y - x) ^ 2 := by ring

end VoronovskajaTypeFormula
