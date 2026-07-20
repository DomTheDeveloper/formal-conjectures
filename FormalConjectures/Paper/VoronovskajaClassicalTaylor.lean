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

public import FormalConjectures.Paper.VoronovskajaClassicalMoments
public import Mathlib.Analysis.Calculus.Taylor

/-!
# Second-order Taylor remainder for the classical Bernstein theorem

At a fixed point `x`, the second-order remainder is little-o of `(y-x)^2`. A global quadratic bound
also follows from the bounded second within-derivative established in the Bézier proof.
-/

public section

noncomputable section

open Topology Filter Real unitInterval Polynomial
open Set

namespace VoronovskajaTypeFormula

/-- Second-order Taylor remainder with the within-derivative convention of the conjecture. -/
@[expose]
noncomputable def classicalSecondRemainder
    (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  f y - f x - iteratedDerivWithin 1 f I x * (y - x) -
    (1 / 2 : ℝ) * iteratedDerivWithin 2 f I x * (y - x) ^ 2

lemma taylorWithinEval_two_eq
    (f : ℝ → ℝ) (x y : ℝ) :
    taylorWithinEval f 2 I x y =
      f x + iteratedDerivWithin 1 f I x * (y - x) +
        (1 / 2 : ℝ) * iteratedDerivWithin 2 f I x * (y - x) ^ 2 := by
  rw [taylor_within_apply]
  norm_num [Finset.sum_range_succ, smul_eq_mul]
  ring

lemma classicalSecondRemainder_eq_taylor_sub
    (f : ℝ → ℝ) (x y : ℝ) :
    classicalSecondRemainder f x y = f y - taylorWithinEval f 2 I x y := by
  rw [classicalSecondRemainder, taylorWithinEval_two_eq]
  ring

/-- The normalized second-order remainder tends to zero within the unit interval. -/
lemma tendsto_classicalSecondRemainder_div_sq
    (f : ℝ → ℝ) (x : ℝ) (hx : x ∈ I)
    (hf : ContDiffOn ℝ 2 f I) :
    Tendsto
      (fun y : ℝ ↦ classicalSecondRemainder f x y / (y - x) ^ 2)
      (𝓝[I] x) (𝓝 0) := by
  simpa only [classicalSecondRemainder_eq_taylor_sub] using
    (Real.taylor_tendsto (convex_Icc (0 : ℝ) 1) hx hf)

/-- Eventual epsilon form of the second-order Taylor estimate. -/
lemma eventually_abs_classicalSecondRemainder_le
    (f : ℝ → ℝ) (x : ℝ) (hx : x ∈ I)
    (hf : ContDiffOn ℝ 2 f I) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝[I] x,
      |classicalSecondRemainder f x y| ≤ ε * (y - x) ^ 2 := by
  have hratio : Tendsto
      (fun y : ℝ ↦ |classicalSecondRemainder f x y / (y - x) ^ 2|)
      (𝓝[I] x) (𝓝 0) := by
    simpa using (tendsto_classicalSecondRemainder_div_sq f x hx hf).abs
  have hev : ∀ᶠ y in 𝓝[I] x,
      |classicalSecondRemainder f x y / (y - x) ^ 2| < ε :=
    hratio.eventually_lt_const hε
  filter_upwards [hev] with y hy
  by_cases hxy : y = x
  · subst y
    simp [classicalSecondRemainder]
  · have hsq : 0 < (y - x) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hxy)
    rw [abs_div, abs_of_pos hsq] at hy
    have := (div_lt_iff₀ hsq).mp hy
    exact this.le

/-- A global quadratic bound for the second-order remainder. -/
lemma exists_global_bound_classicalSecondRemainder
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f I) (x : ℝ) (hx : x ∈ I) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ I, |classicalSecondRemainder f x y| ≤ C * (y - x) ^ 2 := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_iteratedDerivWithin_two f hf
  let C : ℝ := M + |(1 / 2 : ℝ) * iteratedDerivWithin 2 f I x|
  have hC0 : 0 ≤ C := add_nonneg hM0 (abs_nonneg _)
  refine ⟨C, hC0, ?_⟩
  intro y hy
  have hfirst := norm_sub_linearization_le_sq f hf M hM0 hM hx hy
  rw [Real.norm_eq_abs] at hfirst
  rw [classicalSecondRemainder]
  calc
    |(f y - f x - iteratedDerivWithin 1 f I x * (y - x)) -
        (1 / 2 : ℝ) * iteratedDerivWithin 2 f I x * (y - x) ^ 2| ≤
        |f y - f x - iteratedDerivWithin 1 f I x * (y - x)| +
          |(1 / 2 : ℝ) * iteratedDerivWithin 2 f I x * (y - x) ^ 2| :=
      abs_sub _ _
    _ ≤ M * (y - x) ^ 2 +
        |(1 / 2 : ℝ) * iteratedDerivWithin 2 f I x| * (y - x) ^ 2 := by
      have hsecond :
          |(1 / 2 : ℝ) * iteratedDerivWithin 2 f I x * (y - x) ^ 2| =
            |(1 / 2 : ℝ) * iteratedDerivWithin 2 f I x| * (y - x) ^ 2 := by
        rw [abs_mul, abs_pow, abs_sq]
      exact add_le_add hfirst hsecond.le
    _ = C * (y - x) ^ 2 := by
      simp [C]
      ring

end VoronovskajaTypeFormula
