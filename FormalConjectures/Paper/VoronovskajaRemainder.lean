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

public import FormalConjectures.Paper.VoronovskajaTaylorBound

/-!
# The scaled Taylor remainder vanishes

The global quadratic Taylor estimate is summed against the nonnegative Bézier weights.  The resulting
upper bound is exactly the squared centered moment whose `sqrt n` scaling was proved to vanish.
-/

public section

noncomputable section

open Topology Filter Real unitInterval Polynomial
open Set

namespace VoronovskajaTypeFormula

private lemma sample_mem_unitInterval
    (n : ℕ) (hn : 0 < n) {k : ℕ} (hk : k ∈ Finset.range (n + 1)) :
    ((k : ℝ) / (n : ℝ)) ∈ I := by
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  constructor
  · positivity
  · rw [div_le_one]
    · exact_mod_cast hkn
    · exact_mod_cast hn

/-- A uniform quadratic Taylor estimate bounds the weighted Bézier remainder by the squared centered
moment. -/
lemma abs_bezierTaylorRemainder_le_sq_moment
    (n : ℕ) (hn : 0 < n)
    (α : ℝ) (hα : 0 < α)
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f I)
    (x : ℝ) (hx : x ∈ I)
    (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ y ∈ I, ‖iteratedDerivWithin 2 f I y‖ ≤ M) :
    |bezierTaylorRemainder n α f x (iteratedDerivWithin 1 f I x)| ≤
      M *
        (∑ k ∈ Finset.range (n + 1),
          ((((k : ℝ) / (n : ℝ)) - x) ^ 2) * bezierWeight n k α x) := by
  rw [bezierTaylorRemainder]
  calc
    |∑ k ∈ Finset.range (n + 1),
        (f ((k : ℝ) / (n : ℝ)) - f x -
          iteratedDerivWithin 1 f I x * (((k : ℝ) / (n : ℝ)) - x)) *
            bezierWeight n k α x| ≤
        ∑ k ∈ Finset.range (n + 1),
          |(f ((k : ℝ) / (n : ℝ)) - f x -
            iteratedDerivWithin 1 f I x * (((k : ℝ) / (n : ℝ)) - x)) *
              bezierWeight n k α x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (n + 1),
        M * (((((k : ℝ) / (n : ℝ)) - x) ^ 2) * bezierWeight n k α x) := by
      apply Finset.sum_le_sum
      intro k hk
      have hy : ((k : ℝ) / (n : ℝ)) ∈ I := sample_mem_unitInterval n hn hk
      have hw : 0 ≤ bezierWeight n k α x :=
        bezierWeight_nonneg n k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) hα hx
      have hTaylor := norm_sub_linearization_le_sq f hf M hM0 hM hx hy
      rw [Real.norm_eq_abs] at hTaylor
      rw [abs_mul, abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_right hTaylor hw
    _ = M *
        (∑ k ∈ Finset.range (n + 1),
          ((((k : ℝ) / (n : ℝ)) - x) ^ 2) * bezierWeight n k α x) := by
      rw [Finset.mul_sum]

/-- For every interior point, the scaled weighted Taylor remainder tends to zero. -/
lemma tendsto_sqrt_mul_bezierTaylorRemainder
    (α : ℝ) (hα : 0 < α)
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f I)
    (x : I) (hx0 : 0 < (x : ℝ)) (hx1 : (x : ℝ) < 1) :
    Tendsto
      (fun n : ℕ ↦ Real.sqrt n *
        bezierTaylorRemainder n α f (x : ℝ)
          (iteratedDerivWithin 1 f I (x : ℝ)))
      atTop (𝓝 0) := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_iteratedDerivWithin_two f hf
  have hsq := tendsto_sqrt_mul_sum_sq_centered_bezierWeight x hx0 hx1 α hα
  have hupper : Tendsto
      (fun n : ℕ ↦ M *
        (Real.sqrt n *
          (∑ k ∈ Finset.range (n + 1),
            ((((k : ℝ) / (n : ℝ)) - (x : ℝ)) ^ 2) *
              bezierWeight n k α (x : ℝ))))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hsq)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦ norm_nonneg _
  · refine eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩
    have hrem := abs_bezierTaylorRemainder_le_sq_moment
      n hn α hα f hf (x : ℝ) x.property M hM0 hM
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg n)]
    calc
      Real.sqrt n *
          |bezierTaylorRemainder n α f (x : ℝ)
            (iteratedDerivWithin 1 f I (x : ℝ))| ≤
        Real.sqrt n *
          (M *
            (∑ k ∈ Finset.range (n + 1),
              ((((k : ℝ) / (n : ℝ)) - (x : ℝ)) ^ 2) *
                bezierWeight n k α (x : ℝ))) :=
        mul_le_mul_of_nonneg_left hrem (Real.sqrt_nonneg n)
      _ = M *
          (Real.sqrt n *
            (∑ k ∈ Finset.range (n + 1),
              ((((k : ℝ) / (n : ℝ)) - (x : ℝ)) ^ 2) *
                bezierWeight n k α (x : ℝ))) := by ring
  · exact hupper

end VoronovskajaTypeFormula
