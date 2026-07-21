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

public import FormalConjectures.Paper.VoronovskajaClassicalConcentration

/-!
# Negligibility of the classical second-order Taylor remainder

The local `o((y-x)^2)` estimate controls nearby Bernstein samples using the exact variance identity.
The global quadratic bound controls the remaining samples, whose total mass is exponentially small.
-/

public section

noncomputable section

open Topology Filter Real unitInterval Polynomial
open Set

namespace VoronovskajaTypeFormula

private lemma exists_delta_abs_classicalSecondRemainder_le
    (f : ℝ → ℝ) (x : ℝ) (hx : x ∈ I)
    (hf : ContDiffOn ℝ 2 f I) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∈ I, |y - x| < δ →
        |classicalSecondRemainder f x y| ≤ ε * (y - x) ^ 2 := by
  have hev := eventually_abs_classicalSecondRemainder_le f x hx hf hε
  change {y : ℝ | |classicalSecondRemainder f x y| ≤ ε * (y - x) ^ 2} ∈ 𝓝[I] x at hev
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hev
  obtain ⟨u, hu, hu_sub⟩ := hev
  rcases Metric.mem_nhds_iff.1 hu with ⟨δ, hδ, hball⟩
  refine ⟨δ, hδ, fun y hyI hyδ ↦ ?_⟩
  apply hu_sub
  refine ⟨hball ?_, hyI⟩
  simpa [Real.dist_eq] using hyδ

private lemma sample_mem_unitInterval_classical
    (n : ℕ) (hn : 0 < n) {k : ℕ} (hk : k ∈ Finset.range (n + 1)) :
    ((k : ℝ) / (n : ℝ)) ∈ I := by
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  constructor
  · positivity
  · rw [div_le_one]
    · exact_mod_cast hkn
    · exact_mod_cast hn

private lemma abs_sample_sub_le_one
    (n : ℕ) (hn : 0 < n) (x : I) {k : ℕ} (hk : k ∈ Finset.range (n + 1)) :
    |((k : ℝ) / (n : ℝ)) - (x : ℝ)| ≤ 1 := by
  have hy := sample_mem_unitInterval_classical n hn hk
  rw [abs_le]
  constructor <;> linarith [x.property.1, x.property.2, hy.1, hy.2]

/-- Weighted second-order Taylor remainder for the ordinary Bernstein operator. -/
@[expose]
noncomputable def classicalSecondRemainderSum
    (n : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    classicalSecondRemainder f x ((k : ℝ) / (n : ℝ)) *
      bezierWeight n k 1 x

private lemma abs_classicalSecondRemainderSum_le
    (n : ℕ) (hn : 0 < n)
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f I)
    (x : I)
    (C ε δ : ℝ) (hC0 : 0 ≤ C) (hε0 : 0 ≤ ε) (hδ : 0 < δ)
    (hglobal : ∀ y ∈ I,
      |classicalSecondRemainder f (x : ℝ) y| ≤ C * (y - (x : ℝ)) ^ 2)
    (hlocal : ∀ y ∈ I, |y - (x : ℝ)| < δ →
      |classicalSecondRemainder f (x : ℝ) y| ≤ ε * (y - (x : ℝ)) ^ 2) :
    |classicalSecondRemainderSum n f (x : ℝ)| ≤
      ε *
        (∑ k ∈ Finset.range (n + 1),
          ((((k : ℝ) / (n : ℝ)) - (x : ℝ)) ^ 2) *
            bezierWeight n k 1 (x : ℝ)) +
      C * classicalFarMass n x δ := by
  rw [classicalSecondRemainderSum]
  calc
    |∑ k ∈ Finset.range (n + 1),
        classicalSecondRemainder f (x : ℝ) ((k : ℝ) / (n : ℝ)) *
          bezierWeight n k 1 (x : ℝ)| ≤
        ∑ k ∈ Finset.range (n + 1),
          |classicalSecondRemainder f (x : ℝ) ((k : ℝ) / (n : ℝ)) *
            bezierWeight n k 1 (x : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (n + 1),
        (ε * ((((k : ℝ) / (n : ℝ)) - (x : ℝ)) ^ 2) *
            bezierWeight n k 1 (x : ℝ) +
          C * (if δ ≤ |((k : ℝ) / (n : ℝ)) - (x : ℝ)| then
            bezierWeight n k 1 (x : ℝ) else 0)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hy := sample_mem_unitInterval_classical n hn hk
      have hw : 0 ≤ bezierWeight n k 1 (x : ℝ) :=
        bezierWeight_nonneg n k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) one_pos x.property
      rw [abs_mul, abs_of_nonneg hw]
      by_cases hfar : δ ≤ |((k : ℝ) / (n : ℝ)) - (x : ℝ)|
      · have hR := hglobal ((k : ℝ) / (n : ℝ)) hy
        let d : ℝ := ((k : ℝ) / (n : ℝ)) - (x : ℝ)
        have habs : |d| ≤ 1 := by
          simpa [d] using abs_sample_sub_le_one n hn x hk
        have hsq : d ^ 2 ≤ 1 := by
          nlinarith [abs_nonneg d, sq_abs d]
        simp only [if_pos hfar]
        calc
          |classicalSecondRemainder f (x : ℝ) ((k : ℝ) / (n : ℝ))| *
              bezierWeight n k 1 (x : ℝ) ≤
              (C * d ^ 2) * bezierWeight n k 1 (x : ℝ) := by
            simpa [d] using mul_le_mul_of_nonneg_right hR hw
          _ ≤ C * bezierWeight n k 1 (x : ℝ) := by
            have hCd : C * d ^ 2 ≤ C := by
              simpa only [mul_one] using mul_le_mul_of_nonneg_left hsq hC0
            exact mul_le_mul_of_nonneg_right hCd hw
          _ ≤ ε * d ^ 2 * bezierWeight n k 1 (x : ℝ) +
              C * bezierWeight n k 1 (x : ℝ) := by
            exact le_add_of_nonneg_left (mul_nonneg (mul_nonneg hε0 (sq_nonneg d)) hw)
      · have hnear : |((k : ℝ) / (n : ℝ)) - (x : ℝ)| < δ := lt_of_not_ge hfar
        have hR := hlocal ((k : ℝ) / (n : ℝ)) hy hnear
        simp only [if_neg hfar, mul_zero, add_zero]
        exact mul_le_mul_of_nonneg_right hR hw
    _ = ε *
          (∑ k ∈ Finset.range (n + 1),
            ((((k : ℝ) / (n : ℝ)) - (x : ℝ)) ^ 2) *
              bezierWeight n k 1 (x : ℝ)) +
        C * classicalFarMass n x δ := by
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      · rw [Finset.mul_sum, classicalFarMass, Fin.sum_univ_eq_sum_range]

/-- The `n`-scaled second-order Taylor remainder tends to zero at every interior point. -/
lemma tendsto_nat_mul_classicalSecondRemainderSum
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f I)
    (x : I) (hx0 : 0 < (x : ℝ)) (hx1 : (x : ℝ) < 1) :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) * classicalSecondRemainderSum n f (x : ℝ))
      atTop (𝓝 0) := by
  obtain ⟨C, hC0, hglobal⟩ :=
    exists_global_bound_classicalSecondRemainder f hf (x : ℝ) x.property
  rw [Metric.tendsto_atTop]
  intro η hη
  let ε : ℝ := η / (2 * ((x : ℝ) * (1 - (x : ℝ)) + 1))
  have hden : 0 < 2 * ((x : ℝ) * (1 - (x : ℝ)) + 1) := by
    have hxprod : 0 ≤ (x : ℝ) * (1 - (x : ℝ)) := mul_nonneg x.property.1 (sub_nonneg.mpr x.property.2)
    positivity
  have hε : 0 < ε := div_pos hη hden
  obtain ⟨δ, hδ, hlocal⟩ :=
    exists_delta_abs_classicalSecondRemainder_le f (x : ℝ) x.property hf hε
  have hfar := (tendsto_nat_mul_classicalFarMass x hx0 hx1 hδ).const_mul C
  have hfar0 : Tendsto
      (fun n : ℕ ↦ C * ((n : ℝ) * classicalFarMass n x δ)) atTop (𝓝 0) := by
    simpa using hfar
  have hfarEventually : ∀ᶠ n : ℕ in atTop,
      |C * ((n : ℝ) * classicalFarMass n x δ)| < η / 2 := by
    have hnorm := hfar0.norm.eventually_lt_const (half_pos hη)
    simpa [Real.norm_eq_abs] using hnorm
  rcases eventually_atTop.1 hfarEventually with ⟨N, hN⟩
  refine ⟨max 1 N, fun n hn ↦ ?_⟩
  have hn1 : 1 ≤ n := (le_max_left 1 N).trans hn
  have hfarN := hN n ((le_max_right 1 N).trans hn)
  have hn0 : 0 < n := hn1
  have hsum := abs_classicalSecondRemainderSum_le
    n hn0 f hf x C ε δ hC0 hε.le hδ hglobal hlocal
  have hvar := sum_sq_centered_bezierWeight_one n hn0 x
  rw [hvar] at hsum
  rw [Real.dist_eq, sub_zero, abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
  calc
    (n : ℝ) * |classicalSecondRemainderSum n f (x : ℝ)| ≤
        (n : ℝ) *
          (ε * ((x : ℝ) * (1 - (x : ℝ)) / (n : ℝ)) +
            C * classicalFarMass n x δ) :=
      mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg n)
    _ = ε * ((x : ℝ) * (1 - (x : ℝ))) +
        C * ((n : ℝ) * classicalFarMass n x δ) := by
      field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast hn0.ne']
      ring
    _ ≤ η / 2 + |C * ((n : ℝ) * classicalFarMass n x δ)| := by
      have hnear : ε * ((x : ℝ) * (1 - (x : ℝ))) ≤ η / 2 := by
        dsimp [ε]
        have hxprod : 0 ≤ (x : ℝ) * (1 - (x : ℝ)) :=
          mul_nonneg x.property.1 (sub_nonneg.mpr x.property.2)
        apply (div_le_iff₀ hden).2
        nlinarith
      gcongr
      exact le_abs_self _
    _ < η / 2 + η / 2 := add_lt_add_left hfarN _
    _ = η := add_halves η

end VoronovskajaTypeFormula
