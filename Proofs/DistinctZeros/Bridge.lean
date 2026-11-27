/-
Copyright 2026 The Formal Conjectures Authors and @domthedeveloper.
Released under Apache 2.0 license.
The five counting and threshold definitions below are copied from google-deepmind/formal-conjectures
at f606af160664c5a10952e9a957b100a1cd45bbeb.
-/
import Mathlib

noncomputable section

namespace Complex

noncomputable def zeroCountOn (f : ℂ → ℂ) (S : Set ℂ) : ℕ :=
  ∑ᶠ s ∈ S, analyticOrderNatAt f s

end Complex

namespace ZetaZeros

def nontrivialZeros (f : ℂ → ℂ) (T₁ T₂ : ℝ) : Set ℂ :=
  {s | f s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ T₁ < s.im ∧ s.im ≤ T₂}

noncomputable def N (f : ℂ → ℂ) (T₁ T₂ : ℝ) : ℕ :=
  Complex.zeroCountOn f (nontrivialZeros f T₁ T₂)

noncomputable def Nd (f : ℂ → ℂ) (T₁ T₂ : ℝ) : ℕ := (nontrivialZeros f T₁ T₂).ncard

noncomputable def montgomeryTaylorConst : ℝ := √2 * (1 / √2).tan / (1 + (1 / √2).tan / √2)

end ZetaZeros

namespace DistinctZeros

open Real

private theorem threshold_lt :
    (3 - (√2 * tan (1 / √2) / (1 + tan (1 / √2) / √2))⁻¹) / 2 < (17 / 20 : ℝ) := by
  let x : ℝ := 1 / √2
  have hr : (0 : ℝ) < √2 := by positivity
  have hr2 : (√(2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hx : 0 < x := by dsimp [x]; positivity
  have hx2 : x ^ 2 = 1 / 2 := by simp [x, hr2]
  have hc : 3 / 4 ≤ cos x := by linarith [one_sub_sq_div_two_le_cos (x := x)]
  have hs : 0 < sin x := sin_pos_of_pos_of_lt_pi hx (by nlinarith [Real.pi_gt_three])
  have hcpos : 0 < cos x := by linarith
  have hsc : 32 * sin x ^ 2 < 25 * cos x ^ 2 := by
    nlinarith [sin_sq_add_cos_sq x, mul_nonneg (sub_nonneg.mpr hc) (show 0 ≤ cos x + 3/4 by linarith)]
  have hu : 4 * √2 * sin x < 5 * cos x := by
    by_contra! h
    have hsquares := mul_nonneg (sub_nonneg.mpr h)
      (show 0 ≤ 4 * √2 * sin x + 5 * cos x by positivity)
    nlinarith [show (4 * √2 * sin x) ^ 2 = 32 * sin x ^ 2 by rw [mul_pow, mul_pow, hr2]; ring]
  let u := √2 * tan x
  have hu0 : 0 < u := by
    dsimp [u]
    rw [tan_eq_sin_div_cos]
    positivity
  have hu' : u < 5 / 4 := by
    dsimp [u]
    rw [tan_eq_sin_div_cos, ← mul_div_assoc, div_lt_iff₀ hcpos]
    linarith
  have hd : tan x / √2 = u / 2 := by
    apply (div_eq_iff (ne_of_gt hr)).2
    dsimp [u]
    calc
      tan x = tan x * ((√2)^2 / 2) := by rw [hr2]; ring
      _ = _ := by ring
  change (3 - (u / (1 + tan x / √2))⁻¹) / 2 < _
  rw [hd, inv_div]
  have := (lt_div_iff₀ hu0).2 (show (13 / 10) * u < 1 + u / 2 by linarith)
  linarith

open Filter Asymptotics

/-- A bound for every sufficiently large dyadic window gives the requested little-o estimate. -/
private theorem dyadic_to_all_heights (total distinct : ℝ → ℕ) {k : ℝ} (hk : 17/20 < k)
    (h : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (k - ε) * (total T : ℝ) ≤ distinct T) :
    ∃ o : ℝ → ℝ, o =o[atTop] (1 : ℝ → ℝ) ∧
      ∀ T > 0, (17/20 - o T) * (total T : ℝ) ≤ distinct T := by
  obtain ⟨T₀, hT₀⟩ := h (k - 17/20) (sub_pos.mpr hk)
  refine ⟨fun T => if T₀ ≤ T then 0 else 17/20, ?_, ?_⟩
  · refine (isLittleO_zero (1 : ℝ → ℝ) atTop).congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop T₀] with T hT
    simp [hT]
  · intro T _
    by_cases hT : T₀ ≤ T
    · simpa [hT] using hT₀ T hT
    · simp [hT]

open ZetaZeros

/-- Distinct critical-line zeros in the same half-open window as `ZetaZeros.Nd`. -/
noncomputable def lineCount (a b : ℝ) : ℕ :=
  (nontrivialZeros riemannZeta a b ∩ {z : ℂ | z.re = 1 / 2}).ncard

private theorem lineCount_le (a b : ℝ) : lineCount a b ≤ Nd riemannZeta a b := by
  have hK : IsCompact (Complex.reProdIm (Set.Icc (0 : ℝ) 1) (Set.Icc a b)) :=
    isCompact_Icc.reProdIm isCompact_Icc
  refine Set.ncard_le_ncard Set.inter_subset_left (hK.inter_riemannZetaZeros_finite.subset ?_)
  rintro z ⟨hz, hr₀, hr₁, hi₀, hi₁⟩
  exact ⟨⟨⟨hr₀.le, hr₁.le⟩, ⟨hi₀.le, hi₁⟩⟩, hz⟩

theorem distinct_prop_lt_of_record {k : ℝ}
    (hk : 17 / 20 < k)
    (record : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (k - ε) * (N riemannZeta T (2 * T) : ℝ) ≤ lineCount T (2 * T)) :
    ∃ c > (3 - montgomeryTaylorConst⁻¹) / 2, ∃ o : ℝ → ℝ,
      o =o[atTop] (1 : ℝ → ℝ) ∧ ∀ T > 0,
        (c - o T) * N riemannZeta T (2 * T) ≤ Nd riemannZeta T (2 * T) := by
  refine ⟨17 / 20, threshold_lt, dyadic_to_all_heights _ _ hk ?_⟩
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := record ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  exact (hT₀ T hT).trans ((Nat.cast_le (α := ℝ)).2 (lineCount_le T (2 * T)))

end DistinctZeros

end
