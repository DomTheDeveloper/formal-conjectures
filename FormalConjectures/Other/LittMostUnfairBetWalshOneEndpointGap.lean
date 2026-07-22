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

import FormalConjectures.Other.LittMostUnfairBetWalshInteriorGap

/-!
# The one-endpoint disagreement Walsh gap

When two words agree internally and differ at exactly one endpoint, every
full-span shape has a nonzero raw coefficient. There are `2^(n-2)` such
shapes, so their raw square contribution is `4 * 2^(n-2)`.
-/

set_option autoImplicit false

namespace LittMostUnfairBetWalsh

open Finset
open LittMostUnfairBet

/-- The interior coordinate set. -/
def interiorCoordinates (n : ℕ) : Finset ℕ := Finset.Ico 1 (n - 1)

@[simp] theorem mem_interiorCoordinates {n i : ℕ} :
    i ∈ interiorCoordinates n ↔ 1 ≤ i ∧ i < n - 1 := by
  simp [interiorCoordinates]

/-- Removing both endpoints from a full-span base recovers its interior set. -/
theorem erase_endpoints_fullSpanBase {n : ℕ} {R : Finset ℕ}
    (hR : R ⊆ interiorCoordinates n) :
    ((fullSpanBase n R).erase 0).erase (n - 1) = R := by
  have hR0 : 0 ∉ R := by
    intro h
    have hr := mem_interiorCoordinates.mp (hR h)
    omega
  have hRlast : n - 1 ∉ R := by
    intro h
    have hr := mem_interiorCoordinates.mp (hR h)
    omega
  ext i
  simp [fullSpanBase, hR0, hRlast]

/-- Adding both endpoints is injective on interior subsets. -/
theorem fullSpanBase_injective {n : ℕ} {R₁ R₂ : Finset ℕ}
    (hR₁ : R₁ ⊆ interiorCoordinates n)
    (hR₂ : R₂ ⊆ interiorCoordinates n)
    (heq : fullSpanBase n R₁ = fullSpanBase n R₂) : R₁ = R₂ := by
  rw [← erase_endpoints_fullSpanBase hR₁,
    ← erase_endpoints_fullSpanBase hR₂, heq]

/-- The interior has `n-2` coordinates. -/
theorem card_interiorCoordinates {n : ℕ} (hn : 2 ≤ n) :
    #(interiorCoordinates n) = n - 2 := by
  simp [interiorCoordinates]
  omega

/-- Full-span bases indexed by interior subsets form `2^(n-2)` distinct shapes. -/
theorem card_fullSpanBases {n : ℕ} (hn : 2 ≤ n) :
    #((interiorCoordinates n).powerset.image (fullSpanBase n)) = 2 ^ (n - 2) := by
  have hinj : Set.InjOn (fullSpanBase n) (interiorCoordinates n).powerset := by
    intro R₁ hR₁ R₂ hR₂ heq
    exact fullSpanBase_injective
      (Finset.mem_powerset.mp hR₁) (Finset.mem_powerset.mp hR₂) heq
  rw [Finset.card_image_of_injOn hinj]
  simp [card_interiorCoordinates hn]

/-- Equal letters have sign product `1`. -/
theorem letterSign_mul_eq_one_of_word_eq {n i : ℕ} (A B : Word n)
    (hi : i < n) (heq : A ⟨i, hi⟩ = B ⟨i, hi⟩) :
    letterSign A i * letterSign B i = 1 := by
  simp [letterSign, hi, heq]

/-- If the words agree internally and differ at exactly one endpoint, every
full-span base has monomial product `-1`. -/
theorem fullSpanBase_monomial_mul_eq_neg_one {n : ℕ} (hn : 2 ≤ n)
    (A B : Word n)
    (hinterior : ∀ i : Fin n, 0 < i.val → i.val < n - 1 → A i = B i)
    (hleft : A ⟨0, by omega⟩ ≠ B ⟨0, by omega⟩)
    (hright : A ⟨n - 1, by omega⟩ = B ⟨n - 1, by omega⟩)
    {R : Finset ℕ} (hR : R ⊆ interiorCoordinates n) :
    natMonomial A (fullSpanBase n R) *
      natMonomial B (fullSpanBase n R) = -1 := by
  have h0last : 0 ≠ n - 1 := by omega
  have hR0 : 0 ∉ R := by
    intro h
    have hr := mem_interiorCoordinates.mp (hR h)
    omega
  have hRlast : n - 1 ∉ R := by
    intro h
    have hr := mem_interiorCoordinates.mp (hR h)
    omega
  have hprodR :
      ∏ i ∈ R, (letterSign A i * letterSign B i) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    have hr := mem_interiorCoordinates.mp (hR hi)
    apply letterSign_mul_eq_one_of_word_eq A B (by omega)
    exact hinterior ⟨i, by omega⟩ (by omega) (by omega)
  unfold natMonomial fullSpanBase
  rw [← Finset.prod_mul_distrib]
  rw [Finset.prod_insert hR0]
  rw [Finset.prod_insert (by simp [hRlast, h0last])]
  rw [hprodR]
  have hleftSign := letterSign_mul_eq_neg_one_of_word_ne A B
    (j := 0) (by omega) hleft
  have hrightSign := letterSign_mul_eq_one_of_word_eq A B
    (i := n - 1) (by omega) hright
  rw [hleftSign, hrightSign]
  norm_num

/-- Symmetric endpoint-position version with the right endpoint differing. -/
theorem fullSpanBase_monomial_mul_eq_neg_one_right {n : ℕ} (hn : 2 ≤ n)
    (A B : Word n)
    (hinterior : ∀ i : Fin n, 0 < i.val → i.val < n - 1 → A i = B i)
    (hleft : A ⟨0, by omega⟩ = B ⟨0, by omega⟩)
    (hright : A ⟨n - 1, by omega⟩ ≠ B ⟨n - 1, by omega⟩)
    {R : Finset ℕ} (hR : R ⊆ interiorCoordinates n) :
    natMonomial A (fullSpanBase n R) *
      natMonomial B (fullSpanBase n R) = -1 := by
  have h0last : 0 ≠ n - 1 := by omega
  have hR0 : 0 ∉ R := by
    intro h
    have hr := mem_interiorCoordinates.mp (hR h)
    omega
  have hRlast : n - 1 ∉ R := by
    intro h
    have hr := mem_interiorCoordinates.mp (hR h)
    omega
  have hprodR :
      ∏ i ∈ R, (letterSign A i * letterSign B i) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    have hr := mem_interiorCoordinates.mp (hR hi)
    apply letterSign_mul_eq_one_of_word_eq A B (by omega)
    exact hinterior ⟨i, by omega⟩ (by omega) (by omega)
  unfold natMonomial fullSpanBase
  rw [← Finset.prod_mul_distrib]
  rw [Finset.prod_insert hR0]
  rw [Finset.prod_insert (by simp [hRlast, h0last])]
  rw [hprodR]
  have hleftSign := letterSign_mul_eq_one_of_word_eq A B
    (i := 0) (by omega) hleft
  have hrightSign := letterSign_mul_eq_neg_one_of_word_ne A B
    (j := n - 1) (by omega) hright
  rw [hleftSign, hrightSign]
  norm_num

/-- One endpoint disagreement forces raw energy at least `4 * 2^(n-2)`. -/
theorem rawEnergy_ge_of_one_endpoint_disagreement {n : ℕ} (hn : 3 ≤ n)
    (A B : Word n)
    (hinterior : ∀ i : Fin n, 0 < i.val → i.val < n - 1 → A i = B i)
    (hone :
      (A ⟨0, by omega⟩ ≠ B ⟨0, by omega⟩ ∧
        A ⟨n - 1, by omega⟩ = B ⟨n - 1, by omega⟩) ∨
      (A ⟨0, by omega⟩ = B ⟨0, by omega⟩ ∧
        A ⟨n - 1, by omega⟩ ≠ B ⟨n - 1, by omega⟩)) :
    4 * 2 ^ (n - 2) ≤ rawEnergy A B := by
  let selected := (interiorCoordinates n).powerset.image (fullSpanBase n)
  have hsubset : selected ⊆ shapes n := by
    intro S hS
    rcases Finset.mem_image.mp hS with ⟨R, hR, rfl⟩
    have hRsub := Finset.mem_powerset.mp hR
    apply mem_shapes.mpr
    refine ⟨?_, zero_mem_fullSpanBase n R⟩
    intro i hi
    simp only [fullSpanBase, Finset.mem_insert] at hi
    rcases hi with rfl | rfl | hi
    · simp; omega
    · simp; omega
    · have hr := mem_interiorCoordinates.mp (hRsub hi)
      simp; omega
  have hsquare : ∀ R ∈ (interiorCoordinates n).powerset,
      (shapeCoeff A B (fullSpanBase n R)).natAbs ^ 2 = 4 := by
    intro R hR
    have hRsub := Finset.mem_powerset.mp hR
    rw [shapeCoeff_eq_rawDifference_of_full_span (by omega) A B
      (fullSpanBase n R)
      (by
        intro i hi
        simp only [fullSpanBase, Finset.mem_insert] at hi
        rcases hi with rfl | rfl | hi
        · simp; omega
        · simp; omega
        · have hr := mem_interiorCoordinates.mp (hRsub hi)
          simp; omega)
      (last_mem_fullSpanBase n R)]
    apply rawDifference_natAbs_sq_eq_four_of_mul_eq_neg_one
    rcases hone with hone | hone
    · exact fullSpanBase_monomial_mul_eq_neg_one (by omega) A B hinterior
        hone.1 hone.2 hRsub
    · exact fullSpanBase_monomial_mul_eq_neg_one_right (by omega) A B hinterior
        hone.1 hone.2 hRsub
  have hselected :
      (∑ S ∈ selected, (shapeCoeff A B S).natAbs ^ 2) =
        4 * 2 ^ (n - 2) := by
    calc
      (∑ S ∈ selected, (shapeCoeff A B S).natAbs ^ 2) =
          ∑ _S ∈ selected, 4 := by
        apply Finset.sum_congr rfl
        intro S hS
        rcases Finset.mem_image.mp hS with ⟨R, hR, rfl⟩
        exact hsquare R hR
      _ = 4 * #selected := by simp [mul_comm]
      _ = 4 * 2 ^ (n - 2) := by rw [card_fullSpanBases (by omega)]
  rw [rawEnergy, ← hselected]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
    intro S hS hnot
    exact Nat.zero_le _)

#print axioms rawEnergy_ge_of_one_endpoint_disagreement

end LittMostUnfairBetWalsh
