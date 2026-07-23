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

import FormalConjectures.Other.LittMostUnfairBetWalshTwoEndpointCore

/-!
# Sign toggling in the two-endpoint Litt gap
-/

set_option autoImplicit false

namespace LittMostUnfairBetWalsh

open Finset
open LittMostUnfairBet

theorem product_eq_four_or_neg_four_of_raw_squares {a b : ℤ}
    (ha : a = 2 ∨ a = -2) (hb : b = 2 ∨ b = -2) :
    a * b = 4 ∨ a * b = -4 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num

theorem natAbs_add_sq_eq_sixteen_of_raw_product {a b : ℤ}
    (ha : a = 2 ∨ a = -2) (hb : b = 2 ∨ b = -2)
    (hprod : a * b = 4) :
    (a + b).natAbs ^ 2 = 16 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  all_goals norm_num at hprod ⊢

theorem rawDifference_eq_two_or_neg_two_of_square {n : ℕ}
    (A B : Word n) (S : Finset ℕ)
    (hsq : (rawDifference A B S).natAbs ^ 2 = 4) :
    rawDifference A B S = 2 ∨ rawDifference A B S = -2 := by
  rcases rawDifference_eq_zero_or_two_or_neg_two A B S with hzero | htwo | hneg
  · simp [hzero] at hsq
  · exact Or.inl htwo
  · exact Or.inr hneg

def middleExcept (n j : ℕ) : Finset ℕ := (middleCoordinates n).erase j

@[simp] theorem mem_middleExcept {n j i : ℕ} :
    i ∈ middleExcept n j ↔ i ≠ j ∧ 1 ≤ i ∧ i < n - 2 := by
  simp [middleExcept]

theorem nearFullBase_insert {n j : ℕ} {R : Finset ℕ}
    (hj0 : j ≠ 0) (hjpen : j ≠ n - 2) :
    nearFullBase n (insert j R) = insert j (nearFullBase n R) := by
  ext i
  simp [nearFullBase, or_left_comm, or_assoc]

theorem translate_nearFullBase_insert {n j : ℕ} {R : Finset ℕ}
    (hj0 : j ≠ 0) (hjpen : j ≠ n - 2) :
    translate (nearFullBase n (insert j R)) 1 =
      insert (j + 1) (translate (nearFullBase n R) 1) := by
  rw [nearFullBase_insert hj0 hjpen]
  ext i
  simp [translate]

theorem distinguished_not_mem_nearFullBase {n : ℕ} (j : Fin n)
    (hjpos : 0 < j.val) (hjpen : j.val < n - 2) {R : Finset ℕ}
    (hR : R ⊆ middleExcept n j.val) :
    j.val ∉ nearFullBase n R := by
  have hj0 : j.val ≠ 0 := Nat.ne_of_gt hjpos
  have hjend : j.val ≠ n - 2 := Nat.ne_of_lt hjpen
  have hjR : j.val ∉ R := by
    intro h
    exact (mem_middleExcept.mp (hR h)).1 rfl
  simp [nearFullBase, hj0, hjend, hjR]

theorem succ_distinguished_not_mem_translated_nearFullBase {n : ℕ} (j : Fin n)
    (hjpos : 0 < j.val) (hjpen : j.val < n - 2) {R : Finset ℕ}
    (hR : R ⊆ middleExcept n j.val) :
    j.val + 1 ∉ translate (nearFullBase n R) 1 := by
  intro hmem
  rcases Finset.mem_image.mp hmem with ⟨i, hi, heq⟩
  have hi_eq : i = j.val := by omega
  subst i
  exact distinguished_not_mem_nearFullBase j hjpos hjpen hR hi

theorem nearFull_product_toggle_neg {n : ℕ} (hn : 4 ≤ n)
    (A B : Word n)
    (hinterior : ∀ i : Fin n, 0 < i.val → i.val < n - 1 → A i = B i)
    (j : Fin n) (hjpos : 0 < j.val) (hjpen : j.val < n - 2)
    (hadj : A j ≠ A ⟨j.val + 1, by omega⟩)
    {R : Finset ℕ} (hR : R ⊆ middleExcept n j.val) :
    rawDifference A B (nearFullBase n (insert j.val R)) *
        rawDifference A B (translate (nearFullBase n (insert j.val R)) 1) =
      -(rawDifference A B (nearFullBase n R) *
        rawDifference A B (translate (nearFullBase n R) 1)) := by
  have hnsub : n - 2 + 2 = n := Nat.sub_add_cancel (by omega)
  have hj0 : j.val ≠ 0 := Nat.ne_of_gt hjpos
  have hjend : j.val ≠ n - 2 := Nat.ne_of_lt hjpen
  have hjlast : j.val < n - 1 := by omega
  have hAjBj : A j = B j := hinterior j hjpos hjlast
  have hjsN : j.val + 1 < n := by omega
  let js : Fin n := ⟨j.val + 1, hjsN⟩
  have hjslast : js.val < n - 1 := by
    dsimp [js]
    omega
  have hAjsBjs : A js = B js := hinterior js (by dsimp [js]; omega) hjslast
  have hsign : letterSign A j.val * letterSign A (j.val + 1) = -1 := by
    simp only [letterSign_of_lt A j.isLt, letterSign_of_lt A hjsN]
    exact coinSign_mul_eq_neg_one_of_ne hadj
  rw [translate_nearFullBase_insert hj0 hjend,
    nearFullBase_insert hj0 hjend]
  rw [rawDifference_insert_of_word_eq A B (nearFullBase n R)
    (distinguished_not_mem_nearFullBase j hjpos hjpen hR) j.isLt hAjBj]
  rw [rawDifference_insert_of_word_eq A B
    (translate (nearFullBase n R) 1)
    (succ_distinguished_not_mem_translated_nearFullBase j hjpos hjpen hR)
    hjsN hAjsBjs]
  calc
    (letterSign A j.val * rawDifference A B (nearFullBase n R)) *
        (letterSign A (j.val + 1) *
          rawDifference A B (translate (nearFullBase n R) 1)) =
      (letterSign A j.val * letterSign A (j.val + 1)) *
        (rawDifference A B (nearFullBase n R) *
          rawDifference A B (translate (nearFullBase n R) 1)) := by ring
    _ = _ := by rw [hsign]; ring

def selectedTwoEndpointShape {n : ℕ} (A B : Word n) (j : ℕ)
    (R : Finset ℕ) : Finset ℕ :=
  if rawDifference A B (nearFullBase n R) *
      rawDifference A B (translate (nearFullBase n R) 1) = 4 then
    nearFullBase n R
  else nearFullBase n (insert j R)

theorem selectedTwoEndpointShape_square {n : ℕ} (hn : 4 ≤ n)
    (A B : Word n)
    (hinterior : ∀ i : Fin n, 0 < i.val → i.val < n - 1 → A i = B i)
    (hleft : A ⟨0, by omega⟩ ≠ B ⟨0, by omega⟩)
    (hright : A ⟨n - 1, by omega⟩ ≠ B ⟨n - 1, by omega⟩)
    (j : Fin n) (hjpos : 0 < j.val) (hjpen : j.val < n - 2)
    (hadj : A j ≠ A ⟨j.val + 1, by omega⟩)
    {R : Finset ℕ} (hR : R ⊆ middleExcept n j.val) :
    (shapeCoeff A B (selectedTwoEndpointShape A B j.val R)).natAbs ^ 2 = 16 := by
  have hRmid : R ⊆ middleCoordinates n := by
    intro i hi
    have hr := mem_middleExcept.mp (hR hi)
    exact mem_middleCoordinates.mpr ⟨hr.2.1, hr.2.2⟩
  have hinsmid : insert j.val R ⊆ middleCoordinates n := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact mem_middleCoordinates.mpr ⟨hjpos, hjpen⟩
    · exact hRmid hi
  have hsquares := nearFull_rawDifference_squares (by omega) A B hinterior
    hleft hright hRmid
  have hsquares' := nearFull_rawDifference_squares (by omega) A B hinterior
    hleft hright hinsmid
  let d0 := rawDifference A B (nearFullBase n R)
  let d1 := rawDifference A B (translate (nearFullBase n R) 1)
  have hd0 : d0 = 2 ∨ d0 = -2 :=
    rawDifference_eq_two_or_neg_two_of_square A B _ hsquares.1
  have hd1 : d1 = 2 ∨ d1 = -2 :=
    rawDifference_eq_two_or_neg_two_of_square A B _ hsquares.2
  unfold selectedTwoEndpointShape
  by_cases hprod : d0 * d1 = 4
  · rw [if_pos hprod, shapeCoeff_nearFullBase (by omega) A B hRmid]
    exact natAbs_add_sq_eq_sixteen_of_raw_product hd0 hd1 hprod
  · rw [if_neg hprod, shapeCoeff_nearFullBase (by omega) A B hinsmid]
    have hpm : d0 * d1 = -4 :=
      (product_eq_four_or_neg_four_of_raw_squares hd0 hd1).resolve_left hprod
    have htoggle := nearFull_product_toggle_neg hn A B hinterior j
      hjpos hjpen hadj hR
    have hprod' :
        rawDifference A B (nearFullBase n (insert j.val R)) *
          rawDifference A B (translate (nearFullBase n (insert j.val R)) 1) = 4 := by
      rw [htoggle, hpm]
      norm_num
    have hd0' := rawDifference_eq_two_or_neg_two_of_square A B _ hsquares'.1
    have hd1' := rawDifference_eq_two_or_neg_two_of_square A B _ hsquares'.2
    exact natAbs_add_sq_eq_sixteen_of_raw_product hd0' hd1' hprod'

def stripTwoEndpointShape (n j : ℕ) (S : Finset ℕ) : Finset ℕ :=
  ((S.erase 0).erase (n - 2)).erase j

theorem selectedTwoEndpointShape_injective {n : ℕ} (A B : Word n)
    (j : Fin n) (hjpos : 0 < j.val) (hjpen : j.val < n - 2)
    {R₁ R₂ : Finset ℕ}
    (hR₁ : R₁ ∈ (middleExcept n j.val).powerset)
    (hR₂ : R₂ ∈ (middleExcept n j.val).powerset)
    (heq : selectedTwoEndpointShape A B j.val R₁ =
      selectedTwoEndpointShape A B j.val R₂) : R₁ = R₂ := by
  have recover : ∀ {R : Finset ℕ}, R ⊆ middleExcept n j.val →
      stripTwoEndpointShape n j.val
        (selectedTwoEndpointShape A B j.val R) = R := by
    intro R hR
    have hR0 : 0 ∉ R := by
      intro h
      have hr := mem_middleExcept.mp (hR h)
      omega
    have hRpen : n - 2 ∉ R := by
      intro h
      have hr := mem_middleExcept.mp (hR h)
      omega
    have hRj : j.val ∉ R := by
      intro h
      exact (mem_middleExcept.mp (hR h)).1 rfl
    have hj0 : j.val ≠ 0 := Nat.ne_of_gt hjpos
    have hjend : j.val ≠ n - 2 := Nat.ne_of_lt hjpen
    unfold stripTwoEndpointShape selectedTwoEndpointShape
    split
    · ext i
      simp only [nearFullBase, Finset.mem_erase, Finset.mem_insert]
      constructor
      · rintro ⟨hij, hipen, hi0, hi0eq | hipeneq | hiR⟩
        · exact (hi0 hi0eq).elim
        · exact (hipen hipeneq).elim
        · exact hiR
      · intro hiR
        refine ⟨?_, ?_, ?_, Or.inr (Or.inr hiR)⟩
        · intro e; subst i; exact hRj hiR
        · intro e; subst i; exact hRpen hiR
        · intro e; subst i; exact hR0 hiR
    · ext i
      simp only [nearFullBase, Finset.mem_erase, Finset.mem_insert]
      constructor
      · rintro ⟨hij, hipen, hi0, hi0eq | hipeneq | hijeq | hiR⟩
        · exact (hi0 hi0eq).elim
        · exact (hipen hipeneq).elim
        · exact (hij hijeq).elim
        · exact hiR
      · intro hiR
        refine ⟨?_, ?_, ?_, Or.inr (Or.inr (Or.inr hiR))⟩
        · intro e; subst i; exact hRj hiR
        · intro e; subst i; exact hRpen hiR
        · intro e; subst i; exact hR0 hiR
  have hrec₁ := recover (Finset.mem_powerset.mp hR₁)
  have hrec₂ := recover (Finset.mem_powerset.mp hR₂)
  rw [← hrec₁, ← hrec₂, heq]

theorem card_middleExcept {n : ℕ} (hn : 4 ≤ n) (j : Fin n)
    (hjpos : 0 < j.val) (hjpen : j.val < n - 2) :
    #(middleExcept n j.val) = n - 4 := by
  have hjmem : j.val ∈ middleCoordinates n :=
    mem_middleCoordinates.mpr ⟨hjpos, hjpen⟩
  rw [middleExcept, Finset.card_erase_of_mem hjmem]
  simp [middleCoordinates]
  omega

theorem rawEnergy_ge_of_two_endpoint_adjacency_disagreement {n : ℕ} (hn : 4 ≤ n)
    (A B : Word n)
    (hinterior : ∀ i : Fin n, 0 < i.val → i.val < n - 1 → A i = B i)
    (hleft : A ⟨0, by omega⟩ ≠ B ⟨0, by omega⟩)
    (hright : A ⟨n - 1, by omega⟩ ≠ B ⟨n - 1, by omega⟩)
    (j : Fin n) (hjpos : 0 < j.val) (hjpen : j.val < n - 2)
    (hadj : A j ≠ A ⟨j.val + 1, by omega⟩) :
    16 * 2 ^ (n - 4) ≤ rawEnergy A B := by
  let selected := (middleExcept n j.val).powerset.image
    (selectedTwoEndpointShape A B j.val)
  have hsubset : selected ⊆ shapes n := by
    intro S hS
    rcases Finset.mem_image.mp hS with ⟨R, hR, rfl⟩
    have hRsub := Finset.mem_powerset.mp hR
    unfold selectedTwoEndpointShape
    split
    · exact nearFullBase_mem_shapes (by omega) (by
        intro i hi
        have hr := mem_middleExcept.mp (hRsub hi)
        exact mem_middleCoordinates.mpr ⟨hr.2.1, hr.2.2⟩)
    · exact nearFullBase_mem_shapes (by omega) (by
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact mem_middleCoordinates.mpr ⟨hjpos, hjpen⟩
        · have hr := mem_middleExcept.mp (hRsub hi)
          exact mem_middleCoordinates.mpr ⟨hr.2.1, hr.2.2⟩)
  have hcard : #selected = 2 ^ (n - 4) := by
    have hinj : Set.InjOn (selectedTwoEndpointShape A B j.val)
        (middleExcept n j.val).powerset := by
      intro R₁ hR₁ R₂ hR₂ heq
      exact selectedTwoEndpointShape_injective A B j hjpos hjpen hR₁ hR₂ heq
    rw [Finset.card_image_of_injOn hinj]
    simp [card_middleExcept hn j hjpos hjpen]
  have hselected :
      (∑ S ∈ selected, (shapeCoeff A B S).natAbs ^ 2) =
        16 * 2 ^ (n - 4) := by
    calc
      (∑ S ∈ selected, (shapeCoeff A B S).natAbs ^ 2) =
          ∑ _S ∈ selected, 16 := by
        apply Finset.sum_congr rfl
        intro S hS
        rcases Finset.mem_image.mp hS with ⟨R, hR, rfl⟩
        exact selectedTwoEndpointShape_square hn A B hinterior hleft hright
          j hjpos hjpen hadj (Finset.mem_powerset.mp hR)
      _ = 16 * #selected := by simp [mul_comm]
      _ = 16 * 2 ^ (n - 4) := by rw [hcard]
  rw [rawEnergy, ← hselected]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
    intro S hS hnot
    exact Nat.zero_le _)

#print axioms nearFull_product_toggle_neg
#print axioms selectedTwoEndpointShape_square
#print axioms rawEnergy_ge_of_two_endpoint_adjacency_disagreement

end LittMostUnfairBetWalsh
