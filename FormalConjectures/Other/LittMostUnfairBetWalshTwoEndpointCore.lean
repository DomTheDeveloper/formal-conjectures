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

import FormalConjectures.Other.LittMostUnfairBetWalshOneEndpointGap

/-!
# Near-full shapes for the two-endpoint Litt gap

For words agreeing internally and differing at both endpoints, the useful
shapes span coordinates `0` through `n-2`. They have exactly two valid
translations, at offsets zero and one, and both raw coefficients are `±2`.
-/

set_option autoImplicit false

namespace LittMostUnfairBetWalsh

open Finset
open LittMostUnfairBet

/-- Coordinates strictly between `0` and `n-2`. -/
def middleCoordinates (n : ℕ) : Finset ℕ := Finset.Ico 1 (n - 2)

@[simp] theorem mem_middleCoordinates {n i : ℕ} :
    i ∈ middleCoordinates n ↔ 1 ≤ i ∧ i < n - 2 := by
  simp [middleCoordinates]

/-- A shape spanning `0` through `n-2`. -/
def nearFullBase (n : ℕ) (R : Finset ℕ) : Finset ℕ :=
  insert 0 (insert (n - 2) R)

@[simp] theorem zero_mem_nearFullBase (n : ℕ) (R : Finset ℕ) :
    0 ∈ nearFullBase n R := by simp [nearFullBase]

@[simp] theorem penultimate_mem_nearFullBase (n : ℕ) (R : Finset ℕ) :
    n - 2 ∈ nearFullBase n R := by simp [nearFullBase]

/-- A near-full base lies in the coordinate range. -/
theorem nearFullBase_subset_range {n : ℕ} (hn : 3 ≤ n) {R : Finset ℕ}
    (hR : R ⊆ middleCoordinates n) :
    nearFullBase n R ⊆ Finset.range n := by
  intro i hi
  simp only [nearFullBase, Finset.mem_insert] at hi
  rcases hi with rfl | rfl | hi
  · simp; omega
  · simp; omega
  · have hr := mem_middleCoordinates.mp (hR hi)
    simp; omega

/-- Every near-full base is a normalized shape. -/
theorem nearFullBase_mem_shapes {n : ℕ} (hn : 3 ≤ n) {R : Finset ℕ}
    (hR : R ⊆ middleCoordinates n) :
    nearFullBase n R ∈ shapes n := by
  exact mem_shapes.mpr ⟨nearFullBase_subset_range hn hR,
    zero_mem_nearFullBase n R⟩

/-- Near-full bases have exactly the translations zero and one. -/
theorem translations_nearFullBase {n : ℕ} (hn : 3 ≤ n) {R : Finset ℕ}
    (hR : R ⊆ middleCoordinates n) :
    translations n (nearFullBase n R) = {0, 1} := by
  ext t
  constructor
  · intro ht
    have ht' := mem_translations.mp ht
    have hmax := ht'.2 (n - 2) (penultimate_mem_nearFullBase n R)
    have ht01 : t = 0 ∨ t = 1 := by omega
    rcases ht01 with rfl | rfl <;> simp
  · intro ht
    have ht01 : t = 0 ∨ t = 1 := by simpa using ht
    rcases ht01 with rfl | rfl
    · apply mem_translations.mpr
      refine ⟨by omega, ?_⟩
      intro i hi
      exact Finset.mem_range.mp (nearFullBase_subset_range hn hR hi)
    · apply mem_translations.mpr
      refine ⟨by omega, ?_⟩
      intro i hi
      simp only [nearFullBase, Finset.mem_insert] at hi
      rcases hi with rfl | rfl | hi
      · omega
      · omega
      · have hr := mem_middleCoordinates.mp (hR hi)
        omega

/-- The coefficient of a near-full shape is the sum of its two raw translates. -/
theorem shapeCoeff_nearFullBase {n : ℕ} (hn : 3 ≤ n)
    (A B : Word n) {R : Finset ℕ} (hR : R ⊆ middleCoordinates n) :
    shapeCoeff A B (nearFullBase n R) =
      rawDifference A B (nearFullBase n R) +
        rawDifference A B (translate (nearFullBase n R) 1) := by
  rw [shapeCoeff, translations_nearFullBase hn hR]
  simp

/-- Inserting an equal-coordinate letter multiplies a raw difference by its sign. -/
theorem rawDifference_insert_of_word_eq {n j : ℕ} (A B : Word n)
    (S : Finset ℕ) (hjS : j ∉ S) (hj : j < n)
    (heq : A ⟨j, hj⟩ = B ⟨j, hj⟩) :
    rawDifference A B (insert j S) =
      letterSign A j * rawDifference A B S := by
  have hsign : letterSign B j = letterSign A j := by
    simp [letterSign, hj, heq]
  rw [rawDifference, natMonomial_insert A S hjS,
    natMonomial_insert B S hjS, hsign]
  ring

/-- A near-full base includes only the left endpoint among the two endpoints. -/
theorem nearFullBase_monomial_mul_eq_neg_one {n : ℕ} (hn : 3 ≤ n)
    (A B : Word n)
    (hinterior : ∀ i : Fin n, 0 < i.val → i.val < n - 1 → A i = B i)
    (hleft : A ⟨0, by omega⟩ ≠ B ⟨0, by omega⟩)
    {R : Finset ℕ} (hR : R ⊆ middleCoordinates n) :
    natMonomial A (nearFullBase n R) *
      natMonomial B (nearFullBase n R) = -1 := by
  have hR0 : 0 ∉ R := by
    intro h
    have hr := mem_middleCoordinates.mp (hR h)
    omega
  have hRpen : n - 2 ∉ R := by
    intro h
    have hr := mem_middleCoordinates.mp (hR h)
    omega
  have h0pen : 0 ≠ n - 2 := by omega
  have hprodR : ∏ i ∈ R, (letterSign A i * letterSign B i) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    have hr := mem_middleCoordinates.mp (hR hi)
    have hiN : i < n := lt_of_lt_of_le hr.2 (Nat.sub_le n 2)
    have hiLast : i < n - 1 := by omega
    apply letterSign_mul_eq_one_of_word_eq A B hiN
    exact hinterior ⟨i, hiN⟩ hr.1 hiLast
  have hpenN : n - 2 < n := by omega
  have hpenPos : 0 < n - 2 := by omega
  have hpenLast : n - 2 < n - 1 := by omega
  have hpen := letterSign_mul_eq_one_of_word_eq A B
    (i := n - 2) hpenN
    (hinterior ⟨n - 2, hpenN⟩ hpenPos hpenLast)
  have hleftSign := letterSign_mul_eq_neg_one_of_word_ne A B
    (j := 0) (by omega) hleft
  unfold natMonomial nearFullBase
  rw [← Finset.prod_mul_distrib]
  rw [Finset.prod_insert (by simp [h0pen, hR0])]
  rw [Finset.prod_insert hRpen]
  rw [hprodR, hleftSign, hpen]
  norm_num

/-- The translated near-full base includes only the right endpoint. -/
theorem translated_nearFullBase_monomial_mul_eq_neg_one {n : ℕ} (hn : 3 ≤ n)
    (A B : Word n)
    (hinterior : ∀ i : Fin n, 0 < i.val → i.val < n - 1 → A i = B i)
    (hright : A ⟨n - 1, by omega⟩ ≠ B ⟨n - 1, by omega⟩)
    {R : Finset ℕ} (hR : R ⊆ middleCoordinates n) :
    natMonomial A (translate (nearFullBase n R) 1) *
      natMonomial B (translate (nearFullBase n R) 1) = -1 := by
  have hsub : translate (nearFullBase n R) 1 ⊆ Finset.range n := by
    intro i hi
    rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
    simp only [nearFullBase, Finset.mem_insert] at hj
    rcases hj with rfl | rfl | hj
    · simp; omega
    · simp; omega
    · have hr := mem_middleCoordinates.mp (hR hj)
      simp; omega
  have hcontainsLast : n - 1 ∈ translate (nearFullBase n R) 1 := by
    exact Finset.mem_image.mpr ⟨n - 2, penultimate_mem_nearFullBase n R, by omega⟩
  have hprodInterior :
      ∏ i ∈ (translate (nearFullBase n R) 1).erase (n - 1),
        (letterSign A i * letterSign B i) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    have hiSet := Finset.mem_of_mem_erase hi
    have hine : i ≠ n - 1 := Finset.ne_of_mem_erase hi
    have hirange : i < n := Finset.mem_range.mp (hsub hiSet)
    have hipos : 0 < i := by
      rcases Finset.mem_image.mp hiSet with ⟨j, hj, rfl⟩
      exact Nat.zero_lt_succ j
    have hile : i ≤ n - 1 := by omega
    have hilast : i < n - 1 := lt_of_le_of_ne hile hine
    apply letterSign_mul_eq_one_of_word_eq A B hirange
    exact hinterior ⟨i, hirange⟩ hipos hilast
  have hrightSign := letterSign_mul_eq_neg_one_of_word_ne A B
    (j := n - 1) (by omega) hright
  unfold natMonomial
  rw [← Finset.prod_mul_distrib]
  rw [← Finset.prod_erase_mul _ _ hcontainsLast]
  rw [hprodInterior, hrightSign]
  norm_num

/-- Both raw coefficients of a two-endpoint near-full shape have square `4`. -/
theorem nearFull_rawDifference_squares {n : ℕ} (hn : 3 ≤ n)
    (A B : Word n)
    (hinterior : ∀ i : Fin n, 0 < i.val → i.val < n - 1 → A i = B i)
    (hleft : A ⟨0, by omega⟩ ≠ B ⟨0, by omega⟩)
    (hright : A ⟨n - 1, by omega⟩ ≠ B ⟨n - 1, by omega⟩)
    {R : Finset ℕ} (hR : R ⊆ middleCoordinates n) :
    (rawDifference A B (nearFullBase n R)).natAbs ^ 2 = 4 ∧
      (rawDifference A B (translate (nearFullBase n R) 1)).natAbs ^ 2 = 4 := by
  constructor
  · exact rawDifference_natAbs_sq_eq_four_of_mul_eq_neg_one A B _
      (nearFullBase_monomial_mul_eq_neg_one hn A B hinterior hleft hR)
  · exact rawDifference_natAbs_sq_eq_four_of_mul_eq_neg_one A B _
      (translated_nearFullBase_monomial_mul_eq_neg_one hn A B hinterior hright hR)

#print axioms translations_nearFullBase
#print axioms shapeCoeff_nearFullBase
#print axioms nearFull_rawDifference_squares

end LittMostUnfairBetWalsh
