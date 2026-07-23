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

import FormalConjectures.Other.LittMostUnfairBetWalshTwoEndpointToggle
import FormalConjectures.Other.LittMostUnfairBetReversal

/-!
# Constant-interior completion of the two-endpoint Litt gap
-/

set_option autoImplicit false

namespace LittMostUnfairBetWalsh

open Finset
open LittMostUnfairBet

/-- Distinct Boolean values are complements. -/
theorem bool_eq_not_of_ne {a b : Bool} (h : a ≠ b) : b = !a := by
  cases a <;> cases b <;> simp at h ⊢

/-- On a constant interior, a monomial depends only on cardinality. -/
theorem natMonomial_interior_constant {n : ℕ} (A : Word n) (c : Bool)
    (hconst : ∀ i : Fin n, 0 < i.val → i.val < n - 1 → A i = c)
    (S : Finset ℕ) (hS : S ⊆ interiorCoordinates n) :
    natMonomial A S = coinSign c ^ #S := by
  unfold natMonomial
  calc
    (∏ i ∈ S, letterSign A i) = ∏ _i ∈ S, coinSign c := by
      apply Finset.prod_congr rfl
      intro i hi
      have hsi := mem_interiorCoordinates.mp (hS hi)
      have hiN : i < n := by omega
      have hval := hconst ⟨i, hiN⟩ hsi.1 hsi.2
      rw [letterSign_of_lt A hiN, hval]
    _ = coinSign c ^ #S := by simp

/-- Translating a middle subset by one remains inside the interior. -/
theorem translate_middle_subset_interior {n : ℕ} {R : Finset ℕ}
    (hR : R ⊆ middleCoordinates n) :
    translate R 1 ⊆ interiorCoordinates n := by
  intro i hi
  rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
  have hr := mem_middleCoordinates.mp (hR hj)
  exact mem_interiorCoordinates.mpr ⟨by omega, by omega⟩

/-- Explicit form of the translated near-full base. -/
theorem translate_nearFullBase_eq {n : ℕ} (hn : 2 ≤ n) {R : Finset ℕ} :
    translate (nearFullBase n R) 1 =
      insert 1 (insert (n - 1) (translate R 1)) := by
  have hsub : n - 2 + 1 = n - 1 := by omega
  ext i
  simp [translate, nearFullBase, hsub]

/-- With constant interior and equal endpoints, the two near-full monomials agree. -/
theorem nearFull_monomial_eq_translated {n : ℕ} (hn : 3 ≤ n)
    (A : Word n) (c : Bool)
    (hconst : ∀ i : Fin n, 0 < i.val → i.val < n - 1 → A i = c)
    (hends : A ⟨0, by omega⟩ = A ⟨n - 1, by omega⟩)
    {R : Finset ℕ} (hR : R ⊆ middleCoordinates n) :
    natMonomial A (nearFullBase n R) =
      natMonomial A (translate (nearFullBase n R) 1) := by
  have hR0 : 0 ∉ R := by
    intro h
    have hr := mem_middleCoordinates.mp (hR h)
    omega
  have hRpen : n - 2 ∉ R := by
    intro h
    have hr := mem_middleCoordinates.mp (hR h)
    omega
  have hTR1 : 1 ∉ translate R 1 := by
    intro h
    rcases Finset.mem_image.mp h with ⟨j, hj, heq⟩
    have hr := mem_middleCoordinates.mp (hR hj)
    omega
  have hTRlast : n - 1 ∉ translate R 1 := by
    intro h
    rcases Finset.mem_image.mp h with ⟨j, hj, heq⟩
    have hr := mem_middleCoordinates.mp (hR hj)
    omega
  have h0pen : 0 ≠ n - 2 := by omega
  have h1last : 1 ≠ n - 1 := by omega
  have hRint : R ⊆ interiorCoordinates n := by
    intro i hi
    have hr := mem_middleCoordinates.mp (hR hi)
    exact mem_interiorCoordinates.mpr ⟨hr.1, by omega⟩
  have hTRint := translate_middle_subset_interior hR
  have hn2lt : n - 2 < n := by omega
  have hn2pos : 0 < n - 2 := by omega
  have hn2int : n - 2 < n - 1 := by omega
  have hpen : A ⟨n - 2, hn2lt⟩ = c := hconst _ hn2pos hn2int
  have h1lt : 1 < n := by omega
  have h2pred : 2 ≤ n - 1 := Nat.le_sub_of_add_le hn
  have h1int : 1 < n - 1 := Nat.lt_of_succ_le h2pred
  have hone : A ⟨1, h1lt⟩ = c := hconst _ (by omega) h1int
  have hnlast : n - 1 < n :=
    Nat.sub_lt (by omega : 0 < n) (by norm_num : 0 < 1)
  rw [translate_nearFullBase_eq (by omega)]
  change natMonomial A (insert 0 (insert (n - 2) R)) =
    natMonomial A (insert 1 (insert (n - 1) (translate R 1)))
  rw [natMonomial_insert A (insert (n - 2) R) (by simp [h0pen, hR0])]
  rw [natMonomial_insert A R hRpen]
  rw [natMonomial_insert A (insert (n - 1) (translate R 1))
    (by simp [h1last, hTR1])]
  rw [natMonomial_insert A (translate R 1) hTRlast]
  rw [natMonomial_interior_constant A c hconst R hRint]
  rw [natMonomial_interior_constant A c hconst (translate R 1) hTRint]
  rw [card_translate]
  rw [letterSign_of_lt A (by omega : 0 < n)]
  rw [letterSign_of_lt A hn2lt]
  rw [letterSign_of_lt A h1lt]
  rw [letterSign_of_lt A hnlast]
  rw [hpen, hone, hends]
  ring

/-- Raw difference equals twice the left monomial when the monomial product is `-1`. -/
theorem rawDifference_eq_two_mul_left_of_mul_eq_neg_one {n : ℕ}
    (A B : Word n) (S : Finset ℕ)
    (hprod : natMonomial A S * natMonomial B S = -1) :
    rawDifference A B S = 2 * natMonomial A S := by
  rcases natMonomial_eq_one_or_neg_one A S with hA | hA <;>
    rcases natMonomial_eq_one_or_neg_one B S with hB | hB <;>
    simp [rawDifference, hA, hB] at hprod ⊢

/-- Every near-full shape contributes `16` when the common interior is constant
and the endpoints of the first word agree. -/
theorem nearFull_shape_square_of_constant_interior_equal_endpoints {n : ℕ}
    (hn : 3 ≤ n) (A B : Word n) (c : Bool)
    (hinterior : ∀ i : Fin n, 0 < i.val → i.val < n - 1 → A i = B i)
    (hconst : ∀ i : Fin n, 0 < i.val → i.val < n - 1 → A i = c)
    (hleft : A ⟨0, by omega⟩ ≠ B ⟨0, by omega⟩)
    (hright : A ⟨n - 1, by omega⟩ ≠ B ⟨n - 1, by omega⟩)
    (hends : A ⟨0, by omega⟩ = A ⟨n - 1, by omega⟩)
    {R : Finset ℕ} (hR : R ⊆ middleCoordinates n) :
    (shapeCoeff A B (nearFullBase n R)).natAbs ^ 2 = 16 := by
  rw [shapeCoeff_nearFullBase hn A B hR]
  have hprod0 := nearFullBase_monomial_mul_eq_neg_one hn A B
    hinterior hleft hR
  have hprod1 := translated_nearFullBase_monomial_mul_eq_neg_one hn A B
    hinterior hright hR
  rw [rawDifference_eq_two_mul_left_of_mul_eq_neg_one A B _ hprod0]
  rw [rawDifference_eq_two_mul_left_of_mul_eq_neg_one A B _ hprod1]
  rw [nearFull_monomial_eq_translated hn A c hconst hends hR]
  rcases natMonomial_eq_one_or_neg_one A (translate (nearFullBase n R) 1)
    with h | h <;> simp [h]

/-- Constant interior with equal endpoints gives a strong raw-energy gap. -/
theorem rawEnergy_ge_of_constant_interior_equal_endpoints {n : ℕ}
    (hn : 3 ≤ n) (A B : Word n) (c : Bool)
    (hinterior : ∀ i : Fin n, 0 < i.val → i.val < n - 1 → A i = B i)
    (hconst : ∀ i : Fin n, 0 < i.val → i.val < n - 1 → A i = c)
    (hleft : A ⟨0, by omega⟩ ≠ B ⟨0, by omega⟩)
    (hright : A ⟨n - 1, by omega⟩ ≠ B ⟨n - 1, by omega⟩)
    (hends : A ⟨0, by omega⟩ = A ⟨n - 1, by omega⟩) :
    16 * 2 ^ (n - 3) ≤ rawEnergy A B := by
  let selected := (middleCoordinates n).powerset.image (nearFullBase n)
  have hsubset : selected ⊆ shapes n := by
    intro S hS
    rcases Finset.mem_image.mp hS with ⟨R, hR, rfl⟩
    exact nearFullBase_mem_shapes hn (Finset.mem_powerset.mp hR)
  have hinj : Set.InjOn (nearFullBase n) (middleCoordinates n).powerset := by
    intro R₁ hR₁ R₂ hR₂ heq
    have recover : ∀ {R : Finset ℕ}, R ⊆ middleCoordinates n →
        ((nearFullBase n R).erase 0).erase (n - 2) = R := by
      intro R hR
      have hR0 : 0 ∉ R := by
        intro h
        have hr := mem_middleCoordinates.mp (hR h)
        omega
      have hRpen : n - 2 ∉ R := by
        intro h
        have hr := mem_middleCoordinates.mp (hR h)
        omega
      ext i
      simp only [Finset.mem_erase, Finset.mem_insert, nearFullBase]
      constructor
      · rintro ⟨hine, hi0, hi0eq | hipenEq | hiR⟩
        · exact (hi0 hi0eq).elim
        · exact (hine hipenEq).elim
        · exact hiR
      · intro hiR
        refine ⟨?_, ?_, Or.inr (Or.inr hiR)⟩
        · intro e; subst i; exact hRpen hiR
        · intro e; subst i; exact hR0 hiR
    rw [← recover (Finset.mem_powerset.mp hR₁),
      ← recover (Finset.mem_powerset.mp hR₂), heq]
  have hcard : #selected = 2 ^ (n - 3) := by
    rw [Finset.card_image_of_injOn hinj]
    simp [middleCoordinates]
    omega
  have hselected :
      (∑ S ∈ selected, (shapeCoeff A B S).natAbs ^ 2) =
        16 * 2 ^ (n - 3) := by
    calc
      (∑ S ∈ selected, (shapeCoeff A B S).natAbs ^ 2) =
          ∑ _S ∈ selected, 16 := by
        apply Finset.sum_congr rfl
        intro S hS
        rcases Finset.mem_image.mp hS with ⟨R, hR, rfl⟩
        exact nearFull_shape_square_of_constant_interior_equal_endpoints hn
          A B c hinterior hconst hleft hright hends
          (Finset.mem_powerset.mp hR)
      _ = 16 * #selected := by simp [mul_comm]
      _ = 16 * 2 ^ (n - 3) := by rw [hcard]
  rw [rawEnergy, ← hselected]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
    intro S hS hnot
    exact Nat.zero_le _)

/-- Constant common interior with opposite endpoints makes the second word the reversal. -/
theorem eq_reverse_of_constant_interior_opposite_endpoints {n : ℕ}
    (hn : 3 ≤ n) (A B : Word n) (c : Bool)
    (hinterior : ∀ i : Fin n, 0 < i.val → i.val < n - 1 → A i = B i)
    (hconst : ∀ i : Fin n, 0 < i.val → i.val < n - 1 → A i = c)
    (hleft : A ⟨0, by omega⟩ ≠ B ⟨0, by omega⟩)
    (hright : A ⟨n - 1, by omega⟩ ≠ B ⟨n - 1, by omega⟩)
    (hopposite : A ⟨0, by omega⟩ ≠ A ⟨n - 1, by omega⟩) :
    B = reverseWord A := by
  funext i
  by_cases hi0 : i.val = 0
  · have hi : i = ⟨0, by omega⟩ := Fin.ext hi0
    rw [hi]
    have hB0 := bool_eq_not_of_ne hleft
    have hAlast := bool_eq_not_of_ne hopposite
    change B (⟨0, by omega⟩ : Fin n) = A ((⟨0, by omega⟩ : Fin n).rev)
    have hrev : ((⟨0, by omega⟩ : Fin n).rev) = ⟨n - 1, by omega⟩ := by
      apply Fin.ext
      simp
    rw [hrev]
    exact hB0.trans hAlast.symm
  · by_cases hilast : i.val = n - 1
    · have hi : i = ⟨n - 1, by omega⟩ := Fin.ext hilast
      rw [hi]
      have hBlast := bool_eq_not_of_ne hright
      have hA0 : A ⟨0, by omega⟩ = !A ⟨n - 1, by omega⟩ := by
        simpa using (bool_eq_not_of_ne hopposite).symm
      change B (⟨n - 1, by omega⟩ : Fin n) =
        A ((⟨n - 1, by omega⟩ : Fin n).rev)
      have hcancel : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
      have hrev : ((⟨n - 1, by omega⟩ : Fin n).rev) = ⟨0, by omega⟩ := by
        apply Fin.ext
        change n - (n - 1 + 1) = 0
        rw [hcancel]
        simp
      rw [hrev]
      exact hBlast.trans hA0.symm
    · have hipos : 0 < i.val := by omega
      have hiint : i.val < n - 1 := by omega
      have hirevpos : 0 < i.rev.val := by
        change 0 < n - (i.val + 1)
        omega
      have hirevint : i.rev.val < n - 1 := by
        change n - (i.val + 1) < n - 1
        omega
      change B i = A i.rev
      rw [← hinterior i hipos hiint]
      rw [hconst i hipos hiint]
      rw [hconst i.rev hirevpos hirevint]

/-- In the opposite-endpoint constant-interior branch the numerator vanishes. -/
theorem selfOverlapDelta_eq_zero_of_constant_interior_opposite_endpoints {n : ℕ}
    (hn : 3 ≤ n) (A B : Word n) (c : Bool)
    (hinterior : ∀ i : Fin n, 0 < i.val → i.val < n - 1 → A i = B i)
    (hconst : ∀ i : Fin n, 0 < i.val → i.val < n - 1 → A i = c)
    (hleft : A ⟨0, by omega⟩ ≠ B ⟨0, by omega⟩)
    (hright : A ⟨n - 1, by omega⟩ ≠ B ⟨n - 1, by omega⟩)
    (hopposite : A ⟨0, by omega⟩ ≠ A ⟨n - 1, by omega⟩) :
    selfOverlapDelta A B = 0 := by
  rw [eq_reverse_of_constant_interior_opposite_endpoints hn A B c
    hinterior hconst hleft hright hopposite]
  exact selfOverlapDelta_reverse A

#print axioms rawEnergy_ge_of_constant_interior_equal_endpoints
#print axioms eq_reverse_of_constant_interior_opposite_endpoints
#print axioms selfOverlapDelta_eq_zero_of_constant_interior_opposite_endpoints

end LittMostUnfairBetWalsh
