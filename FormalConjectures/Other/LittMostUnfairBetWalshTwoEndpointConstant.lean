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

import FormalConjectures.Other.LittMostUnfairBetWalshToggle
import FormalConjectures.Other.LittMostUnfairBetWalshReversal

/-!
# Constant-interior two-endpoint Litt branch
-/

set_option autoImplicit false

namespace LittMostUnfairBetWalsh

open Finset
open LittMostUnfairBet

/-- Coordinates strictly between the endpoints. -/
def interiorCoordinates (n : ℕ) : Finset ℕ := (Finset.range (n - 1)).erase 0

@[simp] theorem mem_interiorCoordinates {n i : ℕ} :
    i ∈ interiorCoordinates n ↔ 0 < i ∧ i < n - 1 := by
  simp [interiorCoordinates]

/-- The near-full coordinate block used in the constant-interior branch. -/
def nearFullBase (n : ℕ) (R : Finset ℕ) : Finset ℕ := insert 0 (insert (n - 2) R)

/-- Middle-coordinate subsets translate into interior-coordinate subsets. -/
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
  rw [natMonomial_insert A (insert (n - 1) (translate R 1)) (by simp [h1last, hTR1])]
  rw [natMonomial_insert A (translate R 1) hTRlast]
  rw [hpen, hone]
  have hmon : natMonomial A R = natMonomial A (translate R 1) := by
    unfold natMonomial
    apply Finset.prod_bij (fun i _ => i + 1)
    · intro i hi
      exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
    · intro i hi j hj hij
      omega
    · intro j hj
      rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
      exact ⟨i, hi, rfl⟩
    · intro i hi
      have hiR := mem_middleCoordinates.mp (hR hi)
      have hiR' := mem_middleCoordinates.mp (hR hi)
      have hiN : i < n := by omega
      have hi1N : i + 1 < n := by omega
      have hiInt : 0 < i ∧ i < n - 1 := ⟨hiR.1, by omega⟩
      have hi1Int : 0 < i + 1 ∧ i + 1 < n - 1 := ⟨by omega, hiR'.2⟩
      rw [letterSign_of_lt A hiN, letterSign_of_lt A hi1N]
      rw [hconst ⟨i, hiN⟩ hiInt.1 hiInt.2]
      rw [hconst ⟨i + 1, hi1N⟩ hi1Int.1 hi1Int.2]
  rw [hmon]
  rw [hends]
  ring

/-- The near-full shape coefficient vanishes in the constant-interior/equal-endpoint branch. -/
theorem shapeCoeff_nearFull_eq_zero {n : ℕ} (hn : 3 ≤ n)
    (A B : Word n)
    (cA cB : Bool)
    (hA : ∀ i : Fin n, 0 < i.val → i.val < n - 1 → A i = cA)
    (hB : ∀ i : Fin n, 0 < i.val → i.val < n - 1 → B i = cB)
    (hAends : A ⟨0, by omega⟩ = A ⟨n - 1, by omega⟩)
    (hBends : B ⟨0, by omega⟩ = B ⟨n - 1, by omega⟩)
    {R : Finset ℕ} (hR : R ⊆ middleCoordinates n) :
    shapeCoeff A B (nearFullBase n R) = 0 := by
  rw [shapeCoeff_nearFullBase (by omega)]
  rw [nearFull_monomial_eq_translated hn A cA hA hAends hR]
  rw [nearFull_monomial_eq_translated hn B cB hB hBends hR]
  ring

/-- Raw energy upper bound in the constant-interior/equal-endpoint branch. -/
theorem rawEnergy_le_of_constant_interior_equal_endpoints {n : ℕ} (hn : 3 ≤ n)
    (A B : Word n)
    (cA cB : Bool)
    (hA : ∀ i : Fin n, 0 < i.val → i.val < n - 1 → A i = cA)
    (hB : ∀ i : Fin n, 0 < i.val → i.val < n - 1 → B i = cB)
    (hAends : A ⟨0, by omega⟩ = A ⟨n - 1, by omega⟩)
    (hBends : B ⟨0, by omega⟩ = B ⟨n - 1, by omega⟩) :
    rawEnergy A B ≤ 2 ^ (n + 1) - 4 * 2 ^ (n - 3) := by
  have hzero : ∀ R ∈ (middleCoordinates n).powerset,
      (shapeCoeff A B (nearFullBase n R)).natAbs ^ 2 = 0 := by
    intro R hR
    rw [shapeCoeff_nearFull_eq_zero hn A B cA cB hA hB hAends hBends
      (Finset.mem_powerset.mp hR)]
    norm_num
  have hfamily :
      (∑ R ∈ (middleCoordinates n).powerset,
          (shapeCoeff A B (nearFullBase n R)).natAbs ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro R hR
    exact hzero R hR
  have hsub :
      ∑ R ∈ (middleCoordinates n).powerset,
        (shapeCoeff A B (nearFullBase n R)).natAbs ^ 2 ≤ rawEnergy A B := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (by
      intro S hS
      rcases Finset.mem_image.mp hS with ⟨R, hR, rfl⟩
      exact nearFullBase_mem_shapes (by omega) (Finset.mem_powerset.mp hR)) (by
        intro S hS hnot
        exact Nat.zero_le _)
  have htotal := rawEnergy_le_universal A B
  rw [hfamily] at hsub
  have hcard : #(middleCoordinates n) = n - 3 := by
    simp [middleCoordinates]
    omega
  have hmissing : 4 * 2 ^ (n - 3) ≤ 2 ^ (n + 1) - rawEnergy A B := by
    have hpow : 4 * 2 ^ (n - 3) = 2 ^ (n - 1) := by
      rw [show n - 1 = (n - 3) + 2 by omega]
      simp [pow_add]
      ring
    rw [hpow]
    omega
  omega

/-- The signed self-overlap difference vanishes in the constant-interior/opposite-endpoint branch. -/
theorem selfOverlapDelta_eq_zero_of_constant_interior_opposite_endpoints {n : ℕ} (hn : 3 ≤ n)
    (A B : Word n)
    (cA cB : Bool)
    (hA : ∀ i : Fin n, 0 < i.val → i.val < n - 1 → A i = cA)
    (hB : ∀ i : Fin n, 0 < i.val → i.val < n - 1 → B i = cB)
    (hAends : A ⟨0, by omega⟩ ≠ A ⟨n - 1, by omega⟩)
    (hBends : B ⟨0, by omega⟩ ≠ B ⟨n - 1, by omega⟩) :
    selfOverlapDelta A B = 0 := by
  have hrevA : (reverseWord A) = A := by
    funext i
    by_cases hi0 : i.val = 0
    · subst i
      have hrev : ((⟨0, by omega⟩ : Fin n).rev) = ⟨n - 1, by omega⟩ := by
        apply Fin.ext
        simp
      rw [reverseWord, hrev]
      have hbool := Bool.eq_false_or_eq_true (A ⟨0, by omega⟩)
      rcases hbool with hfalse | htrue <;> simp [hfalse] at hAends ⊢
    · by_cases hilast : i.val = n - 1
      · have hrev : i.rev = ⟨0, by omega⟩ := by
          apply Fin.ext
          simp [hilast]
        rw [reverseWord, hrev]
        have hbool := Bool.eq_false_or_eq_true (A i)
        rcases hbool with hfalse | htrue <;> simp [hfalse] at hAends ⊢
      · have hi0' : 0 < i.val := Nat.pos_of_ne_zero hi0
        have hilast' : i.val < n - 1 := by omega
        have hrev0 : 0 < i.rev.val := by
          simp only [Fin.rev, Fin.val_mk]
          omega
        have hrevlast : i.rev.val < n - 1 := by
          simp only [Fin.rev, Fin.val_mk]
          omega
        rw [reverseWord]
        rw [hA i hi0' hilast', hA i.rev hrev0 hrevlast]
  have hrevB : (reverseWord B) = B := by
    funext i
    by_cases hi0 : i.val = 0
    · subst i
      have hrev : ((⟨0, by omega⟩ : Fin n).rev) = ⟨n - 1, by omega⟩ := by
        apply Fin.ext
        simp
      rw [reverseWord, hrev]
      have hbool := Bool.eq_false_or_eq_true (B ⟨0, by omega⟩)
      rcases hbool with hfalse | htrue <;> simp [hfalse] at hBends ⊢
    · by_cases hilast : i.val = n - 1
      · have hrev : i.rev = ⟨0, by omega⟩ := by
          apply Fin.ext
          simp [hilast]
        rw [reverseWord, hrev]
        have hbool := Bool.eq_false_or_eq_true (B i)
        rcases hbool with hfalse | htrue <;> simp [hfalse] at hBends ⊢
      · have hi0' : 0 < i.val := Nat.pos_of_ne_zero hi0
        have hilast' : i.val < n - 1 := by omega
        have hrev0 : 0 < i.rev.val := by
          simp only [Fin.rev, Fin.val_mk]
          omega
        have hrevlast : i.rev.val < n - 1 := by
          simp only [Fin.rev, Fin.val_mk]
          omega
        rw [reverseWord]
        rw [hB i hi0' hilast', hB i.rev hrev0 hrevlast]
  have hdeltaA := selfOverlapDelta_reverse_first A B
  have hdeltaB := selfOverlapDelta_reverse_second A B
  rw [hrevA, hrevB] at hdeltaA hdeltaB
  omega

#print axioms nearFull_monomial_eq_translated
#print axioms rawEnergy_le_of_constant_interior_equal_endpoints
#print axioms selfOverlapDelta_eq_zero_of_constant_interior_opposite_endpoints

end LittMostUnfairBetWalsh
