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

import FormalConjectures.Other.LittMostUnfairBetProof
import FormalConjectures.Other.LittMostUnfairBetWalshOverlapBridge

/-!
# Constant-word Walsh variance gap

When one word is constant, raw Walsh differences belonging to two translates
of the same shape have the same sign. Hence every positive-shift correlation
is nonnegative and the raw energy is at least its diagonal term `2^(n+1)`.
-/

set_option autoImplicit false

namespace LittMostUnfairBetWalsh

open Finset
open LittMostUnfairBet

/-- The monomial of a constant word depends only on the set cardinality. -/
theorem natMonomial_constant_of_subset_range {n : ℕ} (b : Bool)
    (S : Finset ℕ) (hsub : S ⊆ Finset.range n) :
    natMonomial (constantWord n b) S = coinSign b ^ #S := by
  unfold natMonomial
  calc
    (∏ i ∈ S, letterSign (constantWord n b) i) =
        ∏ _i ∈ S, coinSign b := by
      apply Finset.prod_congr rfl
      intro i hi
      have hin : i < n := Finset.mem_range.mp (hsub hi)
      simp [letterSign, constantWord, hin]
    _ = coinSign b ^ #S := by simp

/-- A constant word has the same monomial on a set and its valid translate. -/
theorem natMonomial_constant_translate_eq {n h : ℕ} (b : Bool)
    (S : Finset ℕ) (hsub : S ⊆ Finset.range (n - h)) :
    natMonomial (constantWord n b) S =
      natMonomial (constantWord n b) (translate S h) := by
  have hsubn : S ⊆ Finset.range n := by
    intro i hi
    have hil := Finset.mem_range.mp (hsub hi)
    exact Finset.mem_range.mpr (by omega)
  have htrans : translate S h ⊆ Finset.range n := by
    intro i hi
    rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
    have hjl := Finset.mem_range.mp (hsub hj)
    exact Finset.mem_range.mpr (by omega)
  rw [natMonomial_constant_of_subset_range b S hsubn,
    natMonomial_constant_of_subset_range b (translate S h) htrans,
    card_translate]

/-- If the right-word monomials agree, two raw differences have nonnegative product. -/
theorem rawDifference_mul_nonneg_of_right_monomial_eq {n : ℕ}
    (A B : Word n) (S T : Finset ℕ)
    (hB : natMonomial B S = natMonomial B T) :
    0 ≤ rawDifference A B S * rawDifference A B T := by
  rcases natMonomial_eq_one_or_neg_one A S with hAS | hAS <;>
    rcases natMonomial_eq_one_or_neg_one A T with hAT | hAT <;>
    rcases natMonomial_eq_one_or_neg_one B S with hBS | hBS <;>
    rcases natMonomial_eq_one_or_neg_one B T with hBT | hBT <;>
    simp [rawDifference, hAS, hAT, hBS, hBT] at hB ⊢

/-- If the left-word monomials agree, two raw differences have nonnegative product. -/
theorem rawDifference_mul_nonneg_of_left_monomial_eq {n : ℕ}
    (A B : Word n) (S T : Finset ℕ)
    (hA : natMonomial A S = natMonomial A T) :
    0 ≤ rawDifference A B S * rawDifference A B T := by
  have h := rawDifference_mul_nonneg_of_right_monomial_eq B A S T hA
  unfold rawDifference at h ⊢
  nlinarith

/-- Every fixed-shift Walsh summand is nonnegative when one word is constant. -/
theorem shift_product_nonneg_of_constant {n h : ℕ} (A B : Word n)
    (hconst : IsConstant A ∨ IsConstant B)
    (S : Finset ℕ) (hsub : S ⊆ Finset.range (n - h)) :
    0 ≤ rawDifference A B S * shiftedRawDifference A B h S := by
  rw [← rawDifference_translate]
  rcases hconst with hA | hB
  · rcases hA with ⟨b, rfl⟩
    exact rawDifference_mul_nonneg_of_left_monomial_eq
      (constantWord n b) B S (translate S h)
      (natMonomial_constant_translate_eq b S hsub)
  · rcases hB with ⟨b, rfl⟩
    exact rawDifference_mul_nonneg_of_right_monomial_eq
      A (constantWord n b) S (translate S h)
      (natMonomial_constant_translate_eq b S hsub)

/-- Every positive-shift correlation is nonnegative in the constant branch. -/
theorem shift_correlation_nonneg_of_constant {n h : ℕ} (A B : Word n)
    (hconst : IsConstant A ∨ IsConstant B) :
    0 ≤ ∑ S ∈ (Finset.range (n - h)).powerset,
      rawDifference A B S * shiftedRawDifference A B h S := by
  apply Finset.sum_nonneg
  intro S hS
  apply shift_product_nonneg_of_constant A B hconst S
  exact Finset.mem_powerset.mp hS

/-- A distinct pair containing a constant word has raw energy at least `2^(n+1)`. -/
theorem signedRawEnergy_ge_of_constant {n : ℕ} (A B : Word n)
    (hne : A ≠ B) (hconst : IsConstant A ∨ IsConstant B) :
    (2 ^ (n + 1) : ℤ) ≤ signedRawEnergy A B := by
  rw [signedRawEnergy_eq_correlations]
  simp_rw [pow_two]
  rw [diagonal_raw_correlation A B hne]
  have hshift :
      0 ≤ ∑ h ∈ Finset.Ico 1 n,
        ∑ S ∈ (Finset.range (n - h)).powerset,
          rawDifference A B S * shiftedRawDifference A B h S := by
    apply Finset.sum_nonneg
    intro h hh
    exact shift_correlation_nonneg_of_constant A B hconst
  linarith

/-- Natural raw energy lower bound for the constant branch. -/
theorem rawEnergy_ge_of_constant {n : ℕ} (A B : Word n)
    (hne : A ≠ B) (hconst : IsConstant A ∨ IsConstant B) :
    2 ^ (n + 1) ≤ rawEnergy A B := by
  have h := signedRawEnergy_ge_of_constant A B hne hconst
  rw [← natCast_rawEnergy_eq_signedRawEnergy] at h
  exact_mod_cast h

/-- Therefore the repository variance numerator is at least `2^n`. -/
theorem varianceNum_ge_of_constant {n : ℕ} (A B : Word n)
    (hne : A ≠ B) (hconst : IsConstant A ∨ IsConstant B) :
    ((2 ^ n : ℕ) : ℤ) ≤ varianceNum A B := by
  have henergy := rawEnergy_ge_of_constant A B hne hconst
  have hid := rawEnergy_cast_eq_two_mul_varianceNum A B hne
  have hcast : ((2 ^ (n + 1) : ℕ) : ℤ) ≤ (rawEnergy A B : ℤ) := by
    exact_mod_cast henergy
  rw [hid] at hcast
  norm_num [pow_succ] at hcast ⊢

#print axioms rawEnergy_ge_of_constant
#print axioms varianceNum_ge_of_constant

end LittMostUnfairBetWalsh
