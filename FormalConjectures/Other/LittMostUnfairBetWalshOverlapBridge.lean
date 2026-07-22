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

import FormalConjectures.Other.LittMostUnfairBetWalshVariance

/-!
# Positive shifts and proper word overlaps

A positive shift `h` leaves a common block of length `n-h`. This file
identifies that block with the proper overlap index `k = n-h-1` used by
`overlapNum`, and therefore identifies the repository variance numerator with
the Walsh translation-shape square energy.
-/

set_option autoImplicit false

namespace LittMostUnfairBetWalsh

open Finset
open LittMostUnfairBet

/-- Positive shifts of a word of length `n`. -/
abbrev PositiveWordShift (n : ℕ) := ↥(Finset.Ico 1 n)

/-- The proper indices occurring in `overlapNum`. -/
def properOverlapIndices (n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun k => k.val + 1 < n)

/-- A proper overlap index, packaged as a finite subtype. -/
abbrev ProperOverlapIndex (n : ℕ) := ↥(properOverlapIndices n)

/-- A positive shift `h` corresponds to the overlap length `n-h`. -/
def shiftToOverlapIndex {n : ℕ} (h : PositiveWordShift n) :
    ProperOverlapIndex n := by
  have hh := Finset.mem_Ico.mp h.2
  refine ⟨⟨n - h.1 - 1, by omega⟩, ?_⟩
  simp only [properOverlapIndices, Finset.mem_filter, Finset.mem_univ, true_and]
  omega

/-- A proper overlap of length `k+1` corresponds to shift `n-(k+1)`. -/
def overlapIndexToShift {n : ℕ} (k : ProperOverlapIndex n) :
    PositiveWordShift n := by
  have hk := (Finset.mem_filter.mp k.2).2
  refine ⟨n - (k.1.val + 1), Finset.mem_Ico.mpr ?_⟩
  omega

/-- Positive shifts and proper overlap indices are equivalent. -/
def positiveShiftOverlapEquiv (n : ℕ) :
    PositiveWordShift n ≃ ProperOverlapIndex n where
  toFun := shiftToOverlapIndex
  invFun := overlapIndexToShift
  left_inv := by
    intro h
    apply Subtype.ext
    dsimp [shiftToOverlapIndex, overlapIndexToShift]
    have hh := Finset.mem_Ico.mp h.2
    omega
  right_inv := by
    intro k
    apply Subtype.ext
    apply Fin.ext
    dsimp [shiftToOverlapIndex, overlapIndexToShift]
    have hk := (Finset.mem_filter.mp k.2).2
    omega

/-- The overlap length attached to `h` is exactly `n-h`. -/
theorem shiftToOverlapIndex_length {n : ℕ} (h : PositiveWordShift n) :
    (shiftToOverlapIndex h).1.val + 1 = n - h.1 := by
  dsimp [shiftToOverlapIndex]
  have hh := Finset.mem_Ico.mp h.2
  omega

/-- Block equality at shift `h` is the corresponding suffix-prefix overlap. -/
theorem shift_block_eq_iff_overlap {n : ℕ} (A B : Word n)
    (h : PositiveWordShift n) :
    prefixBlock B h.1 = suffixBlock A h.1 ↔
      wordSuffix A (shiftToOverlapIndex h).1 =
        wordPrefix B (shiftToOverlapIndex h).1 := by
  constructor
  · intro hblock
    funext i
    let j : Fin (n - h.1) := ⟨i.val, by
      have hi := i.isLt
      rw [shiftToOverlapIndex_length h] at hi
      exact hi⟩
    have hv := congrFun hblock j
    change A ⟨n - (shiftToOverlapIndex h).1.val - 1 + i.val, by omega⟩ =
      B ⟨i.val, by omega⟩
    convert hv.symm using 1 <;> apply Fin.ext <;>
      dsimp [j, shiftToOverlapIndex] <;>
      have hh := Finset.mem_Ico.mp h.2 <;> omega
  · intro hoverlap
    funext i
    let j : Fin ((shiftToOverlapIndex h).1.val + 1) := ⟨i.val, by
      rw [shiftToOverlapIndex_length h]
      exact i.isLt⟩
    have hv := congrFun hoverlap j
    change B ⟨i.val, by omega⟩ = A ⟨h.1 + i.val, by omega⟩
    convert hv.symm using 1 <;> apply Fin.ext <;>
      dsimp [j, shiftToOverlapIndex] <;>
      have hh := Finset.mem_Ico.mp h.2 <;> omega

/-- The weighted block test is the weighted proper-overlap test. -/
theorem shift_overlap_term_eq {n : ℕ} (A B : Word n)
    (h : PositiveWordShift n) :
    (if prefixBlock B h.1 = suffixBlock A h.1 then 2 ^ (n - h.1) else 0) =
      if wordSuffix A (shiftToOverlapIndex h).1 =
          wordPrefix B (shiftToOverlapIndex h).1 then
        2 ^ ((shiftToOverlapIndex h).1.val + 1)
      else 0 := by
  have hiff := shift_block_eq_iff_overlap A B h
  have hlen := shiftToOverlapIndex_length h
  by_cases hb : prefixBlock B h.1 = suffixBlock A h.1
  · have ho := hiff.mp hb
    simp [hb, ho, hlen]
  · have ho : wordSuffix A (shiftToOverlapIndex h).1 ≠
        wordPrefix B (shiftToOverlapIndex h).1 := by
      exact fun h' => hb (hiff.mpr h')
    simp [hb, ho, hlen]

/-- `overlapNum` is the positive-shift block-equality sum. -/
theorem overlapNum_eq_positive_shift_sum {n : ℕ} (A B : Word n) :
    overlapNum A B =
      ∑ h ∈ Finset.Ico 1 n,
        if prefixBlock B h = suffixBlock A h then 2 ^ (n - h) else 0 := by
  let f : Fin n → ℕ := fun k =>
    if wordSuffix A k = wordPrefix B k then 2 ^ (k.val + 1) else 0
  calc
    overlapNum A B =
        ∑ k : Fin n, if k.val + 1 < n then f k else 0 := by
      unfold overlapNum
      apply Fintype.sum_congr
      intro k
      by_cases hp : k.val + 1 < n <;> simp [f, hp]
    _ = ∑ k ∈ properOverlapIndices n, f k := by
      simp [properOverlapIndices]
    _ = ∑ k : ProperOverlapIndex n, f k.1 := by
      symm
      exact Finset.sum_coe_sort (properOverlapIndices n) f
    _ = ∑ h : PositiveWordShift n,
        f (positiveShiftOverlapEquiv n h).1 := by
      symm
      exact Equiv.sum_comp (positiveShiftOverlapEquiv n)
        (fun k : ProperOverlapIndex n => f k.1)
    _ = ∑ h : PositiveWordShift n,
        if prefixBlock B h.1 = suffixBlock A h.1 then 2 ^ (n - h.1) else 0 := by
      apply Fintype.sum_congr
      intro h
      symm
      simpa [positiveShiftOverlapEquiv, f] using shift_overlap_term_eq A B h
    _ = ∑ h ∈ Finset.Ico 1 n,
        if prefixBlock B h = suffixBlock A h then 2 ^ (n - h) else 0 := by
      exact Finset.sum_coe_sort (Finset.Ico 1 n)
        (fun h => if prefixBlock B h = suffixBlock A h then 2 ^ (n - h) else 0)

/-- Casting `overlapNum` gives the shift-indexed integer numerator. -/
theorem natCast_overlapNum_eq_shiftOverlapNum {n : ℕ} (A B : Word n) :
    ((overlapNum A B : ℕ) : ℤ) = shiftOverlapNum A B := by
  rw [overlapNum_eq_positive_shift_sum]
  unfold shiftOverlapNum
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro h hh
  split <;> simp

/-- The repository and shift-indexed variance numerators coincide. -/
theorem varianceNum_eq_shiftVarianceNum {n : ℕ} (A B : Word n) :
    varianceNum A B = shiftVarianceNum A B := by
  unfold varianceNum shiftVarianceNum
  rw [natCast_overlapNum_eq_shiftOverlapNum A A,
    natCast_overlapNum_eq_shiftOverlapNum B B,
    natCast_overlapNum_eq_shiftOverlapNum A B,
    natCast_overlapNum_eq_shiftOverlapNum B A]

/-- Exact Walsh square identity for the repository variance numerator. -/
theorem rawEnergy_cast_eq_two_mul_varianceNum {n : ℕ}
    (A B : Word n) (hne : A ≠ B) :
    ((rawEnergy A B : ℕ) : ℤ) = 2 * varianceNum A B := by
  rw [varianceNum_eq_shiftVarianceNum]
  exact rawEnergy_cast_eq_two_mul_shiftVarianceNum A B hne

/-- The repository variance numerator is nonnegative. -/
theorem varianceNum_nonneg {n : ℕ} (A B : Word n) (hne : A ≠ B) :
    0 ≤ varianceNum A B := by
  rw [varianceNum_eq_shiftVarianceNum]
  exact shiftVarianceNum_nonneg A B hne

#print axioms positiveShiftOverlapEquiv
#print axioms shift_block_eq_iff_overlap
#print axioms overlapNum_eq_positive_shift_sum
#print axioms varianceNum_eq_shiftVarianceNum
#print axioms rawEnergy_cast_eq_two_mul_varianceNum

end LittMostUnfairBetWalsh
