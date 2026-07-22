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

import FormalConjectures.Other.LittMostUnfairBetWalshEnergyIdentity

/-!
# The exact shift-indexed variance identity

The raw translation-shape square energy is exactly twice the denominator-
cleared overlap variance numerator.
-/

set_option autoImplicit false

namespace LittMostUnfairBetWalsh

open Finset
open LittMostUnfairBet

/-- Proper weighted suffix-prefix overlaps indexed by their positive shift. -/
def shiftOverlapNum {n : ℕ} (A B : Word n) : ℤ :=
  ∑ h ∈ Finset.Ico 1 n,
    if prefixBlock B h = suffixBlock A h then (2 ^ (n - h) : ℤ) else 0

/-- Shift-indexed form of the denominator-cleared variance numerator. -/
def shiftVarianceNum {n : ℕ} (A B : Word n) : ℤ :=
  (2 ^ n : ℤ) + shiftOverlapNum A A + shiftOverlapNum B B -
    shiftOverlapNum A B - shiftOverlapNum B A

/-- Each fixed-shift correlation is the corresponding four overlap indicators. -/
theorem shift_correlation_eq_overlap_terms {n h : ℕ} (A B : Word n) :
    (∑ U ∈ (Finset.range (n - h)).powerset,
      rawDifference A B U * shiftedRawDifference A B h U) =
      (if prefixBlock A h = suffixBlock A h then (2 ^ (n - h) : ℤ) else 0) -
      (if prefixBlock A h = suffixBlock B h then (2 ^ (n - h) : ℤ) else 0) -
      (if prefixBlock B h = suffixBlock A h then (2 ^ (n - h) : ℤ) else 0) +
      (if prefixBlock B h = suffixBlock B h then (2 ^ (n - h) : ℤ) else 0) := by
  simpa using
    (sum_powerset_rawDifference_mul_shiftedRawDifference
      (n := n) (h := h) A B)

/-- The raw Walsh square energy equals twice the shift overlap variance numerator. -/
theorem signedRawEnergy_eq_two_mul_shiftVarianceNum {n : ℕ}
    (A B : Word n) (hne : A ≠ B) :
    signedRawEnergy A B = 2 * shiftVarianceNum A B := by
  rw [signedRawEnergy_eq_correlations]
  rw [diagonal_raw_correlation A B hne]
  unfold shiftVarianceNum shiftOverlapNum
  simp_rw [shift_correlation_eq_overlap_terms]
  ring

/-- Natural raw energy is twice a nonnegative integer variance numerator. -/
theorem rawEnergy_cast_eq_two_mul_shiftVarianceNum {n : ℕ}
    (A B : Word n) (hne : A ≠ B) :
    ((rawEnergy A B : ℕ) : ℤ) = 2 * shiftVarianceNum A B := by
  rw [natCast_rawEnergy_eq_signedRawEnergy]
  exact signedRawEnergy_eq_two_mul_shiftVarianceNum A B hne

/-- The shift variance numerator is nonnegative. -/
theorem shiftVarianceNum_nonneg {n : ℕ} (A B : Word n) (hne : A ≠ B) :
    0 ≤ shiftVarianceNum A B := by
  have h := rawEnergy_cast_eq_two_mul_shiftVarianceNum A B hne
  have henergy : (0 : ℤ) ≤ (rawEnergy A B : ℤ) := by positivity
  omega

#print axioms signedRawEnergy_eq_two_mul_shiftVarianceNum
#print axioms shiftVarianceNum_nonneg

end LittMostUnfairBetWalsh
