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
import FormalConjectures.Other.LittMostUnfairBetWalshOverlapBridge

/-!
# From shift-indexed variance to the Formal Conjectures overlap numerator
-/

set_option autoImplicit false

namespace LittMostUnfairBetWalsh

open Finset
open LittMostUnfairBet

/-- The shift-indexed overlap sum is the integer cast of `overlapNum`. -/
theorem shiftOverlapNum_eq_overlapNum {n : ℕ} (A B : Word n) :
    shiftOverlapNum A B = (overlapNum A B : ℤ) := by
  unfold shiftOverlapNum
  rw [overlapNum_eq_positive_shift_sum]
  push_cast

/-- The shift-indexed variance is exactly the variance numerator in the statement. -/
theorem shiftVarianceNum_eq_varianceNum {n : ℕ} (A B : Word n) :
    shiftVarianceNum A B = varianceNum A B := by
  unfold shiftVarianceNum varianceNum
  rw [shiftOverlapNum_eq_overlapNum A A,
    shiftOverlapNum_eq_overlapNum B B,
    shiftOverlapNum_eq_overlapNum A B,
    shiftOverlapNum_eq_overlapNum B A]
  norm_num

/-- The natural Walsh energy is exactly twice the statement's variance numerator. -/
theorem rawEnergy_cast_eq_two_mul_varianceNum {n : ℕ}
    (A B : Word n) (hne : A ≠ B) :
    ((rawEnergy A B : ℕ) : ℤ) = 2 * varianceNum A B := by
  rw [rawEnergy_cast_eq_two_mul_shiftVarianceNum A B hne,
    shiftVarianceNum_eq_varianceNum]

/-- The denominator-cleared variance numerator is nonnegative. -/
theorem varianceNum_nonneg {n : ℕ} (A B : Word n) (hne : A ≠ B) :
    0 ≤ varianceNum A B := by
  rw [← shiftVarianceNum_eq_varianceNum]
  exact shiftVarianceNum_nonneg A B hne

/-- Package the signed variance numerator as a natural number. -/
theorem exists_varianceNat {n : ℕ} (A B : Word n) (hne : A ≠ B) :
    ∃ q : ℕ, varianceNum A B = (q : ℤ) ∧ rawEnergy A B = 2 * q := by
  let q := (varianceNum A B).toNat
  have hnonneg := varianceNum_nonneg A B hne
  have hcast : (q : ℤ) = varianceNum A B := by
    exact Int.toNat_of_nonneg hnonneg
  refine ⟨q, hcast.symm, ?_⟩
  have henergy := rawEnergy_cast_eq_two_mul_varianceNum A B hne
  rw [← hcast] at henergy
  exact_mod_cast henergy

#print axioms shiftOverlapNum_eq_overlapNum
#print axioms rawEnergy_cast_eq_two_mul_varianceNum
#print axioms exists_varianceNat

end LittMostUnfairBetWalsh
