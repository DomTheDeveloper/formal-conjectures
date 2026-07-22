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

import FormalConjectures.Other.LittMostUnfairBetWalshShapes

/-!
# Unit-square lemmas for the Litt Walsh variance gap

The all-length gap proof selects full-span shapes.  At a differing coordinate,
either the base shape already has a nonzero raw coefficient or inserting that
coordinate forces one.  Each selected shape therefore contributes exactly `4`
to the raw square energy.
-/

set_option autoImplicit false

namespace LittMostUnfairBetWalsh

open Finset
open LittMostUnfairBet

@[simp] theorem natMonomial_insert {n : ℕ} (A : Word n) (S : Finset ℕ)
    {j : ℕ} (hj : j ∉ S) :
    natMonomial A (insert j S) = letterSign A j * natMonomial A S := by
  simp [natMonomial, hj]

/-- Different letters have opposite extended signs at an in-range coordinate. -/
theorem letterSign_mul_eq_neg_one_of_word_ne {n j : ℕ} (A B : Word n)
    (hj : j < n) (hne : A ⟨j, hj⟩ ≠ B ⟨j, hj⟩) :
    letterSign A j * letterSign B j = -1 := by
  simp only [letterSign_of_lt A hj, letterSign_of_lt B hj]
  exact coinSign_mul_eq_neg_one_of_ne hne

/-- A nonzero raw coefficient has square magnitude `4`. -/
theorem rawDifference_natAbs_sq_eq_four_of_ne_zero {n : ℕ}
    (A B : Word n) (S : Finset ℕ) (hne : rawDifference A B S ≠ 0) :
    (rawDifference A B S).natAbs ^ 2 = 4 := by
  rcases rawDifference_eq_zero_or_two_or_neg_two A B S with hzero | htwo | hneg
  · exact (hne hzero).elim
  · simp [htwo]
  · simp [hneg]

/-- If the product of the two monomials is `-1`, their raw difference has
square magnitude `4`. -/
theorem rawDifference_natAbs_sq_eq_four_of_mul_eq_neg_one {n : ℕ}
    (A B : Word n) (S : Finset ℕ)
    (hprod : natMonomial A S * natMonomial B S = -1) :
    (rawDifference A B S).natAbs ^ 2 = 4 := by
  apply rawDifference_natAbs_sq_eq_four_of_ne_zero
  intro hzero
  have heq : natMonomial A S = natMonomial B S := by
    simpa [rawDifference] using hzero
  rw [heq, natMonomial_mul_self] at hprod
  norm_num at hprod

/-- If a base coefficient cancels, inserting a coordinate where the words
differ forces a unit square. -/
theorem inserted_rawDifference_natAbs_sq_eq_four {n j : ℕ}
    (A B : Word n) (S : Finset ℕ) (hj : j < n) (hjS : j ∉ S)
    (hword : A ⟨j, hj⟩ ≠ B ⟨j, hj⟩)
    (hzero : rawDifference A B S = 0) :
    (rawDifference A B (insert j S)).natAbs ^ 2 = 4 := by
  apply rawDifference_natAbs_sq_eq_four_of_mul_eq_neg_one
  have hmono : natMonomial A S = natMonomial B S := by
    simpa [rawDifference] using hzero
  rw [natMonomial_insert A S hjS, natMonomial_insert B S hjS]
  calc
    (letterSign A j * natMonomial A S) *
        (letterSign B j * natMonomial B S) =
      (letterSign A j * letterSign B j) *
        (natMonomial B S * natMonomial B S) := by
          rw [hmono]
          ring
    _ = (-1) * 1 := by
      rw [letterSign_mul_eq_neg_one_of_word_ne A B hj hword,
        natMonomial_mul_self]
    _ = -1 := by norm_num

/-- Choosing between a base shape and the same shape with a differing coordinate
inserted always yields a unit square. -/
def chooseDifferingShape {n : ℕ} (A B : Word n) (j : ℕ) (S : Finset ℕ) :
    Finset ℕ :=
  if rawDifference A B S = 0 then insert j S else S

/-- The chosen shape has raw square contribution `4`, provided the differing
coordinate was not already in the base shape. -/
theorem chooseDifferingShape_square {n j : ℕ} (A B : Word n)
    (S : Finset ℕ) (hj : j < n) (hjS : j ∉ S)
    (hword : A ⟨j, hj⟩ ≠ B ⟨j, hj⟩) :
    (rawDifference A B (chooseDifferingShape A B j S)).natAbs ^ 2 = 4 := by
  unfold chooseDifferingShape
  by_cases hzero : rawDifference A B S = 0
  · simp [hzero, inserted_rawDifference_natAbs_sq_eq_four A B S hj hjS hword hzero]
  · simp [hzero, rawDifference_natAbs_sq_eq_four_of_ne_zero A B S hzero]

#print axioms inserted_rawDifference_natAbs_sq_eq_four
#print axioms chooseDifferingShape_square

end LittMostUnfairBetWalsh
