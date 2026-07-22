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

import FormalConjectures.Other.LittMostUnfairBetWalshEnergyDiagonal
import FormalConjectures.Other.LittMostUnfairBetWalshEnergyUpper

/-!
# The correlation form of the Litt Walsh energy
-/

set_option autoImplicit false

namespace LittMostUnfairBetWalsh

open Finset
open LittMostUnfairBet

/-- The raw shape-square energy is diagonal plus twice the positive shifts. -/
theorem signedRawEnergy_eq_correlations {n : ℕ} (A B : Word n) :
    signedRawEnergy A B =
      (∑ U ∈ (Finset.range n).powerset, rawDifference A B U ^ 2) +
      2 * ∑ h ∈ Finset.Ico 1 n,
        ∑ U ∈ (Finset.range (n - h)).powerset,
          rawDifference A B U * shiftedRawDifference A B h U := by
  unfold signedRawEnergy
  calc
    (∑ S ∈ shapes n, shapeCoeff A B S ^ 2) =
      ∑ S ∈ shapes n,
        ((∑ t ∈ translations n S,
          rawDifference A B (translate S t) ^ 2) +
        2 * ∑ t ∈ translations n S,
          ∑ u ∈ (translations n S).filter (fun u => t < u),
            rawDifference A B (translate S t) *
              rawDifference A B (translate S u)) := by
      apply Finset.sum_congr rfl
      intro S hS
      exact shapeCoeff_sq_decomposition A B S
    _ =
      (∑ S ∈ shapes n, ∑ t ∈ translations n S,
        rawDifference A B (translate S t) ^ 2) +
      2 * (∑ S ∈ shapes n, ∑ t ∈ translations n S,
        ∑ u ∈ (translations n S).filter (fun u => t < u),
          rawDifference A B (translate S t) *
            rawDifference A B (translate S u)) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by
      rw [diagonal_orbit_sum_eq_powerset, upper_orbit_sum_eq_shift_sum]

/-- The natural square energy casts to the integer square energy. -/
theorem natCast_rawEnergy_eq_signedRawEnergy {n : ℕ} (A B : Word n) :
    ((rawEnergy A B : ℕ) : ℤ) = signedRawEnergy A B := by
  unfold rawEnergy signedRawEnergy
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro _ hmem
  simp only [Nat.cast_pow]
  have habs : ((shapeCoeff A B S).natAbs : ℤ) = |shapeCoeff A B S| :=
    Int.natCast_natAbs _
  rw [habs]
  exact sq_abs (shapeCoeff A B S)

#print axioms signedRawEnergy_eq_correlations
#print axioms natCast_rawEnergy_eq_signedRawEnergy

end LittMostUnfairBetWalsh
