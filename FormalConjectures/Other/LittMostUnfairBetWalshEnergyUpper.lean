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

import FormalConjectures.Other.LittMostUnfairBetWalshEnergyTranslate

/-!
# Increasing-orbit reindexing for the Litt Walsh energy
-/

set_option autoImplicit false

namespace LittMostUnfairBetWalsh

open Finset
open LittMostUnfairBet

/-- One increasing-orbit term is its positive-shift correlation term. -/
theorem upperOrbit_term_eq {n : ℕ} (A B : Word n)
    (p : UpperOrbitPair n) :
    rawDifference A B (translate p.1.1.1 p.1.1.2) *
        rawDifference A B (translate p.1.1.1 p.1.2) =
      rawDifference A B (upperOrbitShiftEquiv n p).1.2 *
        shiftedRawDifference A B (upperOrbitShiftEquiv n p).1.1
          (upperOrbitShiftEquiv n p).1.2 := by
  have hp := mem_upperOrbitPairs.mp p.2
  change rawDifference A B (translate p.1.1.1 p.1.1.2) *
      rawDifference A B (translate p.1.1.1 p.1.2) =
    rawDifference A B (translate p.1.1.1 p.1.1.2) *
      shiftedRawDifference A B (p.1.2 - p.1.1.2)
        (translate p.1.1.1 p.1.1.2)
  rw [rawDifference_upper_translation A B p.1.1.1 (Nat.le_of_lt hp.2.2.2)]

/-- Increasing orbit terms reindex to all positive-shift subset correlations. -/
theorem upper_orbit_sum_eq_shift_sum {n : ℕ} (A B : Word n) :
    (∑ S ∈ shapes n, ∑ t ∈ translations n S,
      ∑ u ∈ (translations n S).filter (fun u => t < u),
        rawDifference A B (translate S t) *
          rawDifference A B (translate S u)) =
      ∑ h ∈ Finset.Ico 1 n,
        ∑ U ∈ (Finset.range (n - h)).powerset,
          rawDifference A B U * shiftedRawDifference A B h U := by
  let f : PositiveShiftSubset n → ℤ := fun q =>
    rawDifference A B q.1.2 * shiftedRawDifference A B q.1.1 q.1.2
  calc
    (∑ S ∈ shapes n, ∑ t ∈ translations n S,
      ∑ u ∈ (translations n S).filter (fun u => t < u),
        rawDifference A B (translate S t) *
          rawDifference A B (translate S u)) =
        ∑ p : UpperOrbitPair n,
          rawDifference A B (translate p.1.1.1 p.1.1.2) *
            rawDifference A B (translate p.1.1.1 p.1.2) := by
      symm
      simpa using
        (sum_upperOrbit_nested
          (n := n) (R := ℤ)
          (fun S t u => rawDifference A B (translate S t) *
            rawDifference A B (translate S u)))
    _ = ∑ p : UpperOrbitPair n, f (upperOrbitShiftEquiv n p) := by
      apply Fintype.sum_congr
      intro p
      exact upperOrbit_term_eq A B p
    _ = ∑ q : PositiveShiftSubset n, f q :=
      sum_upperOrbitShiftEquiv f
    _ = ∑ h ∈ Finset.Ico 1 n,
        ∑ U ∈ nonemptySubsets (n - h),
          rawDifference A B U * shiftedRawDifference A B h U := by
      simpa [f] using
        (sum_positiveShift_nested
          (n := n) (R := ℤ)
          (fun h U => rawDifference A B U * shiftedRawDifference A B h U))
    _ = ∑ h ∈ Finset.Ico 1 n,
        ∑ U ∈ (Finset.range (n - h)).powerset,
          rawDifference A B U * shiftedRawDifference A B h U := by
      apply Finset.sum_congr rfl
      intro h hh
      simp [nonemptySubsets, rawDifference, shiftedRawDifference]

#print axioms upperOrbit_term_eq
#print axioms upper_orbit_sum_eq_shift_sum

end LittMostUnfairBetWalsh
