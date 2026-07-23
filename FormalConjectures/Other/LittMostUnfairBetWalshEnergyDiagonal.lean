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
# Diagonal orbit reindexing for the Litt Walsh energy
-/

set_option autoImplicit false

namespace LittMostUnfairBetWalsh

open Finset
open LittMostUnfairBet

/-- Diagonal orbit terms reindex to all subsets; the empty term is zero. -/
theorem diagonal_orbit_sum_eq_powerset {n : ℕ} (A B : Word n) :
    (∑ S ∈ shapes n, ∑ t ∈ translations n S,
      rawDifference A B (translate S t) ^ 2) =
      ∑ U ∈ (Finset.range n).powerset, rawDifference A B U ^ 2 := by
  calc
    (∑ S ∈ shapes n, ∑ t ∈ translations n S,
      rawDifference A B (translate S t) ^ 2) =
        ∑ p : ShapeTranslation n,
          rawDifference A B (pairToSubset p).1 ^ 2 := by
      symm
      simpa [pairToSubset] using
        (sum_shapeTranslation_nested
          (n := n) (R := ℤ)
          (fun S t => rawDifference A B (translate S t) ^ 2))
    _ = ∑ U : NonemptyCoordinateSubset n,
        rawDifference A B U.1 ^ 2 := by
      exact sum_shapeTranslationEquiv
        (fun U : NonemptyCoordinateSubset n => rawDifference A B U.1 ^ 2)
    _ = ∑ U ∈ nonemptySubsets n, rawDifference A B U ^ 2 := by
      simpa only using
        (Finset.sum_attach
          (s := nonemptySubsets n)
          (f := fun U => rawDifference A B U ^ 2))
    _ = ∑ U ∈ (Finset.range n).powerset, rawDifference A B U ^ 2 := by
      simp [nonemptySubsets, rawDifference]

#print axioms diagonal_orbit_sum_eq_powerset

end LittMostUnfairBetWalsh
