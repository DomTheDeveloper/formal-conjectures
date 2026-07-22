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

import FormalConjectures.Other.LittMostUnfairBetWalshUpperOrbit

/-!
# Flattening the finite orbit index types

These lemmas connect sums over the finite subtype encodings used by the orbit
`Equiv`s with the nested shape/translation and shift/subset sums appearing in
the energy calculation.
-/

set_option autoImplicit false

namespace LittMostUnfairBetWalsh

open Finset

/-- A sum over valid shape-translation pairs is the corresponding nested sum. -/
theorem sum_shapeTranslation_nested {n : ℕ} {R : Type*} [AddCommMonoid R]
    (f : Finset ℕ → ℕ → R) :
    (∑ p : ShapeTranslation n, f p.1.1 p.1.2) =
      ∑ S ∈ shapes n, ∑ t ∈ translations n S, f S t := by
  have hmem : ∀ p : Finset ℕ × ℕ,
      p ∈ shapeTranslationPairs n ↔
        p.1 ∈ shapes n ∧ p.2 ∈ translations n p.1 := by
    intro p
    exact mem_shapeTranslationPairs
  simpa using
    (Finset.sum_finset_product'
      (shapeTranslationPairs n) (shapes n) (translations n) hmem
      (f := f))

/-- A sum over increasing orbit pairs is the corresponding three-level sum. -/
theorem sum_upperOrbit_nested {n : ℕ} {R : Type*} [AddCommMonoid R]
    (f : Finset ℕ → ℕ → ℕ → R) :
    (∑ p : UpperOrbitPair n, f p.1.1.1 p.1.1.2 p.1.2) =
      ∑ S ∈ shapes n, ∑ t ∈ translations n S,
        ∑ u ∈ (translations n S).filter (fun u => t < u), f S t u := by
  have houter : ∀ p : (Finset ℕ × ℕ) × ℕ,
      p ∈ upperOrbitPairs n ↔
        p.1 ∈ shapeTranslationPairs n ∧
          p.2 ∈ (translations n p.1.1).filter (fun u => p.1.2 < u) := by
    intro p
    simp [mem_upperOrbitPairs, mem_shapeTranslationPairs, and_assoc]
  calc
    (∑ p : UpperOrbitPair n, f p.1.1.1 p.1.1.2 p.1.2) =
        ∑ st ∈ shapeTranslationPairs n,
          ∑ u ∈ (translations n st.1).filter (fun u => st.2 < u),
            f st.1 st.2 u := by
      simpa using
        (Finset.sum_finset_product'
          (upperOrbitPairs n) (shapeTranslationPairs n)
          (fun st => (translations n st.1).filter (fun u => st.2 < u))
          houter (f := fun st u => f st.1 st.2 u))
    _ = ∑ S ∈ shapes n, ∑ t ∈ translations n S,
        ∑ u ∈ (translations n S).filter (fun u => t < u), f S t u := by
      have hinner : ∀ p : Finset ℕ × ℕ,
          p ∈ shapeTranslationPairs n ↔
            p.1 ∈ shapes n ∧ p.2 ∈ translations n p.1 := by
        intro p
        exact mem_shapeTranslationPairs
      exact Finset.sum_finset_product'
        (shapeTranslationPairs n) (shapes n) (translations n) hinner

/-- A sum over positive-shift subsets is the corresponding dependent nested sum. -/
theorem sum_positiveShift_nested {n : ℕ} {R : Type*} [AddCommMonoid R]
    (f : ℕ → Finset ℕ → R) :
    (∑ q : PositiveShiftSubset n, f q.1.1 q.1.2) =
      ∑ h ∈ Finset.Ico 1 n, ∑ S ∈ nonemptySubsets (n - h), f h S := by
  have hmem : ∀ p : ℕ × Finset ℕ,
      p ∈ positiveShiftSubsets n ↔
        p.1 ∈ Finset.Ico 1 n ∧ p.2 ∈ nonemptySubsets (n - p.1) := by
    intro p
    exact mem_positiveShiftSubsets
  simpa using
    (Finset.sum_finset_product'
      (positiveShiftSubsets n) (Finset.Ico 1 n)
      (fun h => nonemptySubsets (n - h)) hmem (f := f))

#print axioms sum_shapeTranslation_nested
#print axioms sum_upperOrbit_nested
#print axioms sum_positiveShift_nested

end LittMostUnfairBetWalsh
