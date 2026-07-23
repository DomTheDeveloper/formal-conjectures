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

import FormalConjectures.Other.LittMostUnfairBetWalshNormalize

/-!
# The translation-orbit equivalence

Valid translations of normalized shapes are in bijection with nonempty
subsets of the coordinate range. This is the principal finite reindexing step
for the Litt Walsh energy identity.
-/

set_option autoImplicit false

namespace LittMostUnfairBetWalsh

open Finset

/-- Finite set of valid `(shape, translation)` pairs. -/
noncomputable def shapeTranslationPairs (n : ℕ) : Finset (Finset ℕ × ℕ) :=
  ((shapes n).product (Finset.range n)).filter
    (fun p => p.2 ∈ translations n p.1)

@[simp] theorem mem_shapeTranslationPairs {n : ℕ} {p : Finset ℕ × ℕ} :
    p ∈ shapeTranslationPairs n ↔
      p.1 ∈ shapes n ∧ p.2 ∈ translations n p.1 := by
  classical
  unfold shapeTranslationPairs
  rw [Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨hshape, _hrange⟩, htrans⟩
    exact ⟨hshape, htrans⟩
  · rintro ⟨hshape, htrans⟩
    have hrange : p.2 ∈ Finset.range n :=
      Finset.mem_range.mpr (mem_translations.mp htrans).1
    exact ⟨⟨hshape, hrange⟩, htrans⟩

/-- The finite type of valid shape-translation pairs. -/
abbrev ShapeTranslation (n : ℕ) := ↥(shapeTranslationPairs n)

/-- The finite type of nonempty coordinate subsets. -/
abbrev NonemptyCoordinateSubset (n : ℕ) := ↥(nonemptySubsets n)

/-- Convert a valid pair to its translated coordinate subset. -/
def pairToSubset {n : ℕ} (p : ShapeTranslation n) :
    NonemptyCoordinateSubset n :=
  ⟨translate p.1.1 p.1.2,
    translate_mem_nonemptySubsets
      (mem_shapeTranslationPairs.mp p.2).1
      (mem_shapeTranslationPairs.mp p.2).2⟩

/-- Convert a nonempty coordinate subset to its normalized shape and offset. -/
def subsetToPair {n : ℕ} (S : NonemptyCoordinateSubset n) :
    ShapeTranslation n := by
  let h := mem_nonemptySubsets.mp S.2
  exact ⟨(normalize S.1, offset S.1),
    mem_shapeTranslationPairs.mpr ⟨
      normalize_mem_shapes h.1 h.2,
      offset_mem_translations h.1 h.2⟩⟩

/-- Normalized shape/offset and translation are inverse finite encodings. -/
def shapeTranslationEquiv (n : ℕ) :
    ShapeTranslation n ≃ NonemptyCoordinateSubset n where
  toFun := pairToSubset
  invFun := subsetToPair
  left_inv := by
    intro p
    apply Subtype.ext
    apply Prod.ext
    · exact (normalize_translate_pair
        (mem_shapeTranslationPairs.mp p.2).1
        (mem_shapeTranslationPairs.mp p.2).2).1
    · exact (normalize_translate_pair
        (mem_shapeTranslationPairs.mp p.2).1
        (mem_shapeTranslationPairs.mp p.2).2).2
  right_inv := by
    intro S
    apply Subtype.ext
    exact translate_normalize_pair S.2

/-- Reindex any finite sum from valid shape translations to nonempty subsets. -/
theorem sum_shapeTranslationEquiv {n : ℕ} {R : Type*} [AddCommMonoid R]
    (f : NonemptyCoordinateSubset n → R) :
    (∑ p : ShapeTranslation n, f (shapeTranslationEquiv n p)) =
      ∑ S : NonemptyCoordinateSubset n, f S := by
  exact Equiv.sum_comp (shapeTranslationEquiv n) f

/-- The translated subset associated to the inverse pair is the original set. -/
@[simp] theorem pairToSubset_subsetToPair {n : ℕ}
    (S : NonemptyCoordinateSubset n) :
    pairToSubset (subsetToPair S) = S := by
  exact (shapeTranslationEquiv n).apply_symm_apply S

/-- The normalized inverse pair associated to a valid translation is unchanged. -/
@[simp] theorem subsetToPair_pairToSubset {n : ℕ} (p : ShapeTranslation n) :
    subsetToPair (pairToSubset p) = p := by
  exact (shapeTranslationEquiv n).symm_apply_apply p

#print axioms shapeTranslationEquiv
#print axioms sum_shapeTranslationEquiv

end LittMostUnfairBetWalsh
