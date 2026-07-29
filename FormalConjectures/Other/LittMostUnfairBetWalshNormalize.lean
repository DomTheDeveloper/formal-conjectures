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
# Normalizing finite translation shapes

Every nonempty subset of a coordinate interval is uniquely a right translate
of a shape containing zero. This is the orbit reindexing used to convert the
Walsh square energy into fixed-shift correlations.
-/

set_option autoImplicit false

namespace LittMostUnfairBetWalsh

open Finset

/-- Nonempty subsets of the coordinate range. -/
def nonemptySubsets (n : ℕ) : Finset (Finset ℕ) :=
  (Finset.range n).powerset.erase ∅

@[simp] theorem mem_nonemptySubsets {n : ℕ} {S : Finset ℕ} :
    S ∈ nonemptySubsets n ↔ S ⊆ Finset.range n ∧ S.Nonempty := by
  simp [nonemptySubsets, Finset.nonempty_iff_ne_empty, and_comm]

/-- The minimum coordinate, with value zero on the empty set. -/
def offset (S : Finset ℕ) : ℕ :=
  if h : S.Nonempty then S.min' h else 0

/-- Translate a set so that its minimum becomes zero. -/
def normalize (S : Finset ℕ) : Finset ℕ :=
  S.image (fun i => i - offset S)

/-- The offset of a nonempty set belongs to it. -/
theorem offset_mem {S : Finset ℕ} (hS : S.Nonempty) : offset S ∈ S := by
  unfold offset
  rw [dif_pos hS]
  exact Finset.min'_mem S hS

/-- The offset is below every member of a nonempty set. -/
theorem offset_le {S : Finset ℕ} (hS : S.Nonempty) {i : ℕ} (hi : i ∈ S) :
    offset S ≤ i := by
  unfold offset
  rw [dif_pos hS]
  exact Finset.min'_le S i hi

/-- The normalized form of a nonempty set contains zero. -/
theorem zero_mem_normalize {S : Finset ℕ} (hS : S.Nonempty) :
    0 ∈ normalize S := by
  apply Finset.mem_image.mpr
  refine ⟨offset S, offset_mem hS, ?_⟩
  omega

/-- Normalization preserves containment in an initial coordinate range. -/
theorem normalize_subset_range {n : ℕ} {S : Finset ℕ}
    (hsub : S ⊆ Finset.range n) :
    normalize S ⊆ Finset.range n := by
  intro i hi
  rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
  have hjn : j < n := Finset.mem_range.mp (hsub hj)
  simp
  omega

/-- Translating a normalized nonempty set back by its offset recovers it. -/
theorem translate_normalize {S : Finset ℕ} (hS : S.Nonempty) :
    translate (normalize S) (offset S) = S := by
  ext i
  constructor
  · intro hi
    rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
    rcases Finset.mem_image.mp hj with ⟨k, hk, rfl⟩
    rw [Nat.sub_add_cancel (offset_le hS hk)]
    exact hk
  · intro hi
    apply Finset.mem_image.mpr
    refine ⟨i - offset S, ?_, Nat.sub_add_cancel (offset_le hS hi)⟩
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩

/-- Translating a shape containing zero makes its translation amount the new
minimum. -/
theorem offset_translate {S : Finset ℕ} {t : ℕ} (hzero : 0 ∈ S) :
    offset (translate S t) = t := by
  have ht : t ∈ translate S t := by
    exact Finset.mem_image.mpr ⟨0, hzero, by simp⟩
  have hnonempty : (translate S t).Nonempty := ⟨t, ht⟩
  apply Nat.le_antisymm
  · exact offset_le hnonempty ht
  · unfold offset
    rw [dif_pos hnonempty]
    apply Finset.le_min'
    intro i hi
    rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
    omega

/-- Normalizing a translate of a shape containing zero recovers the shape. -/
theorem normalize_translate {S : Finset ℕ} {t : ℕ} (hzero : 0 ∈ S) :
    normalize (translate S t) = S := by
  rw [normalize, offset_translate hzero]
  ext i
  simp [translate]

/-- The normalization of a nonempty subset is a valid normalized shape. -/
theorem normalize_mem_shapes {n : ℕ} {S : Finset ℕ}
    (hsub : S ⊆ Finset.range n) (hS : S.Nonempty) :
    normalize S ∈ shapes n := by
  exact mem_shapes.mpr ⟨normalize_subset_range hsub, zero_mem_normalize hS⟩

/-- The original offset is a valid translation of its normalized shape. -/
theorem offset_mem_translations {n : ℕ} {S : Finset ℕ}
    (hsub : S ⊆ Finset.range n) (hS : S.Nonempty) :
    offset S ∈ translations n (normalize S) := by
  rw [mem_translations]
  constructor
  · exact Finset.mem_range.mp (hsub (offset_mem hS))
  · intro i hi
    let q := i + offset S
    have himg : q ∈ translate (normalize S) (offset S) := by
      dsimp [q]
      exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
    have hback : q ∈ S := by
      rw [← translate_normalize hS]
      exact himg
    exact Finset.mem_range.mp (hsub (by simpa [q] using hback))

/-- A valid translate of a shape is a nonempty subset of the coordinate range. -/
theorem translate_mem_nonemptySubsets {n : ℕ} {S : Finset ℕ} {t : ℕ}
    (hshape : S ∈ shapes n) (ht : t ∈ translations n S) :
    translate S t ∈ nonemptySubsets n := by
  have hshape' := mem_shapes.mp hshape
  have ht' := mem_translations.mp ht
  apply mem_nonemptySubsets.mpr
  constructor
  · intro i hi
    rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
    exact Finset.mem_range.mpr (ht'.2 j hj)
  · refine ⟨t, ?_⟩
    exact Finset.mem_image.mpr ⟨0, hshape'.2, by simp⟩

/-- Normalization and offset recover every valid shape-translation pair. -/
theorem normalize_translate_pair {n : ℕ} {S : Finset ℕ} {t : ℕ}
    (hshape : S ∈ shapes n) (ht : t ∈ translations n S) :
    normalize (translate S t) = S ∧ offset (translate S t) = t := by
  have hzero := (mem_shapes.mp hshape).2
  exact ⟨normalize_translate hzero, offset_translate hzero⟩

/-- Translation recovers every nonempty subset from its normalized pair. -/
theorem translate_normalize_pair {n : ℕ} {S : Finset ℕ}
    (hS : S ∈ nonemptySubsets n) :
    translate (normalize S) (offset S) = S := by
  exact translate_normalize (mem_nonemptySubsets.mp hS).2

#print axioms translate_normalize
#print axioms normalize_translate
#print axioms offset_mem_translations
#print axioms normalize_translate_pair

end LittMostUnfairBetWalsh
