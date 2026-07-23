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

import FormalConjectures.Other.LittMostUnfairBetWalshGap

/-!
# Interior-disagreement contribution to the Litt Walsh gap

If two words differ at an interior coordinate `j`, every subset of the other
interior coordinates determines, after possibly inserting `j`, a distinct
full-span shape with raw square contribution `4`. There are `2^(n-3)` such
subsets.
-/

set_option autoImplicit false

namespace LittMostUnfairBetWalsh

open Finset
open LittMostUnfairBet

/-- Interior coordinates other than `j`. -/
def interiorExcept (n j : ℕ) : Finset ℕ :=
  (Finset.Ico 1 (n - 1)).erase j

@[simp] theorem mem_interiorExcept {n j i : ℕ} :
    i ∈ interiorExcept n j ↔ i ≠ j ∧ 1 ≤ i ∧ i < n - 1 := by
  simp [interiorExcept, and_assoc]

/-- Add both endpoints to an interior subset. -/
def fullSpanBase (n : ℕ) (R : Finset ℕ) : Finset ℕ :=
  insert 0 (insert (n - 1) R)

/-- The selected full-span shape for one interior subset. -/
def selectedInteriorShape {n : ℕ} (A B : Word n) (j : ℕ) (R : Finset ℕ) :
    Finset ℕ :=
  chooseDifferingShape A B j (fullSpanBase n R)

/-- Remove the endpoints and the distinguished coordinate from a selected shape. -/
def stripInteriorShape (n j : ℕ) (S : Finset ℕ) : Finset ℕ :=
  ((S.erase 0).erase (n - 1)).erase j

/-- A full-span base is contained in the coordinate range. -/
theorem fullSpanBase_subset_range {n j : ℕ} (hn : 3 ≤ n) {R : Finset ℕ}
    (hR : R ⊆ interiorExcept n j) :
    fullSpanBase n R ⊆ Finset.range n := by
  intro i hi
  simp only [fullSpanBase, Finset.mem_insert] at hi
  rcases hi with rfl | rfl | hi
  · simp
    omega
  · simp
    omega
  · have hri := mem_interiorExcept.mp (hR hi)
    simp
    omega

@[simp] theorem zero_mem_fullSpanBase (n : ℕ) (R : Finset ℕ) :
    0 ∈ fullSpanBase n R := by
  simp [fullSpanBase]

@[simp] theorem last_mem_fullSpanBase (n : ℕ) (R : Finset ℕ) :
    n - 1 ∈ fullSpanBase n R := by
  simp [fullSpanBase]

/-- The distinguished interior coordinate is absent from every base. -/
theorem distinguished_not_mem_fullSpanBase {n : ℕ} (j : Fin n)
    (hjpos : 0 < j.val) (hjlast : j.val < n - 1) {R : Finset ℕ}
    (hR : R ⊆ interiorExcept n j.val) :
    j.val ∉ fullSpanBase n R := by
  have hj0 : j.val ≠ 0 := Nat.ne_of_gt hjpos
  have hjend : j.val ≠ n - 1 := Nat.ne_of_lt hjlast
  have hjR : j.val ∉ R := by
    intro hjmem
    exact (mem_interiorExcept.mp (hR hjmem)).1 rfl
  simp [fullSpanBase, hj0, hjend, hjR]

/-- The selected shape remains inside the word. -/
theorem selectedInteriorShape_subset_range {n : ℕ} (hn : 3 ≤ n)
    (A B : Word n) (j : Fin n) (hjpos : 0 < j.val)
    (hjlast : j.val < n - 1) {R : Finset ℕ}
    (hR : R ⊆ interiorExcept n j.val) :
    selectedInteriorShape A B j.val R ⊆ Finset.range n := by
  have hbase := fullSpanBase_subset_range (j := j.val) hn hR
  have hjrange : j.val ∈ Finset.range n := Finset.mem_range.mpr j.isLt
  unfold selectedInteriorShape chooseDifferingShape
  by_cases hzero : rawDifference A B (fullSpanBase n R) = 0
  · simp [hzero, Finset.insert_subset_iff, hjrange, hbase]
  · simpa [hzero] using hbase

@[simp] theorem zero_mem_selectedInteriorShape {n : ℕ} (A B : Word n)
    (j : ℕ) (R : Finset ℕ) :
    0 ∈ selectedInteriorShape A B j R := by
  unfold selectedInteriorShape chooseDifferingShape
  split <;> simp [fullSpanBase]

@[simp] theorem last_mem_selectedInteriorShape {n : ℕ} (A B : Word n)
    (j : ℕ) (R : Finset ℕ) :
    n - 1 ∈ selectedInteriorShape A B j R := by
  unfold selectedInteriorShape chooseDifferingShape
  split <;> simp [fullSpanBase]

/-- Every selected set is a normalized shape. -/
theorem selectedInteriorShape_mem_shapes {n : ℕ} (hn : 3 ≤ n)
    (A B : Word n) (j : Fin n) (hjpos : 0 < j.val)
    (hjlast : j.val < n - 1) {R : Finset ℕ}
    (hR : R ⊆ interiorExcept n j.val) :
    selectedInteriorShape A B j.val R ∈ shapes n := by
  exact mem_shapes.mpr ⟨
    selectedInteriorShape_subset_range hn A B j hjpos hjlast hR,
    zero_mem_selectedInteriorShape A B j.val R⟩

/-- Each selected full-span shape contributes exactly `4` to the raw energy. -/
theorem selectedInteriorShape_square {n : ℕ} (hn : 3 ≤ n)
    (A B : Word n) (j : Fin n) (hjpos : 0 < j.val)
    (hjlast : j.val < n - 1) (hword : A j ≠ B j) {R : Finset ℕ}
    (hR : R ⊆ interiorExcept n j.val) :
    (shapeCoeff A B (selectedInteriorShape A B j.val R)).natAbs ^ 2 = 4 := by
  rw [shapeCoeff_eq_rawDifference_of_full_span (by omega) A B
    (selectedInteriorShape A B j.val R)
    (selectedInteriorShape_subset_range hn A B j hjpos hjlast hR)
    (last_mem_selectedInteriorShape A B j.val R)]
  apply chooseDifferingShape_square A B (fullSpanBase n R) j.isLt
    (distinguished_not_mem_fullSpanBase j hjpos hjlast hR)
  simpa using hword

/-- Stripping a selected shape recovers its indexing interior subset. -/
theorem strip_selectedInteriorShape {n : ℕ} (A B : Word n) (j : Fin n)
    (hjpos : 0 < j.val) (hjlast : j.val < n - 1) {R : Finset ℕ}
    (hR : R ⊆ interiorExcept n j.val) :
    stripInteriorShape n j.val (selectedInteriorShape A B j.val R) = R := by
  have hR0 : 0 ∉ R := by
    intro h
    have hr := mem_interiorExcept.mp (hR h)
    omega
  have hRlast : n - 1 ∉ R := by
    intro h
    have hr := mem_interiorExcept.mp (hR h)
    omega
  have hRj : j.val ∉ R := by
    intro h
    exact (mem_interiorExcept.mp (hR h)).1 rfl
  have hj0 : j.val ≠ 0 := Nat.ne_of_gt hjpos
  have hjend : j.val ≠ n - 1 := Nat.ne_of_lt hjlast
  ext i
  unfold stripInteriorShape selectedInteriorShape chooseDifferingShape
  by_cases hzero : rawDifference A B (fullSpanBase n R) = 0
  · simp only [hzero, if_pos, fullSpanBase, Finset.mem_erase, Finset.mem_insert]
    constructor
    · rintro ⟨hij, hilast, hi0, hi⟩
      rcases hi with hij' | hi0' | hilast' | hiR
      · exact (hij hij').elim
      · exact (hi0 hi0').elim
      · exact (hilast hilast').elim
      · exact hiR
    · intro hiR
      refine ⟨?_, ?_, ?_, Or.inr (Or.inr (Or.inr hiR))⟩
      · intro hij
        apply hRj
        simpa [hij] using hiR
      · intro hilast
        apply hRlast
        simpa [hilast] using hiR
      · intro hi0
        apply hR0
        simpa [hi0] using hiR
  · simp only [hzero, if_false, fullSpanBase, Finset.mem_erase, Finset.mem_insert]
    constructor
    · rintro ⟨hij, hilast, hi0, hi⟩
      rcases hi with hi0' | hilast' | hiR
      · exact (hi0 hi0').elim
      · exact (hilast hilast').elim
      · exact hiR
    · intro hiR
      refine ⟨?_, ?_, ?_, Or.inr (Or.inr hiR)⟩
      · intro hij
        apply hRj
        simpa [hij] using hiR
      · intro hilast
        apply hRlast
        simpa [hilast] using hiR
      · intro hi0
        apply hR0
        simpa [hi0] using hiR

/-- The selected-shape map is injective on the interior powerset. -/
theorem selectedInteriorShape_injective {n : ℕ} (A B : Word n)
    (j : Fin n) (hjpos : 0 < j.val) (hjlast : j.val < n - 1)
    {R₁ R₂ : Finset ℕ}
    (hR₁ : R₁ ∈ (interiorExcept n j.val).powerset)
    (hR₂ : R₂ ∈ (interiorExcept n j.val).powerset)
    (heq : selectedInteriorShape A B j.val R₁ =
      selectedInteriorShape A B j.val R₂) :
    R₁ = R₂ := by
  have hstrip₁ := strip_selectedInteriorShape A B j hjpos hjlast
    (Finset.mem_powerset.mp hR₁)
  have hstrip₂ := strip_selectedInteriorShape A B j hjpos hjlast
    (Finset.mem_powerset.mp hR₂)
  rw [← hstrip₁, ← hstrip₂, heq]

/-- The interior set with one distinguished coordinate removed has size `n-3`. -/
theorem card_interiorExcept {n : ℕ} (hn : 3 ≤ n) (j : Fin n)
    (hjpos : 0 < j.val) (hjlast : j.val < n - 1) :
    #(interiorExcept n j.val) = n - 3 := by
  have hjmem : j.val ∈ Finset.Ico 1 (n - 1) := by
    simp
    omega
  rw [interiorExcept, Finset.card_erase_of_mem hjmem]
  simp
  omega

/-- The selected full-span family has exactly `2^(n-3)` members. -/
theorem card_selectedInteriorShapes {n : ℕ} (hn : 3 ≤ n)
    (A B : Word n) (j : Fin n) (hjpos : 0 < j.val)
    (hjlast : j.val < n - 1) :
    #((interiorExcept n j.val).powerset.image
      (selectedInteriorShape A B j.val)) = 2 ^ (n - 3) := by
  have hinj : Set.InjOn (selectedInteriorShape A B j.val)
      (interiorExcept n j.val).powerset := by
    intro R₁ hR₁ R₂ hR₂ heq
    exact selectedInteriorShape_injective A B j hjpos hjlast hR₁ hR₂ heq
  rw [Finset.card_image_of_injOn hinj]
  simp [card_interiorExcept hn j hjpos hjlast]

/-- An interior disagreement forces at least `4 * 2^(n-3)` raw Walsh energy. -/
theorem rawEnergy_ge_of_interior_disagreement {n : ℕ} (hn : 3 ≤ n)
    (A B : Word n) (j : Fin n) (hjpos : 0 < j.val)
    (hjlast : j.val < n - 1) (hword : A j ≠ B j) :
    4 * 2 ^ (n - 3) ≤ rawEnergy A B := by
  let selected := (interiorExcept n j.val).powerset.image
    (selectedInteriorShape A B j.val)
  have hsubset : selected ⊆ shapes n := by
    intro S hS
    rcases Finset.mem_image.mp hS with ⟨R, hR, rfl⟩
    exact selectedInteriorShape_mem_shapes hn A B j hjpos hjlast
      (Finset.mem_powerset.mp hR)
  have hselected :
      (∑ S ∈ selected, (shapeCoeff A B S).natAbs ^ 2) =
        4 * 2 ^ (n - 3) := by
    calc
      (∑ S ∈ selected, (shapeCoeff A B S).natAbs ^ 2) =
          ∑ _S ∈ selected, 4 := by
        apply Finset.sum_congr rfl
        intro S hS
        rcases Finset.mem_image.mp hS with ⟨R, hR, rfl⟩
        exact selectedInteriorShape_square hn A B j hjpos hjlast hword
          (Finset.mem_powerset.mp hR)
      _ = 4 * #selected := by simp [mul_comm]
      _ = 4 * 2 ^ (n - 3) := by
        rw [card_selectedInteriorShapes hn A B j hjpos hjlast]
  rw [rawEnergy, ← hselected]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
    intro S hS hnot
    exact Nat.zero_le _)

#print axioms selectedInteriorShape_square
#print axioms selectedInteriorShape_injective
#print axioms rawEnergy_ge_of_interior_disagreement

end LittMostUnfairBetWalsh
