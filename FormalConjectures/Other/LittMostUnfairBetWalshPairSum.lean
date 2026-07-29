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

import Mathlib

/-!
# A finite square-sum decomposition

For a linearly ordered finite index set, the square of a sum is the diagonal
sum plus twice the sum over strictly ordered pairs.
-/

set_option autoImplicit false

namespace LittMostUnfairBetWalsh

open Finset

variable {α R : Type*} [LinearOrder α] [CommRing R]

/-- Diagonal pairs in `s × s`. -/
def diagonalPairs (s : Finset α) : Finset (α × α) :=
  (s ×ˢ s).filter (fun p => p.1 = p.2)

/-- Strictly increasing pairs in `s × s`. -/
def upperPairs (s : Finset α) : Finset (α × α) :=
  (s ×ˢ s).filter (fun p => p.1 < p.2)

/-- Strictly decreasing pairs in `s × s`. -/
def lowerPairs (s : Finset α) : Finset (α × α) :=
  (s ×ˢ s).filter (fun p => p.2 < p.1)

/-- The three pair classes partition the product. -/
theorem pair_partition (s : Finset α) :
    diagonalPairs s ∪ upperPairs s ∪ lowerPairs s = s ×ˢ s := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · exact (Finset.mem_filter.mp hp).1
      · exact (Finset.mem_filter.mp hp).1
    · exact (Finset.mem_filter.mp hp).1
  · intro hp
    rcases lt_trichotomy p.1 p.2 with hlt | heq | hgt
    · exact Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, hlt⟩))
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, heq⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, hgt⟩)

/-- Diagonal and increasing pairs are disjoint. -/
theorem diagonalPairs_disjoint_upperPairs (s : Finset α) :
    Disjoint (diagonalPairs s) (upperPairs s) := by
  rw [Finset.disjoint_left]
  intro p hpdiag hpupper
  have heq : p.1 = p.2 := (Finset.mem_filter.mp hpdiag).2
  have hlt : p.1 < p.2 := (Finset.mem_filter.mp hpupper).2
  exact (ne_of_lt hlt) heq

/-- The first two classes are disjoint from decreasing pairs. -/
theorem diagonal_union_upper_disjoint_lower (s : Finset α) :
    Disjoint (diagonalPairs s ∪ upperPairs s) (lowerPairs s) := by
  rw [Finset.disjoint_left]
  intro p hp hplower
  have hltLower : p.2 < p.1 := (Finset.mem_filter.mp hplower).2
  rcases Finset.mem_union.mp hp with hpdiag | hpupper
  · have heq : p.1 = p.2 := (Finset.mem_filter.mp hpdiag).2
    exact (ne_of_lt hltLower) heq.symm
  · have hltUpper : p.1 < p.2 := (Finset.mem_filter.mp hpupper).2
    exact (asymm hltUpper hltLower)

/-- Diagonal pairs are the image of `i ↦ (i,i)`. -/
theorem diagonalPairs_eq_image (s : Finset α) :
    diagonalPairs s = s.image (fun i => (i, i)) := by
  ext p
  constructor
  · intro hp
    have hp' := Finset.mem_filter.mp hp
    have hmem := Finset.mem_product.mp hp'.1
    apply Finset.mem_image.mpr
    refine ⟨p.1, hmem.1, ?_⟩
    exact Prod.ext rfl hp'.2
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨i, hi, rfl⟩
    simp [diagonalPairs, hi]

/-- Decreasing pairs are the swapped image of increasing pairs. -/
theorem lowerPairs_eq_swap_image (s : Finset α) :
    lowerPairs s = (upperPairs s).image Prod.swap := by
  ext p
  constructor
  · intro hp
    have hp' := Finset.mem_filter.mp hp
    have hmem := Finset.mem_product.mp hp'.1
    apply Finset.mem_image.mpr
    refine ⟨p.swap, ?_, by simp⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨hmem.2, hmem.1⟩, hp'.2⟩
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
    have hq' := Finset.mem_filter.mp hq
    have hmem := Finset.mem_product.mp hq'.1
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨hmem.2, hmem.1⟩, hq'.2⟩

/-- Sum over diagonal pairs. -/
theorem sum_diagonalPairs (s : Finset α) (f : α → R) :
    (∑ p ∈ diagonalPairs s, f p.1 * f p.2) = ∑ i ∈ s, f i ^ 2 := by
  rw [diagonalPairs_eq_image]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i hi
    ring
  · intro a ha b hb hab
    exact congrArg Prod.fst hab

/-- The decreasing and increasing pair sums agree by swapping coordinates. -/
theorem sum_lowerPairs_eq_sum_upperPairs (s : Finset α) (f : α → R) :
    (∑ p ∈ lowerPairs s, f p.1 * f p.2) =
      ∑ p ∈ upperPairs s, f p.1 * f p.2 := by
  rw [lowerPairs_eq_swap_image]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro p hp
    simp [mul_comm]
  · intro a ha b hb hab
    exact Prod.swap_injective hab

/-- The sum over all ordered pairs is diagonal plus twice the increasing pairs. -/
theorem sum_product_eq_diagonal_add_two_upper (s : Finset α) (f : α → R) :
    (∑ p ∈ s ×ˢ s, f p.1 * f p.2) =
      (∑ i ∈ s, f i ^ 2) +
        2 * ∑ p ∈ upperPairs s, f p.1 * f p.2 := by
  rw [← pair_partition s]
  rw [Finset.sum_union (diagonal_union_upper_disjoint_lower s)]
  rw [Finset.sum_union (diagonalPairs_disjoint_upperPairs s)]
  rw [sum_diagonalPairs, sum_lowerPairs_eq_sum_upperPairs]
  ring

/-- The square of a finite sum is diagonal plus twice the increasing pairs. -/
theorem sum_sq_eq_diagonal_add_two_upper (s : Finset α) (f : α → R) :
    (∑ i ∈ s, f i) ^ 2 =
      (∑ i ∈ s, f i ^ 2) +
        2 * ∑ p ∈ upperPairs s, f p.1 * f p.2 := by
  calc
    (∑ i ∈ s, f i) ^ 2 =
        ∑ p ∈ s ×ˢ s, f p.1 * f p.2 := by
      rw [pow_two, Finset.sum_product]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
    _ = _ := sum_product_eq_diagonal_add_two_upper s f

#print axioms sum_product_eq_diagonal_add_two_upper
#print axioms sum_sq_eq_diagonal_add_two_upper

end LittMostUnfairBetWalsh
