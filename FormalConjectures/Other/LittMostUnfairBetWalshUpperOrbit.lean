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

import FormalConjectures.Other.LittMostUnfairBetWalshOrbit
import FormalConjectures.Other.LittMostUnfairBetWalshPairSum

/-!
# Increasing translation pairs and positive shifts

A pair of valid translations `t < u` of one normalized shape is equivalent to
a positive shift `h = u - t` together with a nonempty subset of the common
coordinate range `0, ..., n-h-1`.
-/

set_option autoImplicit false

namespace LittMostUnfairBetWalsh

open Finset

/-- Flattened finite set of `(shape,t,u)` with `t<u`. -/
noncomputable def upperOrbitPairs (n : ℕ) : Finset ((Finset ℕ × ℕ) × ℕ) :=
  ((((shapes n).product (Finset.range n)).product (Finset.range n))).filter
    (fun p => p.1.2 ∈ translations n p.1.1 ∧
      p.2 ∈ translations n p.1.1 ∧ p.1.2 < p.2)

@[simp] theorem mem_upperOrbitPairs {n : ℕ} {p : (Finset ℕ × ℕ) × ℕ} :
    p ∈ upperOrbitPairs n ↔
      p.1.1 ∈ shapes n ∧
      p.1.2 ∈ translations n p.1.1 ∧
      p.2 ∈ translations n p.1.1 ∧ p.1.2 < p.2 := by
  classical
  unfold upperOrbitPairs
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hp, ht, hu, htu⟩
    have hp' := Finset.mem_product.mp hp
    have hp'' := Finset.mem_product.mp hp'.1
    exact ⟨hp''.1, ht, hu, htu⟩
  · rintro ⟨hshape, ht, hu, htu⟩
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hshape, ?_⟩, ?_⟩,
      ht, hu, htu⟩
    · exact Finset.mem_range.mpr (mem_translations.mp ht).1
    · exact Finset.mem_range.mpr (mem_translations.mp hu).1

/-- Finite set of positive shifts paired with nonempty common-range subsets. -/
def positiveShiftSubsets (n : ℕ) : Finset (ℕ × Finset ℕ) :=
  (((Finset.Ico 1 n).product ((Finset.range n).powerset))).filter
    (fun p => p.2 ∈ nonemptySubsets (n - p.1))

@[simp] theorem mem_positiveShiftSubsets {n h : ℕ} {S : Finset ℕ} :
    (h, S) ∈ positiveShiftSubsets n ↔
      h ∈ Finset.Ico 1 n ∧ S ∈ nonemptySubsets (n - h) := by
  constructor
  · intro hp
    have hp' := Finset.mem_filter.mp hp
    have hprod := Finset.mem_product.mp hp'.1
    exact ⟨hprod.1, hp'.2⟩
  · rintro ⟨hh, hS⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hh, ?_⟩, hS⟩
    apply Finset.mem_powerset.mpr
    intro i hi
    have hi' := (mem_nonemptySubsets.mp hS).1 hi
    have hlt : i < n - h := Finset.mem_range.mp hi'
    exact Finset.mem_range.mpr (lt_of_lt_of_le hlt (Nat.sub_le n h))

abbrev UpperOrbitPair (n : ℕ) := ↥(upperOrbitPairs n)
abbrev PositiveShiftSubset (n : ℕ) := ↥(positiveShiftSubsets n)

private def upperOrbitToShiftVal {n : ℕ} (p : UpperOrbitPair n) :
    ℕ × Finset ℕ :=
  (p.1.2 - p.1.1.2, translate p.1.1.1 p.1.1.2)

/-- Map an increasing translation pair to its positive shift and left subset. -/
def upperOrbitToShift {n : ℕ} (p : UpperOrbitPair n) :
    PositiveShiftSubset n := by
  let T := p.1.1.1
  let t := p.1.1.2
  let u := p.1.2
  let h := u - t
  let S := translate T t
  have hp' := mem_upperOrbitPairs.mp p.2
  have hshape := hp'.1
  have ht := hp'.2.1
  have hu := hp'.2.2.1
  have htu := hp'.2.2.2
  refine ⟨upperOrbitToShiftVal p, mem_positiveShiftSubsets.mpr ⟨?_, ?_⟩⟩
  · have hu_lt := (mem_translations.mp hu).1
    simp only [Finset.mem_Ico]
    change 1 ≤ u - t ∧ u - t < n
    omega
  · apply mem_nonemptySubsets.mpr
    constructor
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
      have hvalid := (mem_translations.mp hu).2 i hi
      simp only [Finset.mem_range]
      change i + t < n - (u - t)
      omega
    · have hzero := (mem_shapes.mp hshape).2
      refine ⟨t, ?_⟩
      exact Finset.mem_image.mpr ⟨0, hzero, by simp⟩

private noncomputable def shiftToUpperOrbitVal {n : ℕ}
    (q : PositiveShiftSubset n) : (Finset ℕ × ℕ) × ℕ :=
  ((normalize q.1.2, offset q.1.2), offset q.1.2 + q.1.1)

/-- Recover the normalized shape and the two translations from a positive shift. -/
noncomputable def shiftToUpperOrbit {n : ℕ} (q : PositiveShiftSubset n) :
    UpperOrbitPair n := by
  let h := q.1.1
  let S := q.1.2
  let T := normalize S
  let t := offset S
  let u := t + h
  have hq := mem_positiveShiftSubsets.mp q.2
  have hh : 1 ≤ h ∧ h < n := by
    simpa [h] using Finset.mem_Ico.mp hq.1
  have hS : S ⊆ Finset.range (n - h) ∧ S.Nonempty := by
    simpa [S, h] using mem_nonemptySubsets.mp hq.2
  have hsubn : S ⊆ Finset.range n := by
    intro i hi
    have hi' := Finset.mem_range.mp (hS.1 hi)
    exact Finset.mem_range.mpr (lt_of_lt_of_le hi' (Nat.sub_le n h))
  have hshape : T ∈ shapes n := normalize_mem_shapes hsubn hS.2
  have ht : t ∈ translations n T := offset_mem_translations hsubn hS.2
  have hu : u ∈ translations n T := by
    apply mem_translations.mpr
    constructor
    · have hoff := Finset.mem_range.mp (hS.1 (offset_mem hS.2))
      change offset S + h < n
      omega
    · intro i hi
      have hiT : i ∈ normalize S := by simpa [T] using hi
      have hback0 : i + offset S ∈ translate (normalize S) (offset S) :=
        Finset.mem_image.mpr ⟨i, hiT, rfl⟩
      rw [translate_normalize hS.2] at hback0
      have hlt := Finset.mem_range.mp (hS.1 hback0)
      change i + (offset S + h) < n
      omega
  refine ⟨shiftToUpperOrbitVal q,
    mem_upperOrbitPairs.mpr ⟨hshape, ht, hu, ?_⟩⟩
  change offset S < offset S + h
  omega

/-- Increasing translation pairs and positive-shift subsets are equivalent. -/
noncomputable def upperOrbitShiftEquiv (n : ℕ) :
    UpperOrbitPair n ≃ PositiveShiftSubset n where
  toFun := upperOrbitToShift
  invFun := shiftToUpperOrbit
  left_inv := by
    intro p
    apply Subtype.ext
    change
      ((normalize (translate p.1.1.1 p.1.1.2),
          offset (translate p.1.1.1 p.1.1.2)),
        offset (translate p.1.1.1 p.1.1.2) + (p.1.2 - p.1.1.2)) = p.1
    apply Prod.ext
    · apply Prod.ext
      · exact (normalize_translate_pair
          (mem_upperOrbitPairs.mp p.2).1
          (mem_upperOrbitPairs.mp p.2).2.1).1
      · exact (normalize_translate_pair
          (mem_upperOrbitPairs.mp p.2).1
          (mem_upperOrbitPairs.mp p.2).2.1).2
    · rw [(normalize_translate_pair
        (mem_upperOrbitPairs.mp p.2).1
        (mem_upperOrbitPairs.mp p.2).2.1).2]
      omega
  right_inv := by
    intro q
    apply Subtype.ext
    change
      (offset q.1.2 + q.1.1 - offset q.1.2,
        translate (normalize q.1.2) (offset q.1.2)) = q.1
    apply Prod.ext
    · omega
    · exact translate_normalize_pair (mem_positiveShiftSubsets.mp q.2).2

/-- Reindex a sum over increasing orbit pairs by positive shifts. -/
theorem sum_upperOrbitShiftEquiv {n : ℕ} {R : Type*} [AddCommMonoid R]
    (f : PositiveShiftSubset n → R) :
    (∑ p : UpperOrbitPair n, f (upperOrbitShiftEquiv n p)) =
      ∑ q : PositiveShiftSubset n, f q := by
  exact Equiv.sum_comp (upperOrbitShiftEquiv n) f

#print axioms upperOrbitShiftEquiv
#print axioms sum_upperOrbitShiftEquiv

end LittMostUnfairBetWalsh
