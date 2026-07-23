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

import FormalConjectures.Other.LittMostUnfairBetWalshShiftCorrelation
import FormalConjectures.Other.LittMostUnfairBetWalshSumFlatten

/-!
# Translation algebra for the Litt Walsh energy
-/

set_option autoImplicit false

namespace LittMostUnfairBetWalsh

open Finset
open LittMostUnfairBet

/-- Integer-valued version of the raw square energy. -/
noncomputable def signedRawEnergy {n : ℕ} (A B : Word n) : ℤ :=
  ∑ S ∈ shapes n, shapeCoeff A B S ^ 2

/-- Translating twice adds the translation amounts. -/
theorem translate_translate (S : Finset ℕ) (t h : ℕ) :
    translate (translate S t) h = translate S (t + h) := by
  ext i
  simp [translate, Nat.add_assoc]

/-- A shifted monomial is the monomial of the translated coordinate set. -/
theorem natMonomial_translate {n : ℕ} (A : Word n) (S : Finset ℕ) (h : ℕ) :
    natMonomial A (translate S h) = shiftedMonomial A h S := by
  unfold natMonomial shiftedMonomial translate
  rw [Finset.prod_image]
  intro a ha b hb hab
  exact Nat.add_right_cancel hab

/-- A shifted raw difference is a raw difference on the translated set. -/
theorem rawDifference_translate {n : ℕ} (A B : Word n)
    (S : Finset ℕ) (h : ℕ) :
    rawDifference A B (translate S h) = shiftedRawDifference A B h S := by
  simp [rawDifference, shiftedRawDifference, natMonomial_translate]

/-- Two translations of one shape differ by the corresponding positive shift. -/
theorem rawDifference_upper_translation {n : ℕ} (A B : Word n)
    (S : Finset ℕ) {t u : ℕ} (htu : t ≤ u) :
    rawDifference A B (translate S u) =
      shiftedRawDifference A B (u - t) (translate S t) := by
  rw [← rawDifference_translate]
  rw [translate_translate]
  congr 2
  omega

/-- Sum over increasing pairs as a nested filtered sum. -/
theorem sum_upperPairs_nested {R : Type*} [AddCommMonoid R]
    (s : Finset ℕ) (f : ℕ → ℕ → R) :
    (∑ p ∈ upperPairs s, f p.1 p.2) =
      ∑ t ∈ s, ∑ u ∈ s.filter (fun u => t < u), f t u := by
  have hmem : ∀ p : ℕ × ℕ,
      p ∈ upperPairs s ↔ p.1 ∈ s ∧ p.2 ∈ s.filter (fun u => p.1 < u) := by
    intro p
    simp [upperPairs, and_assoc]
  exact Finset.sum_finset_product' (upperPairs s) s
    (fun t => s.filter (fun u => t < u)) hmem

/-- Square expansion for one translation shape. -/
theorem shapeCoeff_sq_decomposition {n : ℕ} (A B : Word n)
    (S : Finset ℕ) :
    shapeCoeff A B S ^ 2 =
      (∑ t ∈ translations n S,
        rawDifference A B (translate S t) ^ 2) +
      2 * ∑ t ∈ translations n S,
        ∑ u ∈ (translations n S).filter (fun u => t < u),
          rawDifference A B (translate S t) *
            rawDifference A B (translate S u) := by
  rw [shapeCoeff]
  rw [sum_sq_eq_diagonal_add_two_upper]
  have hp := sum_upperPairs_nested (translations n S)
    (fun t u => rawDifference A B (translate S t) *
      rawDifference A B (translate S u))
  exact congrArg
    (fun z : ℤ =>
      (∑ t ∈ translations n S,
        rawDifference A B (translate S t) ^ 2) + 2 * z) hp

#print axioms rawDifference_upper_translation
#print axioms shapeCoeff_sq_decomposition

end LittMostUnfairBetWalsh
