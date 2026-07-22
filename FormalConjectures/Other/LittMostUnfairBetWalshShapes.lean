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

import FormalConjectures.Other.LittMostUnfairBetDefs
import FormalConjectures.Other.LittMostUnfairBetWalsh

/-!
# Translation shapes for the Litt Walsh energy

A nonempty finite coordinate set has a unique normalized translation shape,
obtained by moving its minimum to zero. The asymptotic variance is the sum of
squares of the aggregated raw Walsh differences over these shapes.
-/

set_option autoImplicit false

namespace LittMostUnfairBetWalsh

open Finset
open LittMostUnfairBet

/-- Extend a word sign by `1` outside its valid coordinate range. -/
def letterSign {n : ℕ} (A : Word n) (i : ℕ) : ℤ :=
  if h : i < n then coinSign (A ⟨i, h⟩) else 1

@[simp] theorem letterSign_of_lt {n : ℕ} (A : Word n) {i : ℕ} (hi : i < n) :
    letterSign A i = coinSign (A ⟨i, hi⟩) := by
  simp [letterSign, hi]

@[simp] theorem letterSign_mul_self {n : ℕ} (A : Word n) (i : ℕ) :
    letterSign A i * letterSign A i = 1 := by
  by_cases hi : i < n
  · simp [letterSign, hi]
  · simp [letterSign, hi]

/-- A Walsh monomial on a finite set of natural-number coordinates. -/
def natMonomial {n : ℕ} (A : Word n) (S : Finset ℕ) : ℤ :=
  ∏ i ∈ S, letterSign A i

@[simp] theorem natMonomial_empty {n : ℕ} (A : Word n) : natMonomial A ∅ = 1 := by
  simp [natMonomial]

@[simp] theorem natMonomial_mul_self {n : ℕ} (A : Word n) (S : Finset ℕ) :
    natMonomial A S * natMonomial A S = 1 := by
  rw [← Finset.prod_mul_distrib]
  simp [natMonomial, letterSign_mul_self]

/-- Every word monomial is itself a sign. -/
theorem natMonomial_eq_one_or_neg_one {n : ℕ} (A : Word n) (S : Finset ℕ) :
    natMonomial A S = 1 ∨ natMonomial A S = -1 := by
  have hsquare := natMonomial_mul_self A S
  nlinarith

/-- Normalized nonempty translation shapes inside a word of length `n`. -/
def shapes (n : ℕ) : Finset (Finset ℕ) :=
  (Finset.range n).powerset.filter (fun S => 0 ∈ S)

@[simp] theorem mem_shapes {n : ℕ} {S : Finset ℕ} :
    S ∈ shapes n ↔ S ⊆ Finset.range n ∧ 0 ∈ S := by
  simp [shapes]

/-- Translating `S` by `t` remains inside a word of length `n`. -/
def ValidTranslation (n : ℕ) (S : Finset ℕ) (t : ℕ) : Prop :=
  ∀ i ∈ S, i + t < n

/-- All valid right translations of a normalized shape. -/
def translations (n : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (Finset.range n).filter (ValidTranslation n S)

@[simp] theorem mem_translations {n t : ℕ} {S : Finset ℕ} :
    t ∈ translations n S ↔ t < n ∧ ValidTranslation n S t := by
  simp [translations]

/-- Translate a finite set of natural coordinates to the right. -/
def translate (S : Finset ℕ) (t : ℕ) : Finset ℕ :=
  S.image (fun i => i + t)

@[simp] theorem translate_zero (S : Finset ℕ) : translate S 0 = S := by
  ext i
  simp [translate]

/-- Translation preserves cardinality. -/
theorem card_translate (S : Finset ℕ) (t : ℕ) :
    #(translate S t) = #S := by
  unfold translate
  rw [Finset.card_image_iff.mpr]
  intro a ha b hb hab
  omega

/-- The raw (undivided) Walsh coefficient difference of two words. -/
def rawDifference {n : ℕ} (A B : Word n) (S : Finset ℕ) : ℤ :=
  natMonomial A S - natMonomial B S

/-- A raw Walsh difference is `0`, `2`, or `-2`. -/
theorem rawDifference_eq_zero_or_two_or_neg_two {n : ℕ}
    (A B : Word n) (S : Finset ℕ) :
    rawDifference A B S = 0 ∨
      rawDifference A B S = 2 ∨ rawDifference A B S = -2 := by
  rcases natMonomial_eq_one_or_neg_one A S with hA | hA <;>
    rcases natMonomial_eq_one_or_neg_one B S with hB | hB <;>
    simp [rawDifference, hA, hB]

/-- The coefficient obtained by adding all translates of one normalized shape. -/
def shapeCoeff {n : ℕ} (A B : Word n) (S : Finset ℕ) : ℤ :=
  ∑ t ∈ translations n S, rawDifference A B (translate S t)

/-- Raw integer square energy of all normalized translation shapes. -/
def rawEnergy {n : ℕ} (A B : Word n) : ℕ :=
  ∑ S ∈ shapes n, (shapeCoeff A B S).natAbs ^ 2

/-- A full-span shape has only the zero translation. -/
theorem translations_eq_singleton_zero {n : ℕ} (hn : 1 ≤ n) (S : Finset ℕ)
    (hsub : S ⊆ Finset.range n) (hlast : n - 1 ∈ S) :
    translations n S = {0} := by
  ext t
  simp only [mem_translations, Finset.mem_singleton]
  constructor
  · rintro ⟨ht, hvalid⟩
    have h := hvalid (n - 1) hlast
    omega
  · rintro rfl
    refine ⟨by omega, ?_⟩
    intro i hi
    exact Finset.mem_range.mp (hsub hi)

/-- The coefficient of a full-span shape is its one raw monomial difference. -/
theorem shapeCoeff_eq_rawDifference_of_full_span {n : ℕ} (hn : 1 ≤ n)
    (A B : Word n) (S : Finset ℕ)
    (hsub : S ⊆ Finset.range n) (hlast : n - 1 ∈ S) :
    shapeCoeff A B S = rawDifference A B S := by
  rw [shapeCoeff, translations_eq_singleton_zero hn S hsub hlast]
  simp

#print axioms natMonomial_eq_one_or_neg_one
#print axioms rawDifference_eq_zero_or_two_or_neg_two
#print axioms translations_eq_singleton_zero
#print axioms shapeCoeff_eq_rawDifference_of_full_span

end LittMostUnfairBetWalsh
