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
# The most unfair Litt coin-word bet

Development file for the finite extremal theorem underlying the fair-coin
Litt game.  The published asymptotic formula reduces the leading unfairness
to a self-overlap difference divided by the asymptotic variance.  Here the
variance is represented by its Walsh translation-shape energy.

The final target is a natural-number squared inequality, avoiding division
and square roots.
-/

set_option autoImplicit false

namespace LittMostUnfairBet

/-- A binary word of length `n`. -/
abbrev Word (n : ℕ) := {w : List Bool // w.length = n}

/-- The `±1` encoding of one coin letter. -/
def sign : Bool → ℤ
  | false => 1
  | true => -1

/-- The sign at position `i`; the default branch is irrelevant for valid positions. -/
def letterSign {n : ℕ} (w : Word n) (i : ℕ) : ℤ :=
  match w.1.get? i with
  | some b => sign b
  | none => 1

/-- Product of the signs in the coordinate set `S`. -/
def monomial {n : ℕ} (w : Word n) (S : Finset ℕ) : ℤ :=
  ∏ i ∈ S, letterSign w i

/-- All normalized nonempty translation shapes in a word of length `n`.
A shape is normalized by requiring that it contain coordinate `0`. -/
def shapes (n : ℕ) : Finset (Finset ℕ) :=
  (Finset.range n).powerset.filter (fun S => 0 ∈ S)

/-- Whether translating `S` to the right by `t` stays inside `range n`. -/
def ValidTranslation (n : ℕ) (S : Finset ℕ) (t : ℕ) : Prop :=
  ∀ i ∈ S, i + t < n

/-- Valid translations of a normalized shape. -/
def translations (n : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (Finset.range n).filter (ValidTranslation n S)

/-- Translate a finite coordinate set to the right by `t`. -/
def translate (S : Finset ℕ) (t : ℕ) : Finset ℕ :=
  S.image (fun i => i + t)

/-- Half the difference of two `±1` monomials, written without integer division. -/
def signedDifference {n : ℕ} (A B : Word n) (S : Finset ℕ) : ℤ :=
  if monomial A S = monomial B S then 0 else monomial A S

/-- Walsh coefficient attached to one translation shape. -/
def shapeCoeff {n : ℕ} (A B : Word n) (S : Finset ℕ) : ℤ :=
  ∑ t ∈ translations n S, signedDifference A B (translate S t)

/-- Integer Walsh translation-shape energy.

If `D = 1 + θAA + θBB - θAB - θBA`, then the elementary Walsh expansion gives
`D = 2^(1-n) * energy A B`.
-/
def energy {n : ℕ} (A B : Word n) : ℕ :=
  ∑ S ∈ shapes n, (shapeCoeff A B S).natAbs ^ 2

/-- Weighted prefix/suffix overlap numerator, with common denominator `2^n`. -/
def overlapNum {n : ℕ} (A B : Word n) : ℕ :=
  ∑ k ∈ Finset.Ico 1 n,
    if A.1.drop (n - k) = B.1.take k then 2 ^ k else 0

/-- Proper self-overlap numerator. -/
def selfOverlapNum {n : ℕ} (A : Word n) : ℕ := overlapNum A A

/-- Absolute self-overlap difference. -/
def overlapDifference {n : ℕ} (A B : Word n) : ℕ :=
  Nat.dist (selfOverlapNum A) (selfOverlapNum B)

/-- A constant binary word. -/
def constantWord (n : ℕ) (b : Bool) : Word n :=
  ⟨List.replicate n b, by simp⟩

/-- The endpoint-flip word `H^m T`, of length `m+1`. -/
def endpointWord (m : ℕ) : Word (m + 1) :=
  ⟨List.replicate m false ++ [true], by simp⟩

/-- Being one of the two constant binary words. -/
def IsConstant {n : ℕ} (A : Word n) : Prop :=
  A = constantWord n false ∨ A = constantWord n true

/-- The largest possible proper-overlap numerator for length `n`. -/
def maxOverlapNum (n : ℕ) : ℕ := 2 ^ n - 2

/-- Cleared-denominator square of the finite Litt extremal functional. -/
def clearedScoreSq {n : ℕ} (A B : Word n) : ℕ :=
  overlapDifference A B ^ 2 * 2 ^ (n - 1)

/-- Cleared-denominator candidate bound. -/
def clearedCandidateSq {n : ℕ} (A B : Word n) : ℕ :=
  maxOverlapNum n ^ 2 * energy A B

/-! ## Arithmetic endgame -/

/-- Constant-word scalar branch. -/
theorem constant_branch_arithmetic
    (M delta E p : ℕ) (hdelta : delta ≤ M) (hE : p ≤ E) :
    delta ^ 2 * p ≤ M ^ 2 * E := by
  exact Nat.mul_le_mul (Nat.pow_le_pow_left hdelta 2) hE

/-- Nonconstant-word scalar branch in the normalization used by `energy`. -/
theorem nonconstant_branch_arithmetic
    (x delta E : ℕ)
    (hx : 2 ≤ x)
    (hdelta : delta ≤ x - 2)
    (hE : x / 4 ≤ E) :
    delta ^ 2 * x ≤ (2 * x - 2) ^ 2 * E := by
  have hsq : 4 * delta ^ 2 ≤ (2 * x - 2) ^ 2 := by
    have hdx : delta + 2 ≤ x := Nat.le_of_sub_le_sub_right hdelta
    nlinarith
  calc
    delta ^ 2 * x = (4 * delta ^ 2) * (x / 4) := by
      sorry
    _ ≤ (2 * x - 2) ^ 2 * E := Nat.mul_le_mul hsq hE

/-! ## Word-level lemmas still being discharged -/

/-- Every proper self-overlap numerator is at most `2^n - 2`. -/
theorem selfOverlapNum_le_max {n : ℕ} (A : Word n) :
    selfOverlapNum A ≤ maxOverlapNum n := by
  sorry

/-- A nonconstant word has no overlap of length `n-1`. -/
theorem selfOverlapNum_le_nonconstant {n : ℕ} (hn : 2 ≤ n) (A : Word n)
    (hA : ¬ IsConstant A) :
    selfOverlapNum A ≤ 2 ^ (n - 1) - 2 := by
  sorry

/-- If one word is constant and the words are distinct, the Walsh energy is large. -/
theorem energy_ge_of_constant {n : ℕ} (hn : 1 ≤ n) (A B : Word n)
    (hne : A ≠ B) (hconst : IsConstant A ∨ IsConstant B) :
    2 ^ (n - 1) ≤ energy A B := by
  sorry

/-- For two nonconstant words, either the reversal-degenerate numerator vanishes,
or the Walsh energy has a uniform quarter-variance gap. -/
theorem energy_gap_or_overlap_eq {n : ℕ} (hn : 2 ≤ n) (A B : Word n)
    (hA : ¬ IsConstant A) (hB : ¬ IsConstant B) :
    overlapDifference A B = 0 ∨ 2 ^ (n - 3) ≤ energy A B := by
  sorry

/-- Global squared extremality of the endpoint-flip versus constant-word pair. -/
theorem most_unfair_litt_bound {n : ℕ} (hn : 2 ≤ n) (A B : Word n) (hne : A ≠ B) :
    clearedScoreSq A B ≤ clearedCandidateSq A B := by
  sorry

/-- The proposed endpoint-flip pair attains the bound. -/
theorem endpoint_pair_attains (m : ℕ) :
    clearedScoreSq (endpointWord (m + 1)) (constantWord (m + 2) false) =
      maxOverlapNum (m + 2) ^ 2 * 2 ^ (m + 1) := by
  sorry

end LittMostUnfairBet
