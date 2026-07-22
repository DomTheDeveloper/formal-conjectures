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
Litt game. The published asymptotic formula reduces the leading unfairness
to a self-overlap difference divided by the asymptotic variance. Here the
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

/-- Being a constant binary word. -/
def IsConstant {n : ℕ} (A : Word n) : Prop :=
  ∃ b : Bool, A = constantWord n b

/-- The largest possible proper-overlap numerator for length `n`. -/
def maxOverlapNum (n : ℕ) : ℕ := 2 ^ n - 2

/-- Cleared-denominator square of the finite Litt extremal functional. -/
def clearedScoreSq {n : ℕ} (A B : Word n) : ℕ :=
  overlapDifference A B ^ 2 * 2 ^ (n - 1)

/-- Cleared-denominator candidate bound. -/
def clearedCandidateSq {n : ℕ} (A B : Word n) : ℕ :=
  maxOverlapNum n ^ 2 * energy A B

/-! ## Elementary overlap bounds -/

/-- The geometric sum used by all overlap estimates. -/
lemma sum_pow_two_Ico : ∀ n : ℕ, (∑ k ∈ Finset.Ico 1 n, 2 ^ k) = 2 ^ n - 2
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
      rw [Nat.Ico_succ_right_eq_insert_Ico (by omega)]
      simp [sum_pow_two_Ico (n + 1), pow_succ]

/-- A list whose tail equals its initial segment of the same length is constant. -/
lemma exists_eq_replicate_of_drop_eq_take : ∀ l : List Bool,
    l.drop 1 = l.take (l.length - 1) →
      ∃ b : Bool, l = List.replicate l.length b
  | [], _ => ⟨false, by simp⟩
  | [a], _ => ⟨a, by simp⟩
  | a :: b :: t, h => by
      have hcons : b :: t = a :: (b :: t).take t.length := by
        simpa using h
      have hab : b = a := (List.cons.inj hcons).1
      have ht : t = (b :: t).take t.length := (List.cons.inj hcons).2
      have htail : (b :: t).drop 1 = (b :: t).take ((b :: t).length - 1) := by
        simpa using ht
      rcases exists_eq_replicate_of_drop_eq_take (b :: t) htail with ⟨c, hc⟩
      have hbc : b = c := by
        have hhead := congrArg List.head? hc
        simpa using hhead
      refine ⟨c, ?_⟩
      rw [← hab, hbc, hc]
      simp

/-- Every proper self-overlap numerator is at most `2^n - 2`. -/
theorem selfOverlapNum_le_max {n : ℕ} (A : Word n) :
    selfOverlapNum A ≤ maxOverlapNum n := by
  calc
    selfOverlapNum A ≤ ∑ k ∈ Finset.Ico 1 n, 2 ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      split <;> simp
    _ = maxOverlapNum n := by
      simp [maxOverlapNum, sum_pow_two_Ico]

/-- A nonconstant word has no overlap of length `n-1`. -/
theorem selfOverlapNum_le_nonconstant {n : ℕ} (hn : 2 ≤ n) (A : Word n)
    (hA : ¬ IsConstant A) :
    selfOverlapNum A ≤ 2 ^ (n - 1) - 2 := by
  have htopMem : n - 1 ∈ Finset.Ico 1 n := by
    simp only [Finset.mem_Ico]
    omega
  have herase : (Finset.Ico 1 n).erase (n - 1) = Finset.Ico 1 (n - 1) := by
    ext k
    simp only [Finset.mem_erase, Finset.mem_Ico]
    omega
  have htop : A.1.drop (n - (n - 1)) ≠ A.1.take (n - 1) := by
    intro h
    have hone : n - (n - 1) = 1 := by omega
    rw [hone] at h
    rcases exists_eq_replicate_of_drop_eq_take A.1 (by simpa [A.2] using h) with ⟨b, hb⟩
    apply hA
    refine ⟨b, Subtype.ext ?_⟩
    simpa [constantWord, A.2] using hb
  rw [selfOverlapNum, overlapNum, ← Finset.sum_erase_add _ _ htopMem, herase]
  simp only [htop, if_false, add_zero]
  calc
    (∑ k ∈ Finset.Ico 1 (n - 1),
        if A.1.drop (n - k) = A.1.take k then 2 ^ k else 0) ≤
        ∑ k ∈ Finset.Ico 1 (n - 1), 2 ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      split <;> simp
    _ = 2 ^ (n - 1) - 2 := sum_pow_two_Ico (n - 1)

/-! ## Arithmetic endgame -/

/-- Constant-word scalar branch. -/
theorem constant_branch_arithmetic
    (M delta E p : ℕ) (hdelta : delta ≤ M) (hE : p ≤ E) :
    delta ^ 2 * p ≤ M ^ 2 * E := by
  exact Nat.mul_le_mul (Nat.pow_le_pow_left hdelta 2) hE

/-- Nonconstant-word scalar branch after writing the power-of-two factor as `4 * p`. -/
theorem nonconstant_branch_arithmetic
    (M delta E p : ℕ)
    (hdelta : 2 * delta ≤ M)
    (hE : p ≤ E) :
    delta ^ 2 * (4 * p) ≤ M ^ 2 * E := by
  have hsq : (2 * delta) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left hdelta 2
  calc
    delta ^ 2 * (4 * p) = (2 * delta) ^ 2 * p := by ring
    _ ≤ M ^ 2 * E := Nat.mul_le_mul hsq hE

/-! ## Walsh-energy lemmas -/

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
