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

import FormalConjectures.Other.LittMostUnfairBetWalshCorrelation
import FormalConjectures.Other.LittMostUnfairBetWalshShapes

/-!
# Fixed-shift Walsh correlations for Litt coin words

For a shift `h`, the common coordinate range has length `n-h`. Character
orthogonality turns the sum over all subsets of this range into four tests of
prefix/suffix block equality.
-/

set_option autoImplicit false

namespace LittMostUnfairBetWalsh

open Finset
open LittMostUnfairBet

/-- The prefix block of length `n-h`. -/
def prefixBlock {n : ℕ} (A : Word n) (h : ℕ) : Fin (n - h) → Bool :=
  fun i => A ⟨i.val, lt_of_lt_of_le i.isLt (Nat.sub_le n h)⟩

/-- The block of length `n-h` starting at coordinate `h`. -/
def suffixBlock {n : ℕ} (A : Word n) (h : ℕ) : Fin (n - h) → Bool :=
  fun i => A ⟨h + i.val, by omega⟩

/-- A Walsh monomial after shifting every coordinate by `h`. -/
def shiftedMonomial {n : ℕ} (A : Word n) (h : ℕ) (S : Finset ℕ) : ℤ :=
  ∏ i ∈ S, letterSign A (i + h)

/-- Raw difference of two shifted word monomials. -/
def shiftedRawDifference {n : ℕ} (A B : Word n) (h : ℕ)
    (S : Finset ℕ) : ℤ :=
  shiftedMonomial A h S - shiftedMonomial B h S

/-- The product over a common block is diagonal character orthogonality. -/
theorem prod_range_one_add_letterSign_shift {n h : ℕ} (A C : Word n) :
    (∏ i ∈ Finset.range (n - h),
      ((1 : ℤ) + letterSign A i * letterSign C (i + h))) =
      if prefixBlock A h = suffixBlock C h then 2 ^ (n - h) else 0 := by
  rw [Finset.prod_range]
  simpa [prefixBlock, suffixBlock, letterSign] using
    (prod_one_add_coinSign_mul (prefixBlock A h) (suffixBlock C h))

/-- One pair of shifted word monomials sums to a block-equality test. -/
theorem sum_powerset_natMonomial_mul_shifted {n h : ℕ} (A C : Word n) :
    (∑ S ∈ (Finset.range (n - h)).powerset,
      natMonomial A S * shiftedMonomial C h S) =
      if prefixBlock A h = suffixBlock C h then 2 ^ (n - h) else 0 := by
  calc
    (∑ S ∈ (Finset.range (n - h)).powerset,
      natMonomial A S * shiftedMonomial C h S) =
        ∏ i ∈ Finset.range (n - h),
          ((1 : ℤ) + letterSign A i * letterSign C (i + h)) := by
      simpa [natMonomial, shiftedMonomial] using
        (sum_powerset_monomial_mul
          (s := Finset.range (n - h))
          (letterSign A) (fun i => letterSign C (i + h)))
    _ = if prefixBlock A h = suffixBlock C h then 2 ^ (n - h) else 0 :=
      prod_range_one_add_letterSign_shift A C

/-- The exact four-term fixed-shift correlation identity. -/
theorem sum_powerset_rawDifference_mul_shiftedRawDifference {n h : ℕ}
    (A B : Word n) :
    (∑ S ∈ (Finset.range (n - h)).powerset,
      rawDifference A B S * shiftedRawDifference A B h S) =
      (if prefixBlock A h = suffixBlock A h then 2 ^ (n - h) else 0) -
      (if prefixBlock A h = suffixBlock B h then 2 ^ (n - h) else 0) -
      (if prefixBlock B h = suffixBlock A h then 2 ^ (n - h) else 0) +
      (if prefixBlock B h = suffixBlock B h then 2 ^ (n - h) else 0) := by
  calc
    (∑ S ∈ (Finset.range (n - h)).powerset,
      rawDifference A B S * shiftedRawDifference A B h S) =
      (∑ S ∈ (Finset.range (n - h)).powerset,
        natMonomial A S * shiftedMonomial A h S) -
      (∑ S ∈ (Finset.range (n - h)).powerset,
        natMonomial A S * shiftedMonomial B h S) -
      (∑ S ∈ (Finset.range (n - h)).powerset,
        natMonomial B S * shiftedMonomial A h S) +
      (∑ S ∈ (Finset.range (n - h)).powerset,
        natMonomial B S * shiftedMonomial B h S) := by
      simp only [rawDifference, shiftedRawDifference, sub_mul, mul_sub,
        Finset.sum_sub_distrib]
      ring
    _ =
      (if prefixBlock A h = suffixBlock A h then 2 ^ (n - h) else 0) -
      (if prefixBlock A h = suffixBlock B h then 2 ^ (n - h) else 0) -
      (if prefixBlock B h = suffixBlock A h then 2 ^ (n - h) else 0) +
      (if prefixBlock B h = suffixBlock B h then 2 ^ (n - h) else 0) := by
      rw [sum_powerset_natMonomial_mul_shifted A A,
        sum_powerset_natMonomial_mul_shifted A B,
        sum_powerset_natMonomial_mul_shifted B A,
        sum_powerset_natMonomial_mul_shifted B B]

/-- At shift zero the blocks are the original words. -/
theorem prefixBlock_zero {n : ℕ} (A : Word n) : prefixBlock A 0 = A := by
  funext i
  rfl

/-- At shift zero the suffix block is also the original word. -/
theorem suffixBlock_zero {n : ℕ} (A : Word n) : suffixBlock A 0 = A := by
  funext i
  rfl

/-- For distinct words the diagonal raw correlation is `2^(n+1)`. -/
theorem diagonal_raw_correlation {n : ℕ} (A B : Word n) (hne : A ≠ B) :
    (∑ S ∈ (Finset.range n).powerset,
      rawDifference A B S * rawDifference A B S) = 2 ^ (n + 1) := by
  have hcorr := sum_powerset_rawDifference_mul_shiftedRawDifference
    (n := n) (h := 0) A B
  simpa [shiftedRawDifference, shiftedMonomial, prefixBlock_zero,
    suffixBlock_zero, hne, pow_succ] using hcorr

#print axioms sum_powerset_rawDifference_mul_shiftedRawDifference
#print axioms diagonal_raw_correlation

end LittMostUnfairBetWalsh
