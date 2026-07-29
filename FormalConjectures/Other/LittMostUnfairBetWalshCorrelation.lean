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

import FormalConjectures.Other.LittMostUnfairBetWalsh

/-!
# Walsh correlation identities for Litt coin words

The difference of two cylinder indicators has Walsh coefficients given by the
differences of their character monomials.  This file proves the exact four-term
correlation identity on a finite Boolean cube.
-/

set_option autoImplicit false

namespace LittMostUnfairBetWalsh

open Finset

/-- The Walsh monomial of a binary word on a subset of coordinates. -/
def boolMonomial {n : ℕ} (A : Fin n → Bool) (s : Finset (Fin n)) : ℤ :=
  monomial (fun i => coinSign (A i)) s

/-- Character orthogonality after summing over every subset of `Fin n`. -/
theorem sum_powerset_boolMonomial_mul {n : ℕ} (A B : Fin n → Bool) :
    (∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
      boolMonomial A s * boolMonomial B s) =
        if A = B then 2 ^ n else 0 := by
  calc
    (∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
      boolMonomial A s * boolMonomial B s) =
        ∏ i ∈ (Finset.univ : Finset (Fin n)),
          ((1 : ℤ) + coinSign (A i) * coinSign (B i)) := by
      simpa [boolMonomial] using
        (sum_powerset_monomial_mul
          (s := (Finset.univ : Finset (Fin n)))
          (fun i => coinSign (A i)) (fun i => coinSign (B i)))
    _ = if A = B then 2 ^ n else 0 := by
      simpa using prod_one_add_coinSign_mul A B

/-- The exact four-term Walsh correlation formula for two word differences. -/
theorem sum_powerset_difference_mul_difference {n : ℕ}
    (A B C D : Fin n → Bool) :
    (∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
      (boolMonomial A s - boolMonomial B s) *
        (boolMonomial C s - boolMonomial D s)) =
      (if A = C then 2 ^ n else 0) -
      (if A = D then 2 ^ n else 0) -
      (if B = C then 2 ^ n else 0) +
      (if B = D then 2 ^ n else 0) := by
  calc
    (∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
      (boolMonomial A s - boolMonomial B s) *
        (boolMonomial C s - boolMonomial D s)) =
      (∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
        boolMonomial A s * boolMonomial C s) -
      (∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
        boolMonomial A s * boolMonomial D s) -
      (∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
        boolMonomial B s * boolMonomial C s) +
      (∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
        boolMonomial B s * boolMonomial D s) := by
      simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
      ring
    _ =
      (if A = C then 2 ^ n else 0) -
      (if A = D then 2 ^ n else 0) -
      (if B = C then 2 ^ n else 0) +
      (if B = D then 2 ^ n else 0) := by
      rw [sum_powerset_boolMonomial_mul A C,
        sum_powerset_boolMonomial_mul A D,
        sum_powerset_boolMonomial_mul B C,
        sum_powerset_boolMonomial_mul B D]

/-- The empty Walsh coefficient cancels in every word difference. -/
@[simp] theorem boolMonomial_empty {n : ℕ} (A : Fin n → Bool) :
    boolMonomial A ∅ = 1 := by
  simp [boolMonomial, monomial]

#print axioms sum_powerset_boolMonomial_mul
#print axioms sum_powerset_difference_mul_difference

end LittMostUnfairBetWalsh
