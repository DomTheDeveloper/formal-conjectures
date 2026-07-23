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
# Walsh foundations for the most unfair Litt coin-word bet

This file develops the finite Boolean-cube identities needed for the remaining
variance bridge.  It contains no probability theory: the core facts are the
powerset product expansion and orthogonality of the `±1` characters.
-/

set_option autoImplicit false

namespace LittMostUnfairBetWalsh

open Finset

/-- Expanding `∏ᵢ (1 + xᵢ)` chooses a subset of coordinates. -/
theorem sum_powerset_prod {α R : Type*} [DecidableEq α] [CommRing R]
    (s : Finset α) (x : α → R) :
    (∑ t ∈ s.powerset, ∏ i ∈ t, x i) = ∏ i ∈ s, (1 + x i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_powerset_insert ha]
      have hsecond :
          (∑ t ∈ s.powerset, ∏ i ∈ insert a t, x i) =
            x a * ∑ t ∈ s.powerset, ∏ i ∈ t, x i := by
        calc
          (∑ t ∈ s.powerset, ∏ i ∈ insert a t, x i) =
              ∑ t ∈ s.powerset, x a * ∏ i ∈ t, x i := by
            apply Finset.sum_congr rfl
            intro t ht
            have hat : a ∉ t := by
              intro hat
              exact ha ((Finset.mem_powerset.mp ht) hat)
            rw [Finset.prod_insert hat]
          _ = x a * ∑ t ∈ s.powerset, ∏ i ∈ t, x i := by
            rw [Finset.mul_sum]
      rw [hsecond, ih, Finset.prod_insert ha]
      ring

/-- The `±1` encoding of a fair-coin letter. -/
def coinSign : Bool → ℤ
  | false => 1
  | true => -1

@[simp] theorem coinSign_mul_self (b : Bool) : coinSign b * coinSign b = 1 := by
  cases b <;> rfl

/-- Two unequal coin signs multiply to `-1`. -/
theorem coinSign_mul_eq_neg_one_of_ne {a b : Bool} (h : a ≠ b) :
    coinSign a * coinSign b = -1 := by
  cases a <;> cases b <;> simp [coinSign] at h ⊢

/-- The Boolean-cube character product is `2^n` on the diagonal and zero off it. -/
theorem prod_one_add_coinSign_mul {n : ℕ} (A B : Fin n → Bool) :
    (∏ i ∈ Finset.univ, (1 : ℤ) + coinSign (A i) * coinSign (B i)) =
      if A = B then 2 ^ n else 0 := by
  classical
  by_cases hAB : A = B
  · subst B
    simp [hAB]
  · rw [if_neg hAB]
    have hex : ∃ i : Fin n, A i ≠ B i := by
      by_contra hnone
      apply hAB
      funext i
      exact not_ne_iff.mp (not_exists.mp hnone i)
    rcases hex with ⟨i, hi⟩
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [coinSign_mul_eq_neg_one_of_ne hi]
    norm_num

/-- A Walsh monomial indexed by a finite coordinate set. -/
def monomial {α : Type*} [DecidableEq α] (x : α → ℤ) (s : Finset α) : ℤ :=
  ∏ i ∈ s, x i

/-- Multiplying two Walsh monomials multiplies their coordinate functions. -/
theorem monomial_mul {α : Type*} [DecidableEq α]
    (x y : α → ℤ) (s : Finset α) :
    monomial x s * monomial y s = monomial (fun i => x i * y i) s := by
  simp [monomial, Finset.prod_mul_distrib]

/-- Summing products of Walsh monomials over all subsets gives the character
orthogonality product. -/
theorem sum_powerset_monomial_mul {α : Type*} [DecidableEq α]
    (s : Finset α) (x y : α → ℤ) :
    (∑ t ∈ s.powerset, monomial x t * monomial y t) =
      ∏ i ∈ s, ((1 : ℤ) + x i * y i) := by
  calc
    (∑ t ∈ s.powerset, monomial x t * monomial y t) =
        ∑ t ∈ s.powerset, monomial (fun i => x i * y i) t := by
      apply Finset.sum_congr rfl
      intro t ht
      exact monomial_mul x y t
    _ = ∏ i ∈ s, ((1 : ℤ) + x i * y i) := by
      simpa [monomial] using
        (sum_powerset_prod (R := ℤ) s (fun i => x i * y i))

#print axioms sum_powerset_prod
#print axioms prod_one_add_coinSign_mul
#print axioms sum_powerset_monomial_mul

end LittMostUnfairBetWalsh
