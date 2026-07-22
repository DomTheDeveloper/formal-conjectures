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

import FormalConjectures.Other.LittMostUnfairBetWalshConstantGap
import FormalConjectures.Other.LittMostUnfairBetWalshOneEndpointGap

/-!
# Assembly of the Litt variance cases

All branches except the final two-endpoint alternative are discharged here.
The supplied hypothesis is exactly the remaining near-full-shape lemma: when
the words agree internally and differ at both endpoints, either the two
self-overlap numerators agree or the raw Walsh energy has the quarter-variance
gap required by the arithmetic endgame.
-/

set_option autoImplicit false

namespace LittMostUnfairBetWalsh

open Finset
open LittMostUnfairBet

/-- Package a nonnegative integer variance numerator and the exact energy relation. -/
theorem exists_varianceNat {n : ℕ} (A B : Word n) (hne : A ≠ B) :
    ∃ q : ℕ, varianceNum A B = (q : ℤ) ∧ rawEnergy A B = 2 * q := by
  let q := (varianceNum A B).toNat
  have hnonneg := varianceNum_nonneg A B hne
  have hcast : (q : ℤ) = varianceNum A B := Int.toNat_of_nonneg hnonneg
  refine ⟨q, hcast.symm, ?_⟩
  have henergy := rawEnergy_cast_eq_two_mul_varianceNum A B hne
  rw [← hcast] at henergy
  exact_mod_cast henergy

/-- The interior energy scale is twice the desired natural variance scale. -/
theorem four_mul_pow_pred_eq_two_mul_pow {n : ℕ} (hn : 3 ≤ n) :
    4 * 2 ^ (n - 3) = 2 * 2 ^ (n - 2) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [show m + 3 - 3 = m by omega, show m + 3 - 2 = m + 1 by omega,
    pow_succ]
  ring

/-- Assemble the exact variance cases from the remaining two-endpoint lemma. -/
theorem variance_cases_of_two_endpoint_gap {n : ℕ} (hn : 2 ≤ n)
    (A B : Word n) (hne : A ≠ B)
    (hboth :
      (∀ i : Fin n, 0 < i.val → i.val < n - 1 → A i = B i) →
      A ⟨0, by omega⟩ ≠ B ⟨0, by omega⟩ →
      A ⟨n - 1, by omega⟩ ≠ B ⟨n - 1, by omega⟩ →
      Nat.dist (overlapNum A A) (overlapNum B B) = 0 ∨
        2 * 2 ^ (n - 2) ≤ rawEnergy A B) :
    ∃ q : ℕ,
      varianceNum A B = (q : ℤ) ∧
      (Nat.dist (overlapNum A A) (overlapNum B B) = 0 ∨
        ((IsConstant A ∨ IsConstant B) ∧ 2 ^ n ≤ q) ∨
        ((¬ IsConstant A ∧ ¬ IsConstant B) ∧ 2 ^ (n - 2) ≤ q)) := by
  rcases exists_varianceNat A B hne with ⟨q, hq, henergy⟩
  refine ⟨q, hq, ?_⟩
  by_cases hdelta : Nat.dist (overlapNum A A) (overlapNum B B) = 0
  · exact Or.inl hdelta
  by_cases hconst : IsConstant A ∨ IsConstant B
  · have hz := varianceNum_ge_of_constant A B hne hconst
    rw [hq] at hz
    have hqge : 2 ^ n ≤ q := by exact_mod_cast hz
    exact Or.inr (Or.inl ⟨hconst, hqge⟩)
  have hA : ¬ IsConstant A := fun h => hconst (Or.inl h)
  have hB : ¬ IsConstant B := fun h => hconst (Or.inr h)
  have finish_energy (hraw : 2 * 2 ^ (n - 2) ≤ rawEnergy A B) :
      Nat.dist (overlapNum A A) (overlapNum B B) = 0 ∨
        ((IsConstant A ∨ IsConstant B) ∧ 2 ^ n ≤ q) ∨
        ((¬ IsConstant A ∧ ¬ IsConstant B) ∧ 2 ^ (n - 2) ≤ q) := by
    have hqge : 2 ^ (n - 2) ≤ q := by
      rw [henergy] at hraw
      omega
    exact Or.inr (Or.inr ⟨⟨hA, hB⟩, hqge⟩)
  by_cases hinterior :
      ∃ i : Fin n, 0 < i.val ∧ i.val < n - 1 ∧ A i ≠ B i
  · rcases hinterior with ⟨i, hi0, hilast, hidiff⟩
    have hn3 : 3 ≤ n := by omega
    have hraw := rawEnergy_ge_of_interior_disagreement hn3 A B i hi0 hilast hidiff
    rw [four_mul_pow_pred_eq_two_mul_pow hn3] at hraw
    exact finish_energy hraw
  have hagree : ∀ i : Fin n, 0 < i.val → i.val < n - 1 → A i = B i := by
    intro i hi0 hilast
    by_contra hidiff
    exact hinterior ⟨i, hi0, hilast, hidiff⟩
  let left : Fin n := ⟨0, by omega⟩
  let right : Fin n := ⟨n - 1, by omega⟩
  by_cases hleft : A left ≠ B left
  · by_cases hright : A right ≠ B right
    · have hbranch := hboth hagree (by simpa [left] using hleft)
        (by simpa [right] using hright)
      rcases hbranch with hzero | hraw
      · exact (hdelta hzero).elim
      · exact finish_energy hraw
    · have hrightEq : A right = B right := not_ne_iff.mp hright
      have hraw := rawEnergy_ge_of_one_endpoint_disagreement hn A B hagree
        (Or.inl ⟨by simpa [left] using hleft,
          by simpa [right] using hrightEq⟩)
      have hweaker : 2 * 2 ^ (n - 2) ≤ rawEnergy A B := by
        have hpos : 0 < 2 ^ (n - 2) := pow_pos (by omega) _
        omega
      exact finish_energy hweaker
  · have hleftEq : A left = B left := not_ne_iff.mp hleft
    by_cases hright : A right ≠ B right
    · have hraw := rawEnergy_ge_of_one_endpoint_disagreement hn A B hagree
        (Or.inr ⟨by simpa [left] using hleftEq,
          by simpa [right] using hright⟩)
      have hweaker : 2 * 2 ^ (n - 2) ≤ rawEnergy A B := by
        have hpos : 0 < 2 ^ (n - 2) := pow_pos (by omega) _
        omega
      exact finish_energy hweaker
    · have hrightEq : A right = B right := not_ne_iff.mp hright
      exfalso
      apply hne
      funext i
      by_cases hi0 : i.val = 0
      · have hi : i = left := Fin.ext hi0
        rw [hi]
        exact hleftEq
      by_cases hilast : i.val = n - 1
      · have hi : i = right := Fin.ext hilast
        rw [hi]
        exact hrightEq
      exact hagree i (by omega) (by omega)

/-- The Formal Conjectures inequality follows from the final two-endpoint gap. -/
theorem most_unfair_litt_bound_of_two_endpoint_gap {n : ℕ} (hn : 2 ≤ n)
    (A B : Word n) (hne : A ≠ B)
    (hboth :
      (∀ i : Fin n, 0 < i.val → i.val < n - 1 → A i = B i) →
      A ⟨0, by omega⟩ ≠ B ⟨0, by omega⟩ →
      A ⟨n - 1, by omega⟩ ≠ B ⟨n - 1, by omega⟩ →
      Nat.dist (overlapNum A A) (overlapNum B B) = 0 ∨
        2 * 2 ^ (n - 2) ≤ rawEnergy A B) :
    selfOverlapDelta A B ^ 2 * ((2 ^ n : ℕ) : ℤ) ≤
      candidateNum n ^ 2 * varianceNum A B := by
  rcases variance_cases_of_two_endpoint_gap hn A B hne hboth with
    ⟨q, hq, hcases⟩
  exact most_unfair_litt_bound_of_variance_cases hn A B q hq hcases

#print axioms exists_varianceNat
#print axioms variance_cases_of_two_endpoint_gap
#print axioms most_unfair_litt_bound_of_two_endpoint_gap

end LittMostUnfairBetWalsh
