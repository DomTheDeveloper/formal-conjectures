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

import FormalConjectures.Other.LittMostUnfairBetWalshTwoEndpointConstant

/-!
# Completion of the two-endpoint Litt gap
-/

set_option autoImplicit false

namespace LittMostUnfairBetWalsh

open Finset
open LittMostUnfairBet

/-- The common interior either has an unequal adjacent pair or is constant. -/
theorem interior_adjacency_or_constant {n : ℕ} (hn : 3 ≤ n) (A : Word n) :
    (∃ j : Fin n, 0 < j.val ∧ j.val < n - 2 ∧
      A j ≠ A ⟨j.val + 1, by omega⟩) ∨
    (∃ c : Bool, ∀ i : Fin n,
      0 < i.val → i.val < n - 1 → A i = c) := by
  by_cases hdiff : ∃ j : Fin n, 0 < j.val ∧ j.val < n - 2 ∧
      A j ≠ A ⟨j.val + 1, by omega⟩
  · exact Or.inl hdiff
  · right
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    let C : Word (m + 1) := fun i => A ⟨i.val + 1, by omega⟩
    have hCadj : ∀ i : Fin m, C i.castSucc = C i.succ := by
      intro i
      by_contra hne
      apply hdiff
      refine ⟨⟨i.val + 1, by omega⟩, by omega, by omega, ?_⟩
      simpa [C] using hne
    rcases isConstant_of_adjacent_eq C hCadj with ⟨c, hC⟩
    refine ⟨c, ?_⟩
    intro i hipos hiend
    let j : Fin (m + 1) := ⟨i.val - 1, by omega⟩
    have hj := congrFun hC j
    simpa [C, constantWord, j] using hj

/-- In the two-endpoint branch, either the numerator vanishes or raw energy has
the required `2^(n-1)` gap. -/
theorem rawEnergy_gap_or_delta_zero_of_two_endpoint_disagreement {n : ℕ}
    (hn : 3 ≤ n) (A B : Word n)
    (hinterior : ∀ i : Fin n, 0 < i.val → i.val < n - 1 → A i = B i)
    (hleft : A ⟨0, by omega⟩ ≠ B ⟨0, by omega⟩)
    (hright : A ⟨n - 1, by omega⟩ ≠ B ⟨n - 1, by omega⟩) :
    selfOverlapDelta A B = 0 ∨ 2 ^ (n - 1) ≤ rawEnergy A B := by
  rcases interior_adjacency_or_constant hn A with hadj | hconst
  · rcases hadj with ⟨j, hjpos, hjpen, hjdiff⟩
    right
    have hn4 : 4 ≤ n := by omega
    have hgap := rawEnergy_ge_of_two_endpoint_adjacency_disagreement hn4
      A B hinterior hleft hright j hjpos hjpen hjdiff
    have hpow : 16 * 2 ^ (n - 4) = 2 ^ n := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn4
      simp [pow_add, mul_assoc, mul_comm, mul_left_comm]
    rw [hpow] at hgap
    have hle : 2 ^ (n - 1) ≤ 2 ^ n :=
      pow_le_pow_right' (by norm_num) (by omega)
    exact hle.trans hgap
  · rcases hconst with ⟨c, hconst⟩
    by_cases hends : A ⟨0, by omega⟩ = A ⟨n - 1, by omega⟩
    · right
      have hgap := rawEnergy_ge_of_constant_interior_equal_endpoints hn
        A B c hinterior hconst hleft hright hends
      have hpow : 16 * 2 ^ (n - 3) = 2 ^ (n + 1) := by
        obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
        simp [pow_add, mul_assoc, mul_comm, mul_left_comm]
      rw [hpow] at hgap
      have hle : 2 ^ (n - 1) ≤ 2 ^ (n + 1) :=
        pow_le_pow_right' (by norm_num) (by omega)
      exact hle.trans hgap
    · left
      exact selfOverlapDelta_eq_zero_of_constant_interior_opposite_endpoints hn
        A B c hinterior hconst hleft hright hends

#print axioms interior_adjacency_or_constant
#print axioms rawEnergy_gap_or_delta_zero_of_two_endpoint_disagreement

end LittMostUnfairBetWalsh
