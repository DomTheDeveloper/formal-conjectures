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

/-!
# Arithmetic and overlap core for the most unfair Litt coin-word bet

The complete combinatorial proof is recorded in `LittMostUnfairBetProof.md`.
This file kernelizes the elementary overlap bounds and the denominator-cleared
arithmetic endgame. The remaining universal bridge is the Walsh translation-
shape variance lemma.
-/

set_option autoImplicit false

namespace LittMostUnfairBet

/-- A word is constant when all coordinates contain one bit. -/
def IsConstant {n : ℕ} (A : Word n) : Prop := ∃ b, A = constantWord n b

/-- Every overlap numerator is bounded by the full proper geometric sum. -/
theorem overlapNum_le_candidate {n : ℕ} (A B : Word n) :
    overlapNum A B ≤ 2 ^ n - 2 := by
  cases n with
  | zero => simp [overlapNum]
  | succ m =>
      calc
        overlapNum A B ≤
            ∑ k : Fin (m + 1), if k.val + 1 < m + 1 then 2 ^ (k.val + 1) else 0 := by
          unfold overlapNum
          apply Finset.sum_le_sum
          intro k hk
          by_cases hp : k.val + 1 < m + 1
          · by_cases heq : wordSuffix A k = wordPrefix B k <;> simp [hp, heq]
          · simp [hp]
        _ = 2 ^ (m + 1) - 2 := sum_proper_pow_two m

/-- If adjacent letters agree throughout a nonempty word, then it is constant. -/
theorem isConstant_of_adjacent_eq {m : ℕ} (A : Word (m + 1))
    (hadj : ∀ i : Fin m, A i.castSucc = A i.succ) : IsConstant A := by
  refine ⟨A 0, funext ?_⟩
  intro i
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
      rw [← hadj i]
      exact ih

/-- A self-overlap of length `n-1` forces the word to be constant. -/
theorem isConstant_of_top_border {m : ℕ} (A : Word (m + 2))
    (hborder :
      wordSuffix A ⟨m, by omega⟩ = wordPrefix A ⟨m, by omega⟩) :
    IsConstant A := by
  apply isConstant_of_adjacent_eq A
  intro i
  have h := congrFun hborder i
  change A ⟨m + 2 - m - 1 + i.val, by omega⟩ = A ⟨i.val, by omega⟩ at h
  have hidx : m + 2 - m - 1 + i.val = i.val + 1 := by omega
  simpa [hidx] using h.symm

/-- A nonconstant word has no overlap of length `n-1`; hence its self-overlap
numerator is at most `2^(n-1)-2`. -/
theorem selfOverlapNum_le_nonconstant {n : ℕ} (hn : 2 ≤ n) (A : Word n)
    (hA : ¬ IsConstant A) : overlapNum A A ≤ 2 ^ (n - 1) - 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have htop :
      wordSuffix A ⟨m, by omega⟩ ≠ wordPrefix A ⟨m, by omega⟩ := by
    intro h
    exact hA (isConstant_of_top_border A h)
  unfold overlapNum
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_last, lt_self_iff_false, false_and, if_false, add_zero]
  calc
    (∑ k : Fin (m + 1),
      if k.val + 1 < m + 2 ∧ wordSuffix A k.castSucc = wordPrefix A k.castSucc then
        2 ^ (k.val + 1)
      else 0) ≤
        ∑ k : Fin (m + 1), if k.val + 1 < m + 1 then 2 ^ (k.val + 1) else 0 := by
      apply Finset.sum_le_sum
      intro k hk
      by_cases hkm : k.val = m
      · have hk_last : k = Fin.last m := by
          apply Fin.ext
          simpa using hkm
        subst k
        simp [htop]
      · have hlt : k.val + 1 < m + 1 := by omega
        by_cases heq : wordSuffix A k.castSucc = wordPrefix A k.castSucc <;>
          simp [hlt, heq]
    _ = 2 ^ (m + 1) - 2 := sum_proper_pow_two m

/-- The self-overlap distance is bounded by the largest self-overlap numerator. -/
theorem selfOverlap_dist_le_candidate {n : ℕ} (A B : Word n) :
    Nat.dist (overlapNum A A) (overlapNum B B) ≤ 2 ^ n - 2 := by
  have hAA := overlapNum_le_candidate A A
  have hBB := overlapNum_le_candidate B B
  by_cases hle : overlapNum A A ≤ overlapNum B B
  · rw [Nat.dist_eq_sub_of_le hle]
    omega
  · have hge : overlapNum B B ≤ overlapNum A A := Nat.le_of_lt (Nat.lt_of_not_ge hle)
    rw [Nat.dist_eq_sub_of_le_right hge]
    omega

/-- For two nonconstant words, twice the self-overlap distance is at most the
candidate numerator `2^n-2`. -/
theorem two_mul_selfOverlap_dist_le_candidate {n : ℕ} (hn : 2 ≤ n)
    (A B : Word n) (hA : ¬ IsConstant A) (hB : ¬ IsConstant B) :
    2 * Nat.dist (overlapNum A A) (overlapNum B B) ≤ 2 ^ n - 2 := by
  have hAA := selfOverlapNum_le_nonconstant hn A hA
  have hBB := selfOverlapNum_le_nonconstant hn B hB
  have hdist : Nat.dist (overlapNum A A) (overlapNum B B) ≤ 2 ^ (n - 1) - 2 := by
    by_cases hle : overlapNum A A ≤ overlapNum B B
    · rw [Nat.dist_eq_sub_of_le hle]
      omega
    · have hge : overlapNum B B ≤ overlapNum A A := Nat.le_of_lt (Nat.lt_of_not_ge hle)
      rw [Nat.dist_eq_sub_of_le_right hge]
      omega
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
    omega
  rw [hpow]
  omega

/-! ## Denominator-cleared arithmetic endgame -/

/-- Constant-word branch. -/
theorem constant_branch_arithmetic
    (candidate delta variance denominator : ℕ)
    (hdelta : delta ≤ candidate)
    (hvariance : denominator ≤ variance) :
    delta ^ 2 * denominator ≤ candidate ^ 2 * variance := by
  exact Nat.mul_le_mul (Nat.pow_le_pow_left hdelta 2) hvariance

/-- Nonconstant branch after writing `2^n = 4 * 2^(n-2)`. -/
theorem nonconstant_branch_arithmetic
    (candidate delta variance quarterDenominator : ℕ)
    (hdelta : 2 * delta ≤ candidate)
    (hvariance : quarterDenominator ≤ variance) :
    delta ^ 2 * (4 * quarterDenominator) ≤ candidate ^ 2 * variance := by
  have hsq : (2 * delta) ^ 2 ≤ candidate ^ 2 := Nat.pow_le_pow_left hdelta 2
  calc
    delta ^ 2 * (4 * quarterDenominator) =
        (2 * delta) ^ 2 * quarterDenominator := by ring
    _ ≤ candidate ^ 2 * variance := Nat.mul_le_mul hsq hvariance

/-- Zero numerator, including the reversal-degenerate pairs, is immediate. -/
theorem zero_difference_branch (candidate variance denominator : ℕ) :
    0 ^ 2 * denominator ≤ candidate ^ 2 * variance := by simp

/-- The square of the signed integer difference is the square of natural distance. -/
theorem selfOverlapDelta_sq_eq_dist_sq {n : ℕ} (A B : Word n) :
    selfOverlapDelta A B ^ 2 =
      ((Nat.dist (overlapNum A A) (overlapNum B B) : ℕ) : ℤ) ^ 2 := by
  unfold selfOverlapDelta
  by_cases hle : overlapNum A A ≤ overlapNum B B
  · rw [Nat.dist_eq_sub_of_le hle, Nat.cast_sub hle]
    ring
  · have hge : overlapNum B B ≤ overlapNum A A := Nat.le_of_lt (Nat.lt_of_not_ge hle)
    rw [Nat.dist_eq_sub_of_le_right hge, Nat.cast_sub hge]

/-- The integer candidate is the cast of the natural geometric numerator. -/
theorem candidateNum_eq_natCast {n : ℕ} (hn : 1 ≤ n) :
    candidateNum n = (((2 ^ n - 2 : ℕ) : ℤ)) := by
  unfold candidateNum
  have hpow : 2 ≤ 2 ^ n := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    simp [pow_succ]
  rw [Nat.cast_sub hpow]
  norm_num

/-- For `n ≥ 2`, split the power-of-two denominator into the quarter-variance scale. -/
theorem pow_two_eq_four_mul_quarter {n : ℕ} (hn : 2 ≤ n) :
    2 ^ n = 4 * 2 ^ (n - 2) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [show m + 2 = m + 2 by rfl, pow_add]
  norm_num

/-- Once the Walsh lemma supplies the exact variance branch, the Formal
Conjectures inequality follows with no additional word combinatorics. -/
theorem most_unfair_litt_bound_of_variance_cases {n : ℕ} (hn : 2 ≤ n)
    (A B : Word n) (q : ℕ)
    (hvariance : varianceNum A B = (q : ℤ))
    (hcase :
      Nat.dist (overlapNum A A) (overlapNum B B) = 0 ∨
      ((IsConstant A ∨ IsConstant B) ∧ 2 ^ n ≤ q) ∨
      ((¬ IsConstant A ∧ ¬ IsConstant B) ∧ 2 ^ (n - 2) ≤ q)) :
    selfOverlapDelta A B ^ 2 * ((2 ^ n : ℕ) : ℤ) ≤
      candidateNum n ^ 2 * varianceNum A B := by
  let delta := Nat.dist (overlapNum A A) (overlapNum B B)
  let candidate := 2 ^ n - 2
  have hnat : delta ^ 2 * 2 ^ n ≤ candidate ^ 2 * q := by
    rcases hcase with hzero | hconstant | hnonconstant
    · have hzero' : delta = 0 := hzero
      subst delta
      simp
    · exact constant_branch_arithmetic candidate delta q (2 ^ n)
        (selfOverlap_dist_le_candidate A B) hconstant.2
    · rw [pow_two_eq_four_mul_quarter hn]
      exact nonconstant_branch_arithmetic candidate delta q (2 ^ (n - 2))
        (two_mul_selfOverlap_dist_le_candidate hn A B hnonconstant.1.1 hnonconstant.1.2)
        hnonconstant.2
  rw [selfOverlapDelta_sq_eq_dist_sq, hvariance,
    candidateNum_eq_natCast (Nat.le_trans (by omega : 1 ≤ 2) hn)]
  exact_mod_cast hnat

#print axioms overlapNum_le_candidate
#print axioms selfOverlapNum_le_nonconstant
#print axioms two_mul_selfOverlap_dist_le_candidate
#print axioms constant_branch_arithmetic
#print axioms nonconstant_branch_arithmetic
#print axioms most_unfair_litt_bound_of_variance_cases

end LittMostUnfairBet
