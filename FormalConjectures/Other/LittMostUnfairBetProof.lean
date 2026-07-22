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

import FormalConjectures.Other.LittMostUnfairBet

/-!
# Proof development for the most unfair Litt coin-word bet

This file discharges the exact endpoint-flip equality case and records the
arithmetic reduction used by the global proof. The remaining global theorem
is reduced to the word-level constant-case and variance-gap lemmas proved in
the accompanying certificate.
-/

set_option autoImplicit false

open Finset

namespace LittMostUnfairBet

/-- The sum of all possible proper-overlap weights. -/
def properWeightSum (n : ℕ) : ℕ :=
  ∑ k : Fin n, if k.val + 1 < n then 2 ^ (k.val + 1) else 0

/-- The proper-overlap weights form the geometric sum `2^n - 2`. -/
theorem properWeightSum_succ (m : ℕ) :
    properWeightSum (m + 1) = 2 ^ (m + 1) - 2 := by
  unfold properWeightSum
  rw [Fin.sum_univ_castSucc]
  have hproper (i : Fin m) : i.val + 1 < m + 1 := by omega
  simp only [Fin.val_castSucc, hproper, if_true, Fin.val_last, lt_self_iff_false,
    if_false, add_zero]
  rw [← Finset.sum_range]
  have hgeom : (∑ i ∈ Finset.range m, 2 ^ i) = 2 ^ m - 1 := by
    simpa using geom_sum_mul_of_one_le (x := (2 : ℕ)) (by omega) m
  calc
    (∑ i ∈ Finset.range m, 2 ^ (i + 1)) =
        (∑ i ∈ Finset.range m, 2 ^ i) * 2 := by
      simp_rw [pow_succ]
      rw [Finset.sum_mul]
    _ = (2 ^ m - 1) * 2 := by rw [hgeom]
    _ = 2 ^ (m + 1) - 2 := by
      rw [pow_succ]
      omega

@[simp]
theorem constantWord_apply (n : ℕ) (b : Bool) (i : Fin n) :
    constantWord n b i = b := rfl

@[simp]
theorem endpointFlipWord_last (m : ℕ) (b : Bool) :
    endpointFlipWord m b (Fin.last m) = !b := by
  simp [endpointFlipWord]

theorem endpointFlipWord_eq_of_lt_last (m : ℕ) (b : Bool) (i : Fin (m + 1))
    (hi : i.val < m) : endpointFlipWord m b i = b := by
  rw [endpointFlipWord, if_neg]
  intro h
  have hval := congrArg Fin.val h
  simp at hval
  omega

/-- Every proper prefix of the endpoint-flip word is constant. -/
theorem endpoint_prefix_eq_constant (m : ℕ) (b : Bool) (k : Fin (m + 1))
    (hk : k.val + 1 < m + 1) :
    wordPrefix (endpointFlipWord m b) k =
      wordPrefix (constantWord (m + 1) b) k := by
  funext i
  unfold wordPrefix
  apply endpointFlipWord_eq_of_lt_last
  omega

/-- Every suffix and prefix of a constant word agree. -/
theorem constant_suffix_eq_prefix (n : ℕ) (b : Bool) (k : Fin n) :
    wordSuffix (constantWord n b) k = wordPrefix (constantWord n b) k := by
  funext i
  rfl

/-- A constant suffix agrees with every proper prefix of the endpoint-flip word. -/
theorem constant_suffix_eq_endpoint_prefix (m : ℕ) (b : Bool) (k : Fin (m + 1))
    (hk : k.val + 1 < m + 1) :
    wordSuffix (constantWord (m + 1) b) k =
      wordPrefix (endpointFlipWord m b) k := by
  rw [endpoint_prefix_eq_constant m b k hk]
  exact constant_suffix_eq_prefix (m + 1) b k

/-- Every nonempty suffix of the endpoint-flip word ends in the flipped bit. -/
theorem endpoint_suffix_ne_constant_prefix (m : ℕ) (b : Bool) (k : Fin (m + 1)) :
    wordSuffix (endpointFlipWord m b) k ≠
      wordPrefix (constantWord (m + 1) b) k := by
  intro h
  let i : Fin (k.val + 1) := Fin.last k.val
  have hi :
      (⟨m + 1 - k.val - 1 + i.val, by omega⟩ : Fin (m + 1)) = Fin.last m := by
    apply Fin.ext
    simp [i]
    omega
  have hvalue := congrFun h i
  change endpointFlipWord m b
      ⟨m + 1 - k.val - 1 + i.val, by omega⟩ = b at hvalue
  rw [hi, endpointFlipWord_last] at hvalue
  exact Bool.not_ne_self b hvalue

/-- No proper suffix of the endpoint-flip word is one of its prefixes. -/
theorem endpoint_suffix_ne_endpoint_prefix (m : ℕ) (b : Bool) (k : Fin (m + 1))
    (hk : k.val + 1 < m + 1) :
    wordSuffix (endpointFlipWord m b) k ≠
      wordPrefix (endpointFlipWord m b) k := by
  intro h
  let i : Fin (k.val + 1) := Fin.last k.val
  have hsuffix :
      (⟨m + 1 - k.val - 1 + i.val, by omega⟩ : Fin (m + 1)) = Fin.last m := by
    apply Fin.ext
    simp [i]
    omega
  have hprefix : i.val < m := by
    simp [i]
    omega
  have hvalue := congrFun h i
  change endpointFlipWord m b
      ⟨m + 1 - k.val - 1 + i.val, by omega⟩ = endpointFlipWord m b
        ⟨i.val, by omega⟩ at hvalue
  rw [hsuffix, endpointFlipWord_last,
    endpointFlipWord_eq_of_lt_last m b ⟨i.val, by omega⟩ hprefix] at hvalue
  exact Bool.not_ne_self b hvalue

/-- A constant word has every proper self-overlap. -/
theorem overlapNum_constant (n : ℕ) (b : Bool) :
    overlapNum (constantWord n b) (constantWord n b) = properWeightSum n := by
  unfold overlapNum properWeightSum
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hproper : k.val + 1 < n
  · rw [if_pos hproper]
    rw [if_pos ⟨hproper, constant_suffix_eq_prefix n b k⟩]
  · rw [if_neg hproper]
    rw [if_neg]
    exact fun h => hproper h.1

/-- A constant word overlaps every proper prefix of the endpoint-flip word. -/
theorem overlapNum_constant_endpoint (m : ℕ) (b : Bool) :
    overlapNum (constantWord (m + 1) b) (endpointFlipWord m b) =
      properWeightSum (m + 1) := by
  unfold overlapNum properWeightSum
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hproper : k.val + 1 < m + 1
  · rw [if_pos hproper]
    rw [if_pos ⟨hproper, constant_suffix_eq_endpoint_prefix m b k hproper⟩]
  · rw [if_neg hproper]
    rw [if_neg]
    exact fun h => hproper h.1

/-- The endpoint-flip word has no overlap into a constant prefix. -/
theorem overlapNum_endpoint_constant (m : ℕ) (b : Bool) :
    overlapNum (endpointFlipWord m b) (constantWord (m + 1) b) = 0 := by
  unfold overlapNum
  apply Finset.sum_eq_zero
  intro k hk
  rw [if_neg]
  intro h
  exact endpoint_suffix_ne_constant_prefix m b k h.2

/-- The endpoint-flip word is unbordered. -/
theorem overlapNum_endpoint_self (m : ℕ) (b : Bool) :
    overlapNum (endpointFlipWord m b) (endpointFlipWord m b) = 0 := by
  unfold overlapNum
  apply Finset.sum_eq_zero
  intro k hk
  rw [if_neg]
  intro h
  exact endpoint_suffix_ne_endpoint_prefix m b k h.1 h.2

/-- The sharp endpoint-flip pair attains equality. -/
theorem endpoint_flip_pair_attains_proof (m : ℕ) (hm : 1 ≤ m) (b : Bool) :
    selfOverlapDelta (endpointFlipWord m b) (constantWord (m + 1) b) ^ 2 *
        ((2 ^ (m + 1) : ℕ) : ℤ) =
      candidateNum (m + 1) ^ 2 *
        varianceNum (endpointFlipWord m b) (constantWord (m + 1) b) := by
  rw [selfOverlapDelta, varianceNum]
  rw [overlapNum_endpoint_self, overlapNum_constant,
    overlapNum_endpoint_constant, overlapNum_constant_endpoint]
  rw [properWeightSum_succ]
  unfold candidateNum
  have hpow : 2 ≤ 2 ^ (m + 1) := by
    rw [pow_succ]
    have hpos : 0 < 2 ^ m := pow_pos (by omega) m
    omega
  push_cast [Nat.cast_sub hpow]
  ring

/-! ## Arithmetic endgame for the global theorem -/

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

/-!
The remaining proof obligation is the all-word variance gap. The accompanying
certificate proves it by a Walsh translation-shape count: an interior
disagreement gives `2^(n-3)` full-span unit squares; endpoint-only disagreement
uses the span-`n-2` family, with the sole zero-energy case a reversal pair whose
self-overlap difference is zero.
-/

end LittMostUnfairBet
