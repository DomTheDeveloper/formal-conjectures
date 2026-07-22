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

import FormalConjecturesUtil

/-!
# The most unfair Litt coin-word bet

For a binary word `W` of length `n`, let `N_W(m)` be the number of possibly
overlapping occurrences of `W` in `m` fair coin tosses. Ekhad and Zeilberger
asked which pair of distinct words has the largest leading asymptotic bias
between the events `N_A(m) > N_B(m)` and `N_B(m) > N_A(m)`.

Janson, Nica, and Segert express the leading coefficient using weighted
prefix-suffix overlaps. After clearing denominators and squaring, their
formula reduces the extremal problem to the integer inequality stated below.
The sharp pair is a constant word and the word obtained by flipping one
endpoint.

*References:*
- [Ekhad--Zeilberger challenge](https://sites.math.rutgers.edu/~zeilberg/mamarim/mamarimhtml/litt.html)
- Svante Janson, Mihai Nica, and Simon Segert,
  [The generalized Alice HH vs Bob HT problem](https://arxiv.org/abs/2503.19035)
-/

namespace LittMostUnfairBet

/-- A binary word of length `n`. -/
abbrev Word (n : ℕ) := Fin n → Bool

/-- The suffix of length `k + 1`. -/
def wordSuffix {n : ℕ} (w : Word n) (k : Fin n) : Fin (k + 1) → Bool :=
  fun i => w ⟨n - k - 1 + i, by omega⟩

/-- The prefix of length `k + 1`. -/
def wordPrefix {n : ℕ} (w : Word n) (k : Fin n) : Fin (k + 1) → Bool :=
  fun i => w ⟨i, by omega⟩

/--
The proper overlap polynomial evaluated at `2`: a common suffix-prefix of
length `r` contributes `2^r`. The full overlap of length `n` is excluded.
-/
def overlapNum {n : ℕ} (A B : Word n) : ℕ :=
  ∑ k : Fin n,
    if k.val + 1 < n ∧ wordSuffix A k = wordPrefix B k then
      2 ^ (k.val + 1)
    else 0

/-- The signed difference of the two proper self-overlap numerators. -/
def selfOverlapDelta {n : ℕ} (A B : Word n) : ℤ :=
  (overlapNum A A : ℤ) - overlapNum B B

/--
The numerator of
`1 + θ_AA + θ_BB - θ_AB - θ_BA`, with common denominator `2^n`.
-/
def varianceNum {n : ℕ} (A B : Word n) : ℤ :=
  ((2 ^ n : ℕ) : ℤ) + overlapNum A A + overlapNum B B -
    overlapNum A B - overlapNum B A

/-- The numerator of `1 - 2^(1-n)`, with common denominator `2^n`. -/
def candidateNum (n : ℕ) : ℤ := ((2 ^ n : ℕ) : ℤ) - 2

/-- A constant binary word. -/
def constantWord (n : ℕ) (b : Bool) : Word n := fun _ => b

/-- A constant word with its first letter flipped. -/
def endpointFlipWord (m : ℕ) (b : Bool) : Word (m + 1) :=
  fun i => if i = 0 then !b else b

/-! ## Exact evaluation of the sharp pair -/

lemma sum_pow_two_fin : ∀ n : ℕ,
    (∑ i : Fin n, 2 ^ (i.val + 1)) = 2 ^ (n + 1) - 2
  | 0 => by simp
  | n + 1 => by
      rw [Fin.sum_univ_castSucc, sum_pow_two_fin n]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [pow_succ]
      omega

lemma sum_proper_pow_two (n : ℕ) :
    (∑ k : Fin (n + 1), if k.val + 1 < n + 1 then 2 ^ (k.val + 1) else 0) =
      2 ^ (n + 1) - 2 := by
  rw [Fin.sum_univ_castSucc]
  have hproper : ∀ i : Fin n, i.val + 1 < n + 1 := by
    intro i
    omega
  simp [hproper, sum_pow_two_fin]

lemma constant_suffix_eq_prefix (n : ℕ) (b : Bool) (k : Fin n) :
    wordSuffix (constantWord n b) k = wordPrefix (constantWord n b) k := by
  funext i
  rfl

lemma endpoint_suffix_eq_constant_prefix {m : ℕ} (b : Bool) (k : Fin (m + 1))
    (hk : k.val + 1 < m + 1) :
    wordSuffix (endpointFlipWord m b) k = wordPrefix (constantWord (m + 1) b) k := by
  funext i
  have hidx :
      (⟨m + 1 - k - 1 + i, by omega⟩ : Fin (m + 1)) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero] at hv
    omega
  simp [wordSuffix, wordPrefix, endpointFlipWord, constantWord, hidx]

lemma endpoint_suffix_ne_endpoint_prefix {m : ℕ} (b : Bool) (k : Fin (m + 1))
    (hk : k.val + 1 < m + 1) :
    wordSuffix (endpointFlipWord m b) k ≠ wordPrefix (endpointFlipWord m b) k := by
  intro h
  have h0 := congrFun h (0 : Fin (k + 1))
  have hidx :
      (⟨m + 1 - k - 1, by omega⟩ : Fin (m + 1)) ≠ 0 := by
    intro heq
    have hv := congrArg Fin.val heq
    simp only [Fin.val_zero] at hv
    omega
  cases b <;> simp [wordSuffix, wordPrefix, endpointFlipWord, hidx] at h0

lemma constant_suffix_ne_endpoint_prefix {m : ℕ} (b : Bool) (k : Fin (m + 1)) :
    wordSuffix (constantWord (m + 1) b) k ≠ wordPrefix (endpointFlipWord m b) k := by
  intro h
  have h0 := congrFun h (0 : Fin (k + 1))
  cases b <;> simp [wordSuffix, wordPrefix, endpointFlipWord, constantWord] at h0

lemma overlapNum_constant (m : ℕ) (b : Bool) :
    overlapNum (constantWord (m + 1) b) (constantWord (m + 1) b) =
      2 ^ (m + 1) - 2 := by
  rw [overlapNum]
  calc
    (∑ k : Fin (m + 1),
      if k.val + 1 < m + 1 ∧
          wordSuffix (constantWord (m + 1) b) k =
            wordPrefix (constantWord (m + 1) b) k then
        2 ^ (k.val + 1)
      else 0) =
        ∑ k : Fin (m + 1), if k.val + 1 < m + 1 then 2 ^ (k.val + 1) else 0 := by
          apply Finset.sum_congr rfl
          intro k hk
          by_cases hp : k.val + 1 < m + 1
          · simp [hp, constant_suffix_eq_prefix]
          · simp [hp]
    _ = 2 ^ (m + 1) - 2 := sum_proper_pow_two m

lemma overlapNum_endpoint_self (m : ℕ) (b : Bool) :
    overlapNum (endpointFlipWord m b) (endpointFlipWord m b) = 0 := by
  rw [overlapNum]
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hp : k.val + 1 < m + 1
  · simp [hp, endpoint_suffix_ne_endpoint_prefix b k hp]
  · simp [hp]

lemma overlapNum_endpoint_constant (m : ℕ) (b : Bool) :
    overlapNum (endpointFlipWord m b) (constantWord (m + 1) b) =
      2 ^ (m + 1) - 2 := by
  rw [overlapNum]
  calc
    (∑ k : Fin (m + 1),
      if k.val + 1 < m + 1 ∧
          wordSuffix (endpointFlipWord m b) k =
            wordPrefix (constantWord (m + 1) b) k then
        2 ^ (k.val + 1)
      else 0) =
        ∑ k : Fin (m + 1), if k.val + 1 < m + 1 then 2 ^ (k.val + 1) else 0 := by
          apply Finset.sum_congr rfl
          intro k hk
          by_cases hp : k.val + 1 < m + 1
          · simp [hp, endpoint_suffix_eq_constant_prefix b k hp]
          · simp [hp]
    _ = 2 ^ (m + 1) - 2 := sum_proper_pow_two m

lemma overlapNum_constant_endpoint (m : ℕ) (b : Bool) :
    overlapNum (constantWord (m + 1) b) (endpointFlipWord m b) = 0 := by
  rw [overlapNum]
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hp : k.val + 1 < m + 1
  · simp [hp, constant_suffix_ne_endpoint_prefix b k]
  · simp [hp]

/--
The denominator-cleared square of the Ekhad--Zeilberger extremal conjecture.
Equivalently, the overlap functional

`|θ_AA - θ_BB| / sqrt (1 + θ_AA + θ_BB - θ_AB - θ_BA)`

is at most `1 - 2^(1-n)`.
-/
@[category research open, AMS 5 60]
theorem most_unfair_litt_coin_word_bet {n : ℕ} (hn : 2 ≤ n)
    (A B : Word n) (hne : A ≠ B) :
    selfOverlapDelta A B ^ 2 * ((2 ^ n : ℕ) : ℤ) ≤
      candidateNum n ^ 2 * varianceNum A B := by
  sorry

/-- The constant/end-flip pair attains the sharp bound. -/
@[category research open, AMS 5 60]
theorem endpoint_flip_pair_attains (m : ℕ) (hm : 1 ≤ m) (b : Bool) :
    selfOverlapDelta (endpointFlipWord m b) (constantWord (m + 1) b) ^ 2 *
        ((2 ^ (m + 1) : ℕ) : ℤ) =
      candidateNum (m + 1) ^ 2 *
        varianceNum (endpointFlipWord m b) (constantWord (m + 1) b) := by
  rw [selfOverlapDelta, varianceNum, candidateNum,
    overlapNum_endpoint_self, overlapNum_constant,
    overlapNum_endpoint_constant, overlapNum_constant_endpoint]
  ring

end LittMostUnfairBet
