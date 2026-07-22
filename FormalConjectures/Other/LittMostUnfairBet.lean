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

/-- A constant word with its final letter flipped. -/
def endpointFlipWord (m : ℕ) (b : Bool) : Word (m + 1) :=
  fun i => if i = Fin.last m then !b else b

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
  sorry

end LittMostUnfairBet
