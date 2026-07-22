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

import FormalConjectures.Other.LittMostUnfairBetWalshAssembly
import FormalConjectures.Other.LittMostUnfairBetWalshTwoEndpointComplete

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

set_option autoImplicit false

namespace LittMostUnfairBet

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
  by_cases hn3 : 3 ≤ n
  · apply LittMostUnfairBetWalsh.most_unfair_litt_bound_of_two_endpoint_gap
      hn3 A B hne
    intro hagree hleft hright
    rcases
        LittMostUnfairBetWalsh.rawEnergy_gap_or_delta_zero_of_two_endpoint_disagreement
          hn3 A B hagree hleft hright with hzero | hgap
    · left
      have hcast : (overlapNum A A : ℤ) = (overlapNum B B : ℤ) := by
        unfold selfOverlapDelta at hzero
        omega
      have heq : overlapNum A A = overlapNum B B := by
        exact_mod_cast hcast
      simp [heq]
    · right
      simpa [show n - 1 = (n - 2) + 1 by omega, pow_succ, mul_comm] using hgap
  · have hn2 : n = 2 := by omega
    subst n
    revert A B
    decide

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

#print axioms most_unfair_litt_coin_word_bet
#print axioms endpoint_flip_pair_attains

end LittMostUnfairBet
