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
module

public import FormalConjectures.Util.ProblemImports

@[expose] public section

/-!
# OEIS A343881 / Peter Kagey's Problem 16

For integers `n` and `k`, let `T(n, k)` be the least integer `m > k` for which
there are positive integers `c`, `x`, and `y`, with `x, y < n`, such that

`k ^ x * m ^ y = c ^ n`.

The OEIS entry conjectures that, for each fixed `k > 1`, one eventually has
`T(p, k) = k * rad(k)` as `p` ranges over sufficiently large primes.

This is false for `k = 12`: the proposed value is `72`, but the exponent
vectors of `12` and `72` have determinant one modulo every prime, so no
allowed positive exponents can make `12 ^ x * 72 ^ y` a prime-th power.
In fact, the obstruction holds for every prime, with no asymptotic lower bound.

*Reference:* [OEIS A343881](https://oeis.org/A343881)
-/

namespace OeisA343881

open scoped BigOperators

/-- `m` is an admissible candidate for `T(n, k)`. -/
def IsCandidate (n k m : ℕ) : Prop :=
  k < m ∧ ∃ c x y : ℕ,
    0 < c ∧ 0 < x ∧ x < n ∧ 0 < y ∧ y < n ∧ k ^ x * m ^ y = c ^ n

/-- Relational formulation saying that `m` is the least admissible candidate. -/
def IsTValue (n k m : ℕ) : Prop :=
  IsLeast {r : ℕ | IsCandidate n k r} m

/-- A064549: `k` times the product of the distinct prime factors of `k`. -/
def a064549 (k : ℕ) : ℕ :=
  k * ∏ q ∈ k.primeFactors, q

lemma a064549_twelve : a064549 12 = 72 := by
  norm_num [a064549, Nat.primeFactors, Nat.primeFactorsList]

/-- The proposed value `72` is never admissible for `k = 12` at a prime exponent. -/
lemma twelve_seventy_two_not_candidate {p : ℕ} (hp : p.Prime) :
    ¬ IsCandidate p 12 72 := by
  rintro ⟨_, c, x, y, hc, hx, hxp, hy, hyp, hpow⟩
  have hfac :
      x • (12.factorization) + y • (72.factorization) = p • c.factorization := by
    calc
      x • (12.factorization) + y • (72.factorization) =
          (12 ^ x).factorization + (72 ^ y).factorization := by
            rw [Nat.factorization_pow, Nat.factorization_pow]
      _ = (12 ^ x * 72 ^ y).factorization := by
            rw [Nat.factorization_mul (pow_ne_zero x (by norm_num))
              (pow_ne_zero y (by norm_num))]
      _ = (c ^ p).factorization := congrArg Nat.factorization hpow
      _ = p • c.factorization := Nat.factorization_pow c p
  have h12two : 12.factorization 2 = 2 := by decide
  have h12three : 12.factorization 3 = 1 := by decide
  have h72two : 72.factorization 2 = 3 := by decide
  have h72three : 72.factorization 3 = 2 := by decide
  have htwo := congrArg (fun f : ℕ →₀ ℕ => f 2) hfac
  have hthree := congrArg (fun f : ℕ →₀ ℕ => f 3) hfac
  simp [h12two, h12three, h72two, h72three, nsmul_eq_mul] at htwo hthree
  have htwoZ := congrArg (fun z : ℕ => (z : ZMod p)) htwo
  have hthreeZ := congrArg (fun z : ℕ => (z : ZMod p)) hthree
  push_cast at htwoZ hthreeZ
  simp at htwoZ hthreeZ
  have hyZ : (y : ZMod p) = 0 := by
    linear_combination 2 * hthreeZ - htwoZ
  have hpy : p ∣ y := (CharP.cast_eq_zero_iff (ZMod p) p y).mp hyZ
  exact (Nat.not_dvd_of_pos_of_lt hy hyp) hpy

/--
The eventual-value conjecture in OEIS A343881 is false. The fixed value
`k = 12` is a counterexample for every prime exponent.
-/
@[category research solved, AMS 11]
theorem conjecture : answer(False) ↔
    ∀ k : ℕ, 1 < k → ∃ N : ℕ, ∀ p : ℕ, N ≤ p → p.Prime →
      IsTValue p k (a064549 k) := by
  constructor
  · simp
  · intro h
    obtain ⟨N, hN⟩ := h 12 (by norm_num)
    obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes N
    have hleast := hN p hpN hp
    have hcandidate : IsCandidate p 12 72 := by
      rw [← a064549_twelve]
      exact hleast.1
    exact twelve_seventy_two_not_candidate hp hcandidate

#print axioms OeisA343881.conjecture

end OeisA343881
