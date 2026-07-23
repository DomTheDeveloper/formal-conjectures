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

import FormalConjectures.Arxiv.«2508.10245».Geode5Proof.MomentToReduced
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Elementary absolute bound for the five-dimensional Geode

The enlarged CRT certificate permits a deliberately simple bound.  Every one
of the `(n+1)^4` reduced summands is bounded uniformly using

* `choose N k ≤ 2^N`, and
* `r!/(n+r+1)! ≤ 1/(n+1)!`.

For `n=1000`, the resulting rational bound is below `2^35618`.
-/

namespace Arxiv.«2508.10245».Geode5Proof

open scoped BigOperators

/-- Uniform rational bound for one reduced summand. -/
def simpleTermBound (n : ℕ) : ℚ :=
  qFactorial (5 * n) / qFactorial n ^ 4 *
    ((1 / qFactorial (n + 1)) * (2 : ℚ) ^ (24 * n + 2))

/-- Uniform rational bound for the complete four-dimensional sum. -/
def simpleAbsoluteBound (n : ℕ) : ℚ :=
  (n + 1 : ℚ) ^ 4 * simpleTermBound n

@[positivity]
theorem qFactorial_pos (n : ℕ) : 0 < qFactorial n := by
  simp [qFactorial]

/-- A rational binomial quotient is nonnegative. -/
theorem qBinomial_nonneg (n k : ℕ) : 0 ≤ qBinomial n k := by
  simp [qBinomial, qFactorial]
  positivity

/-- A valid rational binomial quotient is bounded by the row sum `2^n`. -/
theorem qBinomial_le_two_pow (n k : ℕ) (hk : k ≤ n) :
    qBinomial n k ≤ (2 : ℚ) ^ n := by
  rw [qBinomial_eq_choose hk]
  exact_mod_cast Nat.choose_le_two_pow n k

/-- The beta factorial ratio is at most its value at `r=0`. -/
theorem qFactorial_ratio_le (n r : ℕ) :
    qFactorial r / qFactorial (n + r + 1) ≤
      1 / qFactorial (n + 1) := by
  rw [div_le_div_iff₀ (qFactorial_pos (n + r + 1))
    (qFactorial_pos (n + 1))]
  have hd :
      Nat.factorial r * Nat.factorial (n + 1) ∣
        Nat.factorial (r + (n + 1)) :=
    Nat.factorial_mul_factorial_dvd_factorial_add r (n + 1)
  have hle :
      Nat.factorial r * Nat.factorial (n + 1) ≤
        Nat.factorial (r + (n + 1)) :=
    Nat.le_of_dvd (Nat.factorial_pos _) hd
  norm_num [qFactorial]
  exact_mod_cast (by simpa [add_assoc, add_comm, add_left_comm] using hle)

/-- Every reduced summand is bounded by the same elementary quantity. -/
theorem abs_qReducedSummand_le_simpleTermBound
    (n a b c d : ℕ)
    (ha : a ≤ n) (hb : b ≤ n) (hc : c ≤ n) (hd : d ≤ n) :
    |qReducedSummand n a b c d| ≤ simpleTermBound n := by
  let r := a + b + c + d
  let q := a + 2 * b + 3 * c + 4 * d
  have hq : q ≤ 10 * n := by
    dsimp [q]
    omega
  have htop : 5 * n ≤ 20 * n + 2 - q := by omega
  have htop_le : 20 * n + 2 - q ≤ 20 * n + 2 := Nat.sub_le _ _
  have hqa := qBinomial_le_two_pow n a ha
  have hqb := qBinomial_le_two_pow n b hb
  have hqc := qBinomial_le_two_pow n c hc
  have hqd := qBinomial_le_two_pow n d hd
  have hqt₀ := qBinomial_le_two_pow (20 * n + 2 - q) (5 * n) htop
  have hqt :
      qBinomial (20 * n + 2 - q) (5 * n) ≤
        (2 : ℚ) ^ (20 * n + 2) := by
    calc
      qBinomial (20 * n + 2 - q) (5 * n) ≤
          (2 : ℚ) ^ (20 * n + 2 - q) := hqt₀
      _ ≤ (2 : ℚ) ^ (20 * n + 2) := by gcongr
  have hratio := qFactorial_ratio_le n r
  have hpref :
      0 ≤ qFactorial (5 * n) / qFactorial n ^ 4 := by positivity
  have hratio_nonneg :
      0 ≤ qFactorial r / qFactorial (n + r + 1) := by positivity
  have hqa0 := qBinomial_nonneg n a
  have hqb0 := qBinomial_nonneg n b
  have hqc0 := qBinomial_nonneg n c
  have hqd0 := qBinomial_nonneg n d
  have hqt0 := qBinomial_nonneg (20 * n + 2 - q) (5 * n)
  simp only [qReducedSummand, r, q, abs_mul, abs_div, abs_pow,
    abs_neg, abs_one, one_pow]
  rw [abs_of_nonneg hpref, abs_of_nonneg (by positivity : 0 ≤ qFactorial r),
    abs_of_nonneg (by positivity : 0 ≤ qFactorial (n + r + 1)),
    abs_of_nonneg hqa0, abs_of_nonneg hqb0, abs_of_nonneg hqc0,
    abs_of_nonneg hqd0, abs_of_nonneg hqt0]
  unfold simpleTermBound
  calc
    qFactorial (5 * n) / qFactorial n ^ 4 *
        (1 * (qFactorial r / qFactorial (n + r + 1)) *
          qBinomial n a * qBinomial n b * qBinomial n c *
          qBinomial n d * qBinomial (20 * n + 2 - q) (5 * n)) ≤
      qFactorial (5 * n) / qFactorial n ^ 4 *
        ((1 / qFactorial (n + 1)) *
          (2 : ℚ) ^ n * (2 : ℚ) ^ n * (2 : ℚ) ^ n *
          (2 : ℚ) ^ n * (2 : ℚ) ^ (20 * n + 2)) := by
      gcongr
    _ = qFactorial (5 * n) / qFactorial n ^ 4 *
        ((1 / qFactorial (n + 1)) * (2 : ℚ) ^ (24 * n + 2)) := by
      ring

/-- Triangle inequality for the complete reduced sum. -/
theorem abs_qReducedGeode_le_simpleAbsoluteBound (n : ℕ) :
    |qReducedGeode n| ≤ simpleAbsoluteBound n := by
  unfold qReducedGeode
  calc
    |∑ a ∈ Finset.range (n + 1),
        ∑ b ∈ Finset.range (n + 1),
          ∑ c ∈ Finset.range (n + 1),
            ∑ d ∈ Finset.range (n + 1), qReducedSummand n a b c d| ≤
      ∑ a ∈ Finset.range (n + 1),
        ∑ b ∈ Finset.range (n + 1),
          ∑ c ∈ Finset.range (n + 1),
            ∑ d ∈ Finset.range (n + 1), |qReducedSummand n a b c d| := by
      repeatedly' apply Finset.abs_sum_le_sum_abs
    _ ≤ ∑ _a ∈ Finset.range (n + 1),
        ∑ _b ∈ Finset.range (n + 1),
          ∑ _c ∈ Finset.range (n + 1),
            ∑ _d ∈ Finset.range (n + 1), simpleTermBound n := by
      gcongr
      exact abs_qReducedSummand_le_simpleTermBound n _ _ _ _
        (by omega) (by omega) (by omega) (by omega)
    _ = simpleAbsoluteBound n := by
      simp [simpleAbsoluteBound]
      ring

/-- The elementary numerical bound at the challenge value. -/
set_option maxHeartbeats 0 in
theorem simpleAbsoluteBound_1000_lt :
    simpleAbsoluteBound 1000 < (2 : ℚ) ^ 35618 := by
  native_decide

/-- Absolute bound for the original integer benchmark definition. -/
theorem geode5_1000_natAbs_lt_two_pow :
    (geode5Diagonal 1000).natAbs < 2 ^ 35618 := by
  have hcast := cast_geode5Diagonal_eq_qReducedGeode 1000
  have hbound := abs_qReducedGeode_le_simpleAbsoluteBound 1000
  have hfinal : |(geode5Diagonal 1000 : ℚ)| < (2 : ℚ) ^ 35618 := by
    rw [hcast]
    exact hbound.trans_lt simpleAbsoluteBound_1000_lt
  exact_mod_cast hfinal

#print axioms geode5_1000_natAbs_lt_two_pow

end Arxiv.«2508.10245».Geode5Proof
