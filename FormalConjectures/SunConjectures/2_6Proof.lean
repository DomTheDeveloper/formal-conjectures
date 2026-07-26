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

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Chebyshev
import FormalConjectures.SunConjectures.«2_6Finite»

/-!
# Proof attempt for Zhi-Wei Sun's Conjecture 2.6

This proof uses only results already in Mathlib:

* the explicit Chebyshev lower bound for `π`;
* the totient upper bound for primes in an interval, with modulus `30`;
* two exact `native_decide` checks for the finite remainder.
-/

namespace SunConjectures

open scoped Nat.Prime

private lemma log_succ_le_nine_hundredths (x : ℝ) (hx : 2401 ≤ x) :
    Real.log (x + 1) < (9 / 100 : ℝ) * x := by
  have hx0 : 0 ≤ x := by positivity
  have hy0 : 0 < x + 1 := by positivity
  have hs0 : 0 ≤ Real.sqrt (x + 1) := Real.sqrt_nonneg _
  have hspos : 0 < Real.sqrt (x + 1) := Real.sqrt_pos.2 hy0
  have hlogsqrt := Real.log_le_sub_one_of_pos hspos
  have hlog : Real.log (x + 1) ≤ 2 * Real.sqrt (x + 1) := by
    have hls := Real.log_sqrt hy0.le
    nlinarith
  have hs_le : Real.sqrt (x + 1) ≤ x / 25 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith
  calc
    Real.log (x + 1) ≤ 2 * Real.sqrt (x + 1) := hlog
    _ ≤ 2 * (x / 25) := by gcongr
    _ < (9 / 100 : ℝ) * x := by nlinarith

private lemma log_lt_three_fifths_sqrt (x : ℝ) (hx : 2401 ≤ x) :
    Real.log x < (3 / 5 : ℝ) * Real.sqrt x := by
  have hx0 : 0 ≤ x := by positivity
  let s := Real.sqrt x
  let u := Real.sqrt s
  have hs0 : 0 ≤ s := by simp [s]
  have hu0 : 0 ≤ u := by simp [u]
  have hs_sq : s ^ 2 = x := by simpa [s] using Real.sq_sqrt hx0
  have hu_sq : u ^ 2 = s := by simpa [u] using Real.sq_sqrt hs0
  have hu7 : 7 ≤ u := by
    by_contra! h
    have hs_lt : s < 49 := by nlinarith
    have hx_lt : x < 2401 := by nlinarith
    linarith
  have hupos : 0 < u := lt_of_lt_of_le (by norm_num) hu7
  have hlogu := Real.log_le_sub_one_of_pos hupos
  have hlog_s : Real.log s = Real.log x / 2 := by
    simpa [s] using Real.log_sqrt hx0
  have hlog_u : Real.log u = Real.log s / 2 := by
    simpa [u] using Real.log_sqrt hs0
  calc
    Real.log x = 4 * Real.log u := by linarith
    _ ≤ 4 * (u - 1) := by gcongr
    _ < (3 / 5 : ℝ) * (u ^ 2) := by nlinarith
    _ = (3 / 5 : ℝ) * Real.sqrt x := by simp [hu_sq, s]

private lemma primeCounting_lower (x : ℕ) (hx : 2401 ≤ x) :
    (3 / 5 : ℝ) * (x : ℝ) / Real.log x < (π x : ℝ) := by
  have hxreal : (2401 : ℝ) ≤ x := by exact_mod_cast hx
  have hx1 : (1 : ℝ) < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos hx1
  have hlogsucc := log_succ_le_nine_hundredths (x : ℝ) hxreal
  have hlogtwo : (69 / 100 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hnum : (3 / 5 : ℝ) * (x : ℝ) <
      (x : ℝ) * Real.log 2 - Real.log ((x : ℝ) + 1) := by
    nlinarith
  have hdiv : (3 / 5 : ℝ) * (x : ℝ) / Real.log x <
      ((x : ℝ) * Real.log 2 - Real.log ((x : ℝ) + 1)) / Real.log x := by
    exact (div_lt_div_iff_of_pos_right hlogpos).2 hnum
  exact hdiv.trans_le (Chebyshev.pi_ge x)

private lemma sqrt_lt_primeCounting (x : ℕ) (hx : 2401 ≤ x) :
    Real.sqrt x < (π x : ℝ) := by
  have hxreal : (2401 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) ≤ x := by positivity
  have hx1 : (1 : ℝ) < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos hx1
  have hspos : 0 < Real.sqrt x := Real.sqrt_pos.2 (by positivity)
  have hlog := log_lt_three_fifths_sqrt (x : ℝ) hxreal
  have hs_sq : (Real.sqrt x) ^ 2 = (x : ℝ) := Real.sq_sqrt hx0
  have hs_lower : Real.sqrt x < (3 / 5 : ℝ) * (x : ℝ) / Real.log x := by
    rw [lt_div_iff₀ hlogpos]
    nlinarith
  exact hs_lower.trans (primeCounting_lower x hx)

private lemma analytic_case (n k : ℕ) (hn : 120 ≤ n) (hk : 1 ≤ k)
    (hx : 2401 ≤ k * n) :
    (π (k * n)) ^ (k + 1) > (π ((k + 1) * n)) ^ k := by
  let x := k * n
  let A := π x
  let B := π (x + n)
  let q := 8 * (n / 30 + 1)
  have hx30 : 30 ≤ x := by simp [x]; omega
  have hB : B ≤ A + q := by
    simpa [A, B, q, x, Nat.totient] using
      (Nat.primeCounting_add_le (a := 30) (k := x) (by norm_num) hx30 n)
  have hq : 10 * q ≤ 3 * n := by
    simp [q]
    omega
  have hAlower := primeCounting_lower x (by simpa [x] using hx)
  have hAsqrt := sqrt_lt_primeCounting x (by simpa [x] using hx)
  have hxreal0 : (0 : ℝ) ≤ x := by positivity
  have hxreal1 : (1 : ℝ) < x := by
    exact lt_of_lt_of_le (by norm_num) (by exact_mod_cast hx)
  have hlogxpos : 0 < Real.log x := Real.log_pos hxreal1
  have hApos : 0 < (A : ℝ) := lt_of_le_of_lt (Real.sqrt_nonneg _) hAsqrt
  have hBpos : 0 < (B : ℝ) := by
    have hAB : A ≤ B := by
      dsimp [A, B]
      exact Nat.monotone_primeCounting (Nat.le_add_right x n)
    exact lt_of_lt_of_le hApos (by exact_mod_cast hAB)
  have hlogA : (1 / 2 : ℝ) * Real.log x < Real.log A := by
    have hslog : Real.log (Real.sqrt x) < Real.log A :=
      Real.log_lt_log (Real.sqrt_pos.2 (by positivity)) hAsqrt
    rw [Real.log_sqrt hxreal0] at hslog
    linarith
  have hqreal : (10 : ℝ) * q ≤ 3 * n := by exact_mod_cast hq
  have hkq : (k : ℝ) * q / A < (1 / 2 : ℝ) * Real.log x := by
    have hxkn : (x : ℝ) = k * n := by simp [x]
    have hAlower' : (3 / 5 : ℝ) * (x : ℝ) < (A : ℝ) * Real.log x := by
      rw [div_lt_iff₀ hlogxpos] at hAlower
      exact hAlower
    rw [div_lt_iff₀ hApos]
    nlinarith
  have hratio : Real.log ((B : ℝ) / A) ≤ (q : ℝ) / A := by
    have hratio_pos : 0 < (B : ℝ) / A := div_pos hBpos hApos
    have hone_pos : 0 < (1 : ℝ) + q / A := by positivity
    have hratio_le : (B : ℝ) / A ≤ 1 + q / A := by
      rw [div_le_iff₀ hApos]
      have hBreal : (B : ℝ) ≤ A + q := by exact_mod_cast hB
      linarith
    calc
      Real.log ((B : ℝ) / A) ≤ Real.log (1 + q / A) :=
        Real.strictMonoOn_log.monotoneOn hratio_pos hone_pos hratio_le
      _ ≤ (1 + q / A) - 1 := Real.log_le_sub_one_of_pos hone_pos
      _ = (q : ℝ) / A := by ring
  have hmainlog : (k : ℝ) * Real.log B < ((k : ℝ) + 1) * Real.log A := by
    have hinc : (k : ℝ) * Real.log ((B : ℝ) / A) < Real.log A := by
      calc
        (k : ℝ) * Real.log ((B : ℝ) / A) ≤ (k : ℝ) * ((q : ℝ) / A) := by
          gcongr
        _ = (k : ℝ) * q / A := by ring
        _ < (1 / 2 : ℝ) * Real.log x := hkq
        _ < Real.log A := hlogA
    rw [Real.log_div (ne_of_gt hBpos) (ne_of_gt hApos)] at hinc
    linarith
  have hlogpow : Real.log ((B : ℝ) ^ k) < Real.log ((A : ℝ) ^ (k + 1)) := by
    simpa [Real.log_pow, Nat.cast_add, Nat.cast_one] using hmainlog
  have hreal : (B : ℝ) ^ k < (A : ℝ) ^ (k + 1) :=
    (Real.log_lt_log_iff (pow_pos hBpos _) (pow_pos hApos _)).mp hlogpow
  have hnat : B ^ k < A ^ (k + 1) := by exact_mod_cast hreal
  simpa [A, B, x, Nat.add_mul, Nat.one_mul, add_comm, add_left_comm, add_assoc] using hnat

/-- Zhi-Wei Sun's Conjecture 2.6. -/
theorem conjecture_2_6_proved (n k : ℕ) (hn : 4 < n) (hk_pos : 1 ≤ k) (hk_le : k ≤ n) :
    (π (k * n)) ^ (k + 1) > (π ((k + 1) * n)) ^ k := by
  by_cases hnsmall : n < 120
  · exact conjecture_2_6_finite_small_n ⟨n, hnsmall⟩ ⟨k, hk_le.trans_lt hnsmall⟩
      hn hk_pos hk_le
  · have hnlarge : 120 ≤ n := by omega
    by_cases hxsmall : k * n < 2401
    · have hn2401 : n < 2401 := by
        have : n ≤ k * n := by nlinarith
        omega
      have hk21 : k < 21 := by nlinarith
      exact conjecture_2_6_finite_small_x ⟨n, hn2401⟩ ⟨k, hk21⟩
        hnlarge hk_pos hk_le hxsmall
    · exact analytic_case n k hnlarge hk_pos (by omega)

#print axioms conjecture_2_6_proved

end SunConjectures
