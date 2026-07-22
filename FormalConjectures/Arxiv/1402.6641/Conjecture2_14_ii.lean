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
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.NumberTheory.Chebyshev

/-!
# Zhi-Wei Sun's Conjecture 2.14(ii)

Zhi-Wei Sun conjectured that the sequence
`Nat.primeCounting (n ^ 2) ^ (1 / n)` is strictly decreasing for `n ≥ 3`.
We use the exactly equivalent integer-power formulation, which avoids any
choice of real roots.

*Reference:*
- [Problems on combinatorial properties of primes](https://arxiv.org/abs/1402.6641),
  Zhi-Wei Sun, Conjecture 2.14(ii).
-/

namespace SunConjecture214II

open Finset Nat Real
open scoped Nat.Prime

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! ## An elementary lower bound for the prime-counting function -/

private def lcmUpto (n : ℕ) : ℕ := (Icc 1 n).lcm id

private theorem lcmUpto_ne_zero (n : ℕ) : lcmUpto n ≠ 0 := by
  simp [lcmUpto]

private theorem lcmUpto_pos (n : ℕ) : 0 < lcmUpto n :=
  pos_of_ne_zero (lcmUpto_ne_zero n)

private theorem factorization_lcmUpto (n : ℕ) {p : ℕ} (hp : p.Prime) :
    (lcmUpto n).factorization p = p.log n := by
  rw [lcmUpto, Finset.factorization_lcm (fun _ _ ↦ by grind)]
  have hp1 := hp.one_lt
  refine le_antisymm ?_ ?_
  · simp only [Finset.sup_le_iff, mem_Icc, and_imp]
    exact fun m _ hm ↦ le_log_of_pow_le hp1 (le_of_dvd (by grind) (ordProj_dvd m p) |>.trans hm)
  · rcases le_or_gt p n with hpn | hnp
    · have hpow := pow_log_le_self p (by omega : n ≠ 0)
      grw [← le_sup (b := p ^ p.log n) (by grind)]
      simpa [hp] using hpow
    · simp [log_of_lt hnp]

private theorem primeFactors_lcmUpto (n : ℕ) :
    (lcmUpto n).primeFactors = primesLE n := by
  ext p
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hp := prime_of_mem_primeFactors h
    rw [← support_factorization, Finsupp.mem_support_iff,
      factorization_lcmUpto n hp] at h
    simp_all [mem_primesLE]
  · refine Prime.mem_primeFactors (prime_of_mem_primesLE h) (dvd_lcm ?_) (lcmUpto_ne_zero n)
    exact mem_Icc.mpr ⟨(prime_of_mem_primesLE h).one_le, le_of_mem_primesLE h⟩

private theorem lcmUpto_eq_prod (n : ℕ) :
    lcmUpto n = ∏ p ∈ primesLE n, p ^ ((lcmUpto n).factorization p) := by
  conv_lhs => rw [← prod_factorization_pow_eq_self (lcmUpto_ne_zero n)]
  rw [prod_factorization_eq_prod_primeFactors, primeFactors_lcmUpto]

private theorem lcmUpto_eq_prod_pow_log (n : ℕ) :
    lcmUpto n = ∏ p ∈ primesLE n, p ^ p.log n := by
  rw [lcmUpto_eq_prod]
  apply prod_congr rfl
  intro p hp
  rw [factorization_lcmUpto n (prime_of_mem_primesLE hp)]

private theorem choose_dvd_lcmUpto {n k : ℕ} (hkn : k ≤ n) :
    choose n k ∣ lcmUpto n := by
  rw [← factorization_prime_le_iff_dvd (choose_ne_zero hkn) (lcmUpto_ne_zero n)]
  intro p hp
  rw [factorization_lcmUpto n hp]
  exact factorization_choose_le_log

private theorem two_pow_le_mul_lcmUpto (n : ℕ) :
    2 ^ n ≤ (n + 1) * lcmUpto n := calc
  _ = ∑ m ∈ range (n + 1), n.choose m := (sum_range_choose _).symm
  _ ≤ ∑ _k ∈ range (n + 1), lcmUpto n := by
    gcongr with k hk
    exact le_of_dvd (lcmUpto_pos n) (choose_dvd_lcmUpto (by grind))
  _ = _ := by simp

private theorem lcmUpto_le_pow_primeCounting {n : ℕ} (hn : n ≠ 0) :
    lcmUpto n ≤ n ^ π n := by
  calc
    lcmUpto n = ∏ p ∈ primesLE n, p ^ p.log n := lcmUpto_eq_prod_pow_log n
    _ ≤ ∏ _p ∈ primesLE n, n := by
      gcongr with p hp
      exact pow_log_le_self p hn
    _ = n ^ π n := by simp [primesLE_card_eq_primeCounting]

private theorem primeCounting_ge (n : ℕ) (hn : 1 < n) :
    ((n : ℝ) * log 2 - log (n + 1)) / log n ≤ (π n : ℝ) := by
  have hnat : 2 ^ n ≤ (n + 1) * n ^ π n :=
    (two_pow_le_mul_lcmUpto n).trans (Nat.mul_le_mul_left _ (lcmUpto_le_pow_primeCounting hn.ne))
  have hreal : (2 : ℝ) ^ n ≤ (n + 1 : ℕ) * (n : ℝ) ^ π n := by
    exact_mod_cast hnat
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ n) hreal
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow] at hlog
  rw [div_le_iff₀ (Real.log_pos (by exact_mod_cast hn))]
  norm_num at hlog ⊢
  linarith

/-! ## A sharp finite wheel-sieve bound for intervals -/

private def wheelWeight (n : ℕ) : ℤ :=
  35 * (if Nat.Coprime 210 n then 1 else 0) - 8

private def wheelPotential (r : ℕ) : ℤ :=
  ∑ i in range r, wheelWeight i

private def wheelIntervalWeight (k len : ℕ) : ℤ :=
  ∑ i in Ico k (k + len), wheelWeight i

private def wheelCount (k len : ℕ) : ℕ :=
  #{i ∈ Ico k (k + len) | Nat.Coprime 210 i}

private theorem wheelPotential_bounds :
    ∀ r : Fin 210, (-53 : ℤ) ≤ wheelPotential r ∧ wheelPotential r ≤ 45 := by
  decide

private theorem wheelPotential_step :
    ∀ r : Fin 210,
      wheelPotential ((r.val + 1) % 210) - wheelPotential r.val = wheelWeight r.val := by
  decide

private theorem wheelWeight_mod (m : ℕ) : wheelWeight (m % 210) = wheelWeight m := by
  unfold wheelWeight
  rw [(Nat.periodic_coprime 210).map_mod_nat m]

private theorem wheelPotential_step_mod (m : ℕ) :
    wheelPotential ((m + 1) % 210) - wheelPotential (m % 210) = wheelWeight m := by
  have h := wheelPotential_step ⟨m % 210, mod_lt _ (by norm_num)⟩
  simpa [Nat.add_mod, wheelWeight_mod] using h

private theorem wheelIntervalWeight_succ (k len : ℕ) :
    wheelIntervalWeight k (len + 1) =
      wheelIntervalWeight k len + wheelWeight (k + len) := by
  unfold wheelIntervalWeight
  rw [show k + (len + 1) = (k + len).succ by omega,
    Nat.Ico_succ_right_eq_insert_Ico (by omega)]
  simp

private theorem wheelIntervalWeight_eq_potential (k len : ℕ) :
    wheelIntervalWeight k len =
      wheelPotential ((k + len) % 210) - wheelPotential (k % 210) := by
  induction len with
  | zero => simp [wheelIntervalWeight]
  | succ len ih =>
      rw [wheelIntervalWeight_succ, ih]
      have hs := wheelPotential_step_mod (k + len)
      rw [show k + (len + 1) = k + len + 1 by omega]
      linarith

private theorem wheelIntervalWeight_le (k len : ℕ) :
    wheelIntervalWeight k len ≤ 98 := by
  rw [wheelIntervalWeight_eq_potential]
  have h₁ := wheelPotential_bounds ⟨(k + len) % 210, mod_lt _ (by norm_num)⟩
  have h₂ := wheelPotential_bounds ⟨k % 210, mod_lt _ (by norm_num)⟩
  omega

private theorem wheelIntervalWeight_eq_count (k len : ℕ) :
    wheelIntervalWeight k len = 35 * (wheelCount k len : ℤ) - 8 * len := by
  classical
  unfold wheelIntervalWeight wheelCount wheelWeight
  rw [sum_sub_distrib]
  simp_rw [sum_mul]
  simp only [sum_const, card_Ico, Nat.add_sub_cancel_left, nsmul_eq_mul]
  simp [mul_comm, mul_left_comm, mul_assoc]

private theorem wheelCount_bound (k len : ℕ) :
    35 * wheelCount k len ≤ 8 * len + 98 := by
  have h := wheelIntervalWeight_le k len
  rw [wheelIntervalWeight_eq_count] at h
  exact_mod_cast h

private theorem primeCounting'_add_le_wheel {k : ℕ} (hk : 210 < k) (len : ℕ) :
    π' (k + len) ≤ π' k + wheelCount k len := by
  calc
    π' (k + len) ≤ #{p ∈ range k | p.Prime} + #{p ∈ Ico k (k + len) | p.Prime} := by
      rw [primeCounting', count_eq_card_filter_range, range_eq_Ico,
        ← Ico_union_Ico_eq_Ico (zero_le k) le_self_add, filter_union]
      exact card_union_le
    _ ≤ π' k + wheelCount k len := by
      rw [primeCounting', count_eq_card_filter_range]
      gcongr with p hp
      rw [coprime_comm]
      exact coprime_of_lt_prime (by norm_num) (hk.trans_le (mem_Ico.1 hp).1)

private theorem primeCounting_square_succ_le (n : ℕ) (hn : 15 ≤ n) :
    π ((n + 1) ^ 2) ≤ π (n ^ 2) + wheelCount (n ^ 2 + 1) (2 * n + 1) := by
  change π' (((n + 1) ^ 2) + 1) ≤
    π' (n ^ 2 + 1) + wheelCount (n ^ 2 + 1) (2 * n + 1)
  convert primeCounting'_add_le_wheel (k := n ^ 2 + 1) (by nlinarith) (2 * n + 1) using 1 <;>
    ring

private theorem square_wheelCount_bound (n : ℕ) :
    35 * wheelCount (n ^ 2 + 1) (2 * n + 1) ≤ 16 * n + 106 := by
  have h := wheelCount_bound (n ^ 2 + 1) (2 * n + 1)
  omega

/-! ## Real inequalities for the tail -/

private theorem log_three_lt_eight_fifths_log_two :
    log 3 < (8 / 5 : ℝ) * log 2 := by
  have h : (3 : ℝ) ^ 5 < (2 : ℝ) ^ 8 := by norm_num
  have hl := Real.strictMonoOn_log h (by positivity) (by positivity)
  rw [Real.log_pow, Real.log_pow] at hl
  norm_num at hl ⊢
  linarith

private theorem log_seven_log_two_lt_sixteen_sevenths_log_two :
    log (7 * log 2) < (16 / 7 : ℝ) * log 2 := by
  have hlog2 : log 2 < (25 / 36 : ℝ) :=
    (Real.log_two_lt_d9.trans (by norm_num))
  have hbase : 7 * log 2 < (175 / 36 : ℝ) := by linarith
  have hp : (7 * log 2) ^ 7 < (2 : ℝ) ^ 16 := by
    calc
      (7 * log 2) ^ 7 < (175 / 36 : ℝ) ^ 7 := by gcongr
      _ < (2 : ℝ) ^ 16 := by norm_num
  have hl := Real.strictMonoOn_log hp (by positivity) (by positivity)
  rw [Real.log_pow, Real.log_pow] at hl
  norm_num at hl ⊢
  linarith

private theorem log_margin_base :
    log 3 + log (log (128 : ℝ)) < (5 / 9 : ℝ) * log 128 := by
  rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
  norm_num
  have h3 := log_three_lt_eight_fifths_log_two
  have h7 := log_seven_log_two_lt_sixteen_sevenths_log_two
  have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  nlinarith

private theorem log_margin_mono {x y : ℝ} (hx : 128 ≤ x) (hxy : x ≤ y) :
    (5 / 9 : ℝ) * log x - log (log x) ≤
      (5 / 9 : ℝ) * log y - log (log y) := by
  have hx1 : 1 < x := by linarith
  have hy1 : 1 < y := hx1.trans_le hxy
  have hlogxy : log x ≤ log y := Real.strictMonoOn_log.monotoneOn (by positivity) (by positivity) hxy
  have hlogxpos : 0 < log x := Real.log_pos hx1
  have hlogypos : 0 < log y := Real.log_pos hy1
  have hratio : 0 < log y / log x := div_pos hlogypos hlogxpos
  have hlogdiff : log (log y) - log (log x) ≤ (log y - log x) / log x := by
    rw [← Real.log_div hlogypos.ne' hlogxpos.ne']
    have h := Real.log_le_sub_one_of_pos hratio
    convert h using 1 <;> field_simp <;> ring
  have hlogx : (9 / 5 : ℝ) ≤ log x := by
    calc
      (9 / 5 : ℝ) < 7 * log 2 := by
        have := Real.log_two_gt_d9
        norm_num at this ⊢
        linarith
      _ = log 128 := by rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]; norm_num
      _ ≤ log x := Real.strictMonoOn_log.monotoneOn (by positivity) (by positivity) hx
  have hinv : 1 / log x ≤ (5 / 9 : ℝ) := by
    rw [div_le_iff₀ hlogxpos]
    nlinarith
  have hdelta : 0 ≤ log y - log x := sub_nonneg.mpr hlogxy
  have := mul_le_mul_of_nonneg_left hinv hdelta
  rw [one_div, ← div_eq_mul_inv] at this
  linarith

private theorem log_margin (n : ℕ) (hn : 128 ≤ n) :
    log 3 + log (log (n : ℝ)) < (5 / 9 : ℝ) * log n := by
  have hm := log_margin_mono (x := 128) (y := n) (by norm_num) (by exact_mod_cast hn)
  linarith [log_margin_base]

private theorem primeCounting_square_lower (n : ℕ) (hn : 128 ≤ n) :
    (n : ℝ) ^ 2 / (3 * log n) ≤ (π (n ^ 2) : ℝ) := by
  have hn1 : 1 < n := by omega
  have hnsq1 : 1 < n ^ 2 := by nlinarith
  have hpi := primeCounting_ge (n ^ 2) hnsq1
  have hlogn : 0 < log (n : ℝ) := Real.log_pos (by exact_mod_cast hn1)
  have hlog2lo : (103 / 150 : ℝ) < log 2 := by
    have := Real.log_two_gt_d9
    norm_num at this ⊢
    linarith
  have hlogn_le : log (n : ℝ) ≤ n := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < n)
    linarith
  have hlog_sq_add : log ((n : ℝ) ^ 2 + 1) ≤ (n : ℝ) ^ 2 / 50 := by
    calc
      log ((n : ℝ) ^ 2 + 1) ≤ log (2 * (n : ℝ) ^ 2) := by
        gcongr
        nlinarith
      _ = log 2 + 2 * log n := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        ring
      _ ≤ 1 + 2 * n := by
        have hlog2lt : log 2 < 1 := Real.log_lt_sub_one_of_pos (by norm_num)
        linarith
      _ ≤ (n : ℝ) ^ 2 / 50 := by
        norm_num at hn ⊢
        nlinarith
  have hnum : (2 / 3 : ℝ) * (n : ℝ) ^ 2 ≤
      (n : ℝ) ^ 2 * log 2 - log ((n : ℝ) ^ 2 + 1) := by
    nlinarith
  have hlogsq : log ((n : ℝ) ^ 2) = 2 * log n := by
    rw [Real.log_pow]
    norm_num
  rw [Nat.cast_pow, hlogsq] at hpi
  have hden : 0 < 2 * log (n : ℝ) := by positivity
  rw [div_le_iff₀ hden] at hpi
  rw [div_le_iff₀ (mul_pos (by norm_num) hlogn)]
  nlinarith

private theorem primeCounting_square_log_lower (n : ℕ) (hn : 128 ≤ n) :
    (13 / 9 : ℝ) * log n < log (π (n ^ 2) : ℝ) := by
  have hlower := primeCounting_square_lower n hn
  have hn1 : 1 < n := by omega
  have hlogn : 0 < log (n : ℝ) := Real.log_pos (by exact_mod_cast hn1)
  have hmargin := log_margin n hn
  have hbasepos : 0 < (n : ℝ) ^ 2 / (3 * log n) := by positivity
  have hpipos : 0 < (π (n ^ 2) : ℝ) := hbasepos.trans_le hlower
  have hloglower :
      log ((n : ℝ) ^ 2 / (3 * log n)) ≤ log (π (n ^ 2) : ℝ) :=
    Real.strictMonoOn_log.monotoneOn hbasepos hpipos hlower
  have hid : log ((n : ℝ) ^ 2 / (3 * log n)) =
      2 * log n - log 3 - log (log n) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow,
      Real.log_mul (by norm_num) hlogn.ne']
    ring
  rw [hid] at hloglower
  linarith

private theorem tail_log_increment (n : ℕ) (hn : 128 ≤ n) :
    (n : ℝ) * (log (π ((n + 1) ^ 2) : ℝ) - log (π (n ^ 2) : ℝ)) <
      log (π (n ^ 2) : ℝ) := by
  let A : ℝ := π (n ^ 2)
  let B : ℝ := π ((n + 1) ^ 2)
  let C : ℝ := wheelCount (n ^ 2 + 1) (2 * n + 1)
  have hn15 : 15 ≤ n := by omega
  have hBnat := primeCounting_square_succ_le n hn15
  have hB : B ≤ A + C := by exact_mod_cast hBnat
  have hCnat := square_wheelCount_bound n
  have hC : C ≤ ((16 * n + 106 : ℕ) : ℝ) / 35 := by
    rw [div_eq_iff (by norm_num : (35 : ℝ) ≠ 0)]
    exact_mod_cast hCnat
  have hAlower := primeCounting_square_lower n hn
  have hn1 : 1 < n := by omega
  have hlogn : 0 < log (n : ℝ) := Real.log_pos (by exact_mod_cast hn1)
  have hApos : 0 < A := (by positivity : 0 < (n : ℝ) ^ 2 / (3 * log n)).trans_le hAlower
  have hBpos : 0 < B := by
    have : 0 < (π (n ^ 2) : ℕ) := by
      exact_mod_cast hApos
    exact_mod_cast (this.trans_le (monotone_primeCounting (Nat.pow_le_pow_left (by omega) 2)))
  have hCnonneg : 0 ≤ C := by positivity
  have hlogratio : log B - log A ≤ C / A := by
    rw [← Real.log_div hBpos.ne' hApos.ne']
    calc
      log (B / A) ≤ log ((A + C) / A) := by
        gcongr
      _ ≤ (A + C) / A - 1 := Real.log_le_sub_one_of_pos (by positivity)
      _ = C / A := by field_simp; ring
  have hcoeff :
      3 * (((16 * n + 106 : ℕ) : ℝ) / 35) / n ≤ (13 / 9 : ℝ) := by
    norm_num at hn ⊢
    field_simp
    nlinarith
  have hratio : (n : ℝ) * (C / A) ≤ (13 / 9 : ℝ) * log n := by
    have hinvA : 1 / A ≤ (3 * log n) / (n : ℝ) ^ 2 := by
      rw [div_le_iff₀ hApos, one_mul]
      rw [← div_le_iff₀ (by positivity : 0 < 3 * log (n : ℝ))]
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hAlower
    calc
      (n : ℝ) * (C / A) = n * C * (1 / A) := by field_simp; ring
      _ ≤ n * (((16 * n + 106 : ℕ) : ℝ) / 35) * ((3 * log n) / n ^ 2) := by
        gcongr
      _ = (3 * (((16 * n + 106 : ℕ) : ℝ) / 35) / n) * log n := by
        field_simp
        ring
      _ ≤ (13 / 9 : ℝ) * log n := by gcongr
  have hlogA := primeCounting_square_log_lower n hn
  calc
    (n : ℝ) * (log B - log A) ≤ n * (C / A) := by gcongr
    _ ≤ (13 / 9 : ℝ) * log n := hratio
    _ < log A := hlogA

private theorem tail_integer_inequality (n : ℕ) (hn : 128 ≤ n) :
    (π ((n + 1) ^ 2)) ^ n < (π (n ^ 2)) ^ (n + 1) := by
  have hinc := tail_log_increment n hn
  have hApos : 0 < (π (n ^ 2) : ℝ) := by
    exact (by positivity : 0 < (n : ℝ) ^ 2 / (3 * log n)).trans_le
      (primeCounting_square_lower n hn)
  have hBpos : 0 < (π ((n + 1) ^ 2) : ℝ) := by
    have hmono := monotone_primeCounting (Nat.pow_le_pow_left (by omega) 2)
    exact_mod_cast (show 0 < π (n ^ 2) from by exact_mod_cast hApos).trans_le hmono
  have hlogpow :
      log ((π ((n + 1) ^ 2) : ℝ) ^ n) <
        log ((π (n ^ 2) : ℝ) ^ (n + 1)) := by
    rw [Real.log_pow, Real.log_pow]
    norm_num
    linarith
  have hreal :
      (π ((n + 1) ^ 2) : ℝ) ^ n < (π (n ^ 2) : ℝ) ^ (n + 1) :=
    Real.strictMonoOn_log.lt_iff_lt hBpos.pow hApos.pow |>.mp hlogpow
  exact_mod_cast hreal

private theorem finite_check (n : ℕ) (hn : 3 ≤ n) (hN : n < 128) :
    (π ((n + 1) ^ 2)) ^ n < (π (n ^ 2)) ^ (n + 1) := by
  interval_cases n <;>
    norm_num [Nat.primeCounting, Nat.primeCounting', Nat.count] at *

/--
Zhi-Wei Sun's Conjecture 2.14(ii), in the equivalent exact-integer form.
-/
@[category research solved, AMS 11]
theorem conjecture_2_14_ii (n : ℕ) (hn : 3 ≤ n) :
    (π ((n + 1) ^ 2)) ^ n < (π (n ^ 2)) ^ (n + 1) := by
  by_cases h : n < 128
  · exact finite_check n hn h
  · exact tail_integer_inequality n (by omega)

end SunConjecture214II
