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

public import FormalConjecturesUtil
import FormalConjectures.Paper.RiemannHypothesisEquivalents

/-!
# Exceptions to Robin's inequality

The sequence consists of integers $n \ge 2$ for which the sum of divisors
$\sigma(n)$ is at least $e^\gamma n\log\log n$, where $\gamma$ is Euler's constant.

*References:*
- [OEIS A067698](https://oeis.org/A067698)
- G. Robin, *Grandes valeurs de la fonction somme des diviseurs et hypothèse de Riemann*,
  J. Math. Pures Appl. 63 (1984), 187–213.
-/

@[expose] public section

namespace OeisA067698

open Real
open scoped ArithmeticFunction.sigma

/-- The integer $n$ is in the domain of $\log\log n$ and violates Robin's strict inequality. -/
def A (n : ℕ) : Prop :=
  2 ≤ n ∧ exp eulerMascheroniConstant * n * log (log n) ≤ (σ 1 n : ℝ)

@[category API, AMS 11]
private theorem exp_gamma_le : exp eulerMascheroniConstant ≤ 1787 / 1000 := by
  have hh : harmonic 256 ≤ (15311 / 2500 : ℚ) := by
    set_option maxRecDepth 8192 in decide +kernel
  have hc : (harmonic 256 : ℝ) ≤ ((15311 / 2500 : ℚ) : ℝ) := Rat.cast_mono hh
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hc
  have hg := eulerMascheroniConstant_lt_eulerMascheroniSeq' 256
  change eulerMascheroniConstant < (harmonic 256 : ℝ) - log 256 at hg
  rw [show (256 : ℝ) = 2 ^ 8 by norm_num, log_pow] at hg
  norm_num only [Nat.cast_ofNat] at hg
  have hγ : eulerMascheroniConstant ≤ 58 / 100 := by linarith only [hg, hc, log_two_gt_d9]
  refine (exp_le_exp.mpr hγ).trans <| (exp_bound' (x := (58 / 100 : ℝ)) (by norm_num)
    (by norm_num) (n := 8) (by norm_num)).trans ?_
  norm_num [Finset.sum_range_succ, Nat.factorial_succ]

@[category API, AMS 11]
private theorem mem_of_bounds {n : ℕ} {x y : ℝ} (hn : 2 ≤ n) (hy : 0 ≤ y)
    (hx : (n : ℝ) ≤ exp x) (hxy : x ≤ exp y)
    (hσ : (1787 / 1000 : ℝ) * n * y ≤ (σ 1 n : ℝ)) : A n := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hlog := (log_le_iff_le_exp (log_pos hn')).2
    (((log_le_iff_le_exp (by positivity : (0 : ℝ) < n)).2 hx).trans hxy)
  refine ⟨hn, le_trans (mul_le_mul_of_nonneg_left hlog (by positivity)) ?_⟩
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right exp_gamma_le (by positivity)) hy).trans hσ

@[category API, AMS 11]
private theorem mem_small {n : ℕ} (hn : 2 ≤ n) (h6 : n ≤ 6) : A n := by
  have h : ∀ m ∈ Finset.Icc 2 6, 5361 * m ≤ 5000 * σ 1 m := by
    simp_rw [ArithmeticFunction.sigma_one_apply]
    decide +kernel
  have hσ : (5361 : ℝ) * n ≤ 5000 * (σ 1 n : ℝ) := by
    exact_mod_cast h n (Finset.mem_Icc.mpr ⟨hn, h6⟩)
  apply mem_of_bounds (x := 9 / 5) (y := 3 / 5) hn (by norm_num)
  · refine (show (n : ℝ) ≤ 6 by exact_mod_cast h6).trans <| le_trans ?_
      (sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 5) 8)
    norm_num [Finset.sum_range_succ, Nat.factorial_succ]
  · refine le_trans ?_ (sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 5) 4)
    norm_num [Finset.sum_range_succ, Nat.factorial_succ]
  · linarith only [hσ]

@[category test, AMS 11]
theorem a_2 : A 2 := mem_small (by decide) (by decide)

@[category test, AMS 11]
theorem a_3 : A 3 := mem_small (by decide) (by decide)

@[category test, AMS 11]
theorem a_4 : A 4 := mem_small (by decide) (by decide)

@[category test, AMS 11]
theorem a_5 : A 5 := mem_small (by decide) (by decide)

@[category test, AMS 11]
theorem a_6 : A 6 := mem_small (by decide) (by decide)

/-- The final listed term, $5040$, violates Robin's inequality. -/
@[category test, AMS 11]
theorem a_5040 : A 5040 := by
  have hs : σ 1 5040 = 19344 := by
    rw [ArithmeticFunction.sigma_one_apply]
    set_option maxRecDepth 20000 in decide +kernel
  apply mem_of_bounds (x := 853 / 100) (y := 2144 / 1000) (by decide) (by norm_num)
  · refine le_trans ?_ (sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 853 / 100) 18)
    norm_num [Finset.sum_range_succ, Nat.factorial_succ]
  · refine le_trans ?_ (sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2144 / 1000) 10)
    norm_num [Finset.sum_range_succ, Nat.factorial_succ]
  · norm_num [hs]

/-- Robin's strict inequality above $5040$ characterizes the greatest element of the sequence. -/
@[category API, AMS 11]
theorem isGreatest_iff_robin :
    IsGreatest {n | A n} 5040 ↔
      ∀ n : ℕ, 5040 < n → (σ 1 n : ℝ) < exp eulerMascheroniConstant * n * log (log n) := by
  constructor
  · intro h n hn
    exact lt_of_not_ge fun hbad ↦ (not_le_of_gt hn) (h.2 (show A n from ⟨by omega, hbad⟩))
  · intro h
    exact ⟨a_5040, fun n hn ↦ le_of_not_gt fun hgt ↦ (h n hgt).not_ge hn.2⟩

/-- “5040 is the last element in the sequence iff the Riemann hypothesis is true.” -/
@[category research solved, AMS 11]
theorem isGreatest_iff_riemannHypothesis : IsGreatest {n | A n} 5040 ↔ RiemannHypothesis :=
  isGreatest_iff_robin.trans RiemannHypothesis.robin_criterion.symm

/-- The greatest member of the sequence is $5040$. -/
@[category research solved, AMS 11]
theorem isGreatest_5040 : IsGreatest {n | A n} 5040 :=
  isGreatest_iff_robin.mpr fun _ hn ↦ RiemannHypothesis.robin_criterion_rhs hn

end OeisA067698
