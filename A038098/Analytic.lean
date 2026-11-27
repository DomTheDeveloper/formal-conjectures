module

public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

public section
namespace Sun.CubeAnalytic
open Real

/-- Every prime in the interval contributes at least log x to the increment of ψ. -/
theorem prime_increment_le {x y : ℕ} (hx : 1 < x) (hxy : x ≤ y) :
    ((y.primeCounting : ℝ) - x.primeCounting) * log x ≤ Chebyshev.psi y - Chebyshev.psi x := by
  induction y, hxy using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have hs : Chebyshev.psi (↑(m + 1) : ℝ) =
        Chebyshev.psi m + ArithmeticFunction.vonMangoldt (m + 1) := by
      simp only [Chebyshev.psi, Nat.floor_natCast]
      rw [Finset.sum_Ioc_succ_top (Nat.zero_le m)]
    have hc : (m + 1).primeCounting =
        m.primeCounting + (if (m + 1).Prime then 1 else 0) := Nat.count_succ _ _
    rw [hs,hc]
    by_cases hp : (m + 1).Prime
    · simp only [if_pos hp, Nat.cast_add, Nat.cast_one, ArithmeticFunction.vonMangoldt_apply_prime hp]
      have hl : log x ≤ log (↑(m + 1) : ℝ) :=
        log_le_log (by exact_mod_cast (show 0 < x by omega)) (by exact_mod_cast (show x ≤ m+1 by omega))
      push_cast at hl
      linarith
    · simp only [if_neg hp, Nat.add_zero]
      linarith [ArithmeticFunction.vonMangoldt_nonneg (n := m+1)]

/-- Compare the two rational prime proportions using one lower bound and one interval upper bound. -/
theorem ratio_lt_of_psi {x y : ℕ} {c : ℝ} (hx : 1 < x) (hxy : x < y)
    (hlower : c / log x ≤ (x.primeCounting : ℝ) / x)
    (hupper : Chebyshev.psi y - Chebyshev.psi x < ((y : ℝ) - x) * c) :
    (y.primeCounting : ℚ) / (y : ℚ) < (x.primeCounting : ℚ) / (x : ℚ) := by
  have xpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have ypos : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
  have logpos : 0 < log (x : ℝ) := log_pos (by exact_mod_cast hx)
  have hi := lt_of_le_of_lt (prime_increment_le hx hxy.le) hupper
  have hi' := (lt_div_iff₀ logpos).2 hi
  rw [mul_div_assoc] at hi'
  have inc := hi'.trans_le (mul_le_mul_of_nonneg_left hlower (sub_nonneg.mpr (by exact_mod_cast hxy.le)))
  have cross := (lt_div_iff₀ xpos).1 (show (y.primeCounting : ℝ) - x.primeCounting <
      ((y : ℝ) - x) * x.primeCounting / x by simpa only [mul_div_assoc] using inc)
  have cmp : (y.primeCounting : ℝ) / y < (x.primeCounting : ℝ) / x := by
    apply (div_lt_div_iff₀ ypos xpos).2
    linarith
  rw [← Rat.cast_lt (K := ℝ)]
  push_cast
  exact cmp

/-- A uniform numerical margin for the zero-sum estimate in the middle cube range. -/
theorem middle_margin {t u v : ℝ} (ht : 43.7 ≤ t) (ht' : t ≤ 52)
    (hu : t / 3 - 2.4 ≤ u) (hv : v ≤ t / 2 - 2.75) (hv0 : 0 ≤ v) :
    6.01 + 2.01 / (2 * π) * (v^2-u^2+2*v+2*u) < 2.994 * exp (t/6) / t := by
  have coeff : (2.01 : ℝ) / (2 * π) ≤ 0.32 := by
    rw [div_le_iff₀ (by positivity)]; linarith [Real.pi_gt_d6]
  let a := t/3 - 2.4
  let b := t/2 - 2.75
  have ha : 1 ≤ a := by dsimp [a]; linarith
  have hquad : v^2-u^2+2*v+2*u ≤ b^2-a^2+2*b+2*a := by
    have h₁ := mul_nonneg (sub_nonneg.mpr (show v ≤ b from hv)) (show 0 ≤ b+v+2 by dsimp [b]; linarith)
    have h₂ := mul_nonneg (sub_nonneg.mpr (show a ≤ u from hu)) (show 0 ≤ u+a-2 by dsimp [a] at *; linarith)
    nlinarith
  have hab : a ≤ b := by dsimp [a,b]; linarith
  have nn : 0 ≤ b^2-a^2+2*b+2*a := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (show 0 ≤ b+a by linarith)]
  have env := (mul_le_mul_of_nonneg_left hquad (show 0 ≤ 2.01/(2*π) by positivity)).trans
    (mul_le_mul_of_nonneg_right coeff nn)
  have pbound : 6.01 + 2.01/(2*π)*(v^2-u^2+2*v+2*u) ≤ 95.6 + 6*(t-43.7) := by
    dsimp [a,b] at env
    nlinarith [mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr ht')]
  have base : (1400:ℝ) < exp (43.7/6) := by
    have e : (2.718 : ℝ)^7 ≤ (exp 1)^7 :=
      pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 7
    have hf := Real.add_one_le_exp ((43.7:ℝ)/6-7)
    rw [show (43.7:ℝ)/6 = (7:ℕ)*1 + (43.7/6-7) by norm_num, Real.exp_add, Real.exp_nat_mul]
    nlinarith [mul_le_mul_of_nonneg_right e (le_of_lt (Real.exp_pos ((43.7:ℝ)/6-7)))]
  have ex : exp (t/6) ≥ 1400*(1+(t-43.7)/6) := by
    rw [show t/6 = 43.7/6+(t-43.7)/6 by ring, Real.exp_add]
    apply mul_le_mul base.le _ (by linarith) (Real.exp_pos _).le
    linarith [Real.add_one_le_exp ((t-43.7)/6)]
  apply (lt_div_iff₀ (show 0<t by linarith)).2
  have prod := mul_le_mul_of_nonneg_right pbound (show 0 ≤ t by linarith)
  nlinarith [mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr ht')]

theorem explicit_formula_margin {t : ℝ} (ht : 43.7 ≤ t) (ht' : t ≤ 52) :
    let u := t / 3 + log (2.01 / (3.01 * (2 * π)))
    let v := t / 2 + log (0.671 / (2.01 * (2 * π)))
    6.01 + 2.01 / (2 * π) * (v^2-u^2+2*v+2*u) < 2.994 * exp (t/6) / t := by
  dsimp only
  have e24 : 10 < exp (2.4 : ℝ) := by
    rw [show (2.4:ℝ) = (2:ℕ)*1+0.4 by norm_num, exp_add, exp_nat_mul]
    have h2 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7)
      (show 2.7 ≤ exp 1 by linarith [exp_one_gt_d9]) 2
    nlinarith [mul_le_mul_of_nonneg_right h2 (exp_pos 0.4).le, add_one_le_exp (0.4:ℝ)]
  have e275 : exp (2.75:ℝ) < 18 := by
    have h3 := pow_le_pow_left₀ (exp_pos 1).le
      (show exp 1 ≤ 2.72 by linarith [exp_one_lt_d9]) 3
    rw [← exp_nat_mul] at h3
    rw [show (3:ℕ)*(1:ℝ) = 2.75+0.25 by norm_num, exp_add] at h3
    nlinarith [mul_le_mul_of_nonneg_left (add_one_le_exp (0.25:ℝ)) (exp_pos 2.75).le]
  have hneg {r s : ℝ} (hr : 0 < r) (h : 1 / r ≤ exp s) : -s ≤ log r := by
    have := (log_le_iff_le_exp (by positivity : 0 < 1/r)).2 h
    rw [one_div, log_inv] at this
    linarith
  have hu : -(2.4 : ℝ) ≤ log (2.01/(3.01*(2*π))) := by
    apply hneg (by positivity)
    rw [one_div_div]
    apply le_trans _ e24.le
    rw [div_le_iff₀ (by norm_num)]
    linarith [pi_lt_d6]
  have hv : log (0.671/(2.01*(2*π))) ≤ -(2.75 : ℝ) := by
    rw [log_le_iff_le_exp (by positivity), exp_neg, le_inv_comm₀ (by positivity) (exp_pos _)]
    rw [inv_div]
    apply le_trans e275.le
    rw [le_div_iff₀ (by norm_num)]
    linarith [pi_gt_d6]
  have hvl : -(4:ℝ) ≤ log (0.671/(2.01*(2*π))) := by
    apply hneg (by positivity)
    rw [one_div_div]
    have h4 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7)
      (show 2.7 ≤ exp 1 by linarith [exp_one_gt_d9]) 4
    rw [← exp_nat_mul] at h4
    norm_num1 at h4
    apply le_trans _ h4
    rw [div_le_iff₀ (by norm_num)]
    linarith [pi_lt_d6]
  exact middle_margin ht ht' (by linarith) (by linarith) (by linarith)

/-- Monotonicity bounds the increment by a difference of two adjacent interval integrals. -/
theorem smoothed_increment (x y d : ℝ) (hd : 0 < d) :
    let F := fun z : ℝ => ∫ u in (1 : ℝ)..z, Chebyshev.psi u
    Chebyshev.psi y - Chebyshev.psi x ≤ (F (y+d) - F y - F x + F (x-d)) / d := by
  dsimp only
  have integ (a b : ℝ) : IntervalIntegrable Chebyshev.psi MeasureTheory.volume a b :=
    Chebyshev.psi_mono.intervalIntegrable
  have upper := intervalIntegral.integral_mono_on (show y ≤ y+d by linarith)
    (intervalIntegrable_const (c := Chebyshev.psi y)) (integ y (y+d))
    (fun u hu => Chebyshev.psi_mono hu.1)
  have lower := intervalIntegral.integral_mono_on (show x-d ≤ x by linarith)
    (integ (x-d) x) (intervalIntegrable_const (c := Chebyshev.psi x))
    (fun u hu => Chebyshev.psi_mono hu.2)
  rw [intervalIntegral.integral_const, smul_eq_mul] at upper lower
  have hy := intervalIntegral.integral_add_adjacent_intervals (integ 1 y) (integ y (y+d))
  have hx := intervalIntegral.integral_add_adjacent_intervals (integ 1 (x-d)) (integ (x-d) x)
  apply (le_div_iff₀ hd).2
  linarith
end Sun.CubeAnalytic
#print axioms Sun.CubeAnalytic.prime_increment_le
#print axioms Sun.CubeAnalytic.ratio_lt_of_psi
#print axioms Sun.CubeAnalytic.middle_margin
#print axioms Sun.CubeAnalytic.explicit_formula_margin
#print axioms Sun.CubeAnalytic.smoothed_increment
