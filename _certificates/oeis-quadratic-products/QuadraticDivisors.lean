import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Divisors of the imaginary coefficient of a quadratic product

Write the product of the factors `1 + k√(-d)`, for k from 1 through n, as
`A + B√(-d)`. For all integers d, B is the nth triangular number times an
integer congruent to 1 modulo d. Thus for d ≥ 2 every positive m divides the
nonzero term at index 2m. The cases d = 2, 3, 4, 5 answer the prime-divisor
questions in OEIS A363410, A363412, A363414, A363416 respectively.
-/

namespace QuadraticDivisors

/-- The quadratic integer with coordinates (1,k). -/
def factor (d k : ℤ) : Zsqrtd (-d) := ⟨1, k⟩

/-- Product of the factors with indices a through a + n − 1. -/
def block (d a : ℤ) : ℕ → Zsqrtd (-d)
  | 0 => 1
  | n + 1 => block d a n * factor d (a + n)

theorem block_eq_prod (d a : ℤ) (n : ℕ) :
    block d a n = ∏ j ∈ Finset.range n, factor d (a + j) := by
  induction n with
  | zero => simp [block]
  | succ n ih => simp [block, Finset.prod_range_succ, ih]

/-- Evaluation in any commutative ring with a chosen square root of −d.
    Taking w = i√d recovers the complex products used in the OEIS entries. -/
theorem evaluate_block {R : Type*} [CommRing R] (d a : ℤ) (n : ℕ)
    (w : R) (hw : w * w = -(d : R)) :
    ((block d a n).re : R) + ((block d a n).im : R) * w =
      ∏ j ∈ Finset.range n, (1 + ((a : R) + (j : R)) * w) := by
  let f : Zsqrtd (-d) →+* R := Zsqrtd.lift ⟨w, by simpa using hw⟩
  change f (block d a n) = _
  rw [block_eq_prod, map_prod]
  apply Finset.prod_congr rfl
  intro j _
  change ((1 : ℤ) : R) + ((a + (j : ℤ) : ℤ) : R) * w = _
  simp

/-- Coefficient of √(-d) in the product with indices 1 through n. -/
def B (d : ℤ) (n : ℕ) : ℤ := (block d 1 n).im

/-- 1 + 2 + ⋯ + n. -/
def triangle : ℕ → ℤ
  | 0 => 0
  | n + 1 => triangle n + (n : ℤ) + 1

theorem two_mul_triangle (n : ℕ) :
    2 * triangle n = (n : ℤ) * (n + 1) := by
  induction n with
  | zero => simp [triangle]
  | succ n ih =>
    simp only [triangle, Nat.cast_succ]
    linear_combination ih

private theorem peel (d a : ℤ) (n : ℕ) :
    block d a (n + 1) = factor d a * block d (a + 1) n := by
  induction n with
  | zero => simp [block]
  | succ n ih =>
    change block d a (n + 1) * factor d (a + ((n + 1 : ℕ) : ℤ)) =
      factor d a * (block d (a + 1) n * factor d (a + 1 + n))
    rw [ih, mul_assoc]
    rw [show a + ((n + 1 : ℕ) : ℤ) = a + 1 + n by push_cast; ring]

private theorem pair_ends (d a : ℤ) (n : ℕ) :
    block d a (n + 2) =
      (factor d a * factor d (a + n + 1)) * block d (a + 1) n := by
  change block d a (n + 1) * factor d (a + ((n + 1 : ℕ) : ℤ)) = _
  rw [peel, show a + ((n + 1 : ℕ) : ℤ) = a + n + 1 by push_cast; ring]
  ac_rfl

private theorem real_form (d a : ℤ) (n : ℕ) :
    ∃ h : ℤ, (block d a n).re = 1 + d * h := by
  induction n with
  | zero => exact ⟨0, by simp [block]⟩
  | succ n ih =>
    obtain ⟨h, hh⟩ := ih
    refine ⟨h - (block d a n).im * (a + n), ?_⟩
    simp only [block, Zsqrtd.re_mul, factor, hh]
    ring

private theorem extend_pair {d a b u v l h t : ℤ}
    (hr : u = 1 + d * h) (hi : 2 * v - l * (a + b) = d * (a + b) * t) :
    2 * ((1 - d * a * b) * v + (a + b) * u) - (l + 2) * (a + b) =
      d * (a + b) * ((1 - d * a * b) * t - a * b * l + 2 * h) := by
  rw [hr]
  linear_combination (1 - d * a * b) * hi

/-- Pair the endpoints. For an interval of length n and endpoint sum s,
    d s divides twice its imaginary coefficient minus n s. -/
private theorem centered (d : ℤ) (n : ℕ) : ∀ a : ℤ,
    d * (2 * a + n - 1) ∣ 2 * (block d a n).im - n * (2 * a + n - 1) := by
  induction n using Nat.twoStepInduction with
  | zero => intro a; simp [block]
  | one =>
    intro a
    refine ⟨0, ?_⟩
    simp [block, factor]
  | more n ih _ =>
    intro a
    let b := a + (n : ℤ) + 1
    obtain ⟨h, hh⟩ := real_form d (a + 1) n
    obtain ⟨k, hk⟩ := ih (a + 1)
    rw [show 2 * (a + 1) + n - 1 = a + b by dsimp [b]; ring] at hk
    have hpair : (block d a (n + 2)).im =
        (1 - d * a * b) * (block d (a + 1) n).im +
          (a + b) * (block d (a + 1) n).re := by
      rw [pair_ends]
      simp only [Zsqrtd.im_mul, Zsqrtd.re_mul, factor, b]
      ring
    refine ⟨(1 - d * a * b) * k - a * b * n + 2 * h, ?_⟩
    rw [hpair]
    push_cast
    rw [show 2 * a + ((n : ℤ) + 2) - 1 = a + b by dsimp [b]; ring]
    exact extend_pair hh hk

/-- The quotient by the triangular number equals 1 modulo d. -/
theorem triangular_factor (d : ℤ) (n : ℕ) :
    ∃ k : ℤ, B d n = triangle n * (1 + d * k) := by
  have empty_factor : factor d 0 = 1 := rfl
  have prepend_zero : block d 0 (n + 1) = block d 1 n := by
    rw [peel, empty_factor]
    simp
  obtain ⟨u, hu⟩ := centered d (n + 1) 0
  obtain ⟨v, hv⟩ := centered d n 1
  rw [prepend_zero] at hu
  push_cast at hu
  have combined : 2 * B d n - (n : ℤ) * (n + 1) =
      d * ((n : ℤ) * (n + 1)) * (u - v) := by
    unfold B
    linear_combination ((n : ℤ) + 1) * hu - (n : ℤ) * hv
  refine ⟨u - v, ?_⟩
  have doubled : 2 * B d n = 2 * (triangle n * (1 + d * (u - v))) := by
    linear_combination combined - (1 + d * (u - v)) * two_mul_triangle n
  omega

private theorem unit_factor_ne_zero (d k : ℤ) (hd : 2 ≤ d) : 1 + d * k ≠ 0 := by
  by_cases hk : 0 ≤ k
  · have h := mul_nonneg (show 0 ≤ d by omega) hk
    omega
  · have h := mul_le_mul_of_nonneg_left (show k ≤ -1 by omega) (show 0 ≤ d by omega)
    omega

theorem coeff_ne_zero (d : ℤ) (hd : 2 ≤ d) {n : ℕ} (hn : 0 < n) : B d n ≠ 0 := by
  obtain ⟨k, hk⟩ := triangular_factor d n
  have hn' : 0 < (n : ℤ) := by exact_mod_cast hn
  have hp := mul_pos hn' (show 0 < (n : ℤ) + 1 by omega)
  have ht := two_mul_triangle n
  rw [hk]
  exact mul_ne_zero (by omega) (unit_factor_ne_zero d k hd)

/-- At index 2m there is always a nonzero multiple of m. -/
theorem nonzero_multiple (d : ℤ) (hd : 2 ≤ d) (m : ℕ) (hm : 0 < m) :
    (m : ℤ) ∣ B d (2 * m) ∧ B d (2 * m) ≠ 0 := by
  obtain ⟨k, hk⟩ := triangular_factor d (2 * m)
  have ht := two_mul_triangle (2 * m)
  push_cast at ht
  have ht' : triangle (2 * m) = (m : ℤ) * (2 * m + 1) := by nlinarith only [ht]
  refine ⟨⟨(2 * (m : ℤ) + 1) * (1 + d * k), ?_⟩, coeff_ne_zero d hd (by omega)⟩
  rw [hk, ht']
  ring

/-- The prime-divisor assertion of the four imaginary-coefficient entries. -/
theorem prime_divides_some_term (d : ℤ) (hd : 2 ≤ d) (p : ℕ) (hp : p.Prime) :
    ∃ n : ℕ, 0 < n ∧ B d n ≠ 0 ∧ (p : ℤ) ∣ B d n := by
  obtain ⟨divides, nonzero⟩ := nonzero_multiple d hd p hp.pos
  exact ⟨2 * p, by have := hp.pos; omega, nonzero, divides⟩

/-- At any prime divisor of d the triangular factor accounts for the entire
    valuation, with no additional powers contributed by the quotient. -/
theorem valuation_at_divisor (d : ℤ) (hd : 2 ≤ d) {p n : ℕ} (hp : p.Prime)
    (hpd : (p : ℤ) ∣ d) (hn : 0 < n) :
    padicValInt p (B d n) = padicValInt p (triangle n) := by
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := triangular_factor d n
  have ht : triangle n ≠ 0 := by
    intro h
    exact coeff_ne_zero d hd hn (by simp [hk, h])
  have hu : ¬ (p : ℤ) ∣ (1 + d * k) := by
    intro h
    have hm : (p : ℤ) ∣ d * k := dvd_mul_of_dvd_left hpd k
    have hone : (p : ℤ) ∣ (1 : ℤ) := by simpa using dvd_sub h hm
    exact (Nat.prime_iff_prime_int.mp hp).not_dvd_one hone
  rw [hk, padicValInt.mul ht (unit_factor_ne_zero d k hd),
    padicValInt.eq_zero_of_not_dvd hu, add_zero]

end QuadraticDivisors

#print axioms QuadraticDivisors.triangular_factor
#print axioms QuadraticDivisors.nonzero_multiple
#print axioms QuadraticDivisors.valuation_at_divisor
#print axioms QuadraticDivisors.evaluate_block
#print axioms QuadraticDivisors.prime_divides_some_term
