import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Coefficient and residue lemmas for the cubic and quadratic row congruences. -/

open Finset PowerSeries
open scoped BigOperators PowerSeries

namespace BalaFraming

/-- Multiplying units by two controls the complete inverse-square sum. -/
theorem three_mul_inverse_square_sum {R : Type*} [CommRing R] [Fintype Rˣ]
    (h2 : IsUnit (2 : R)) :
    3 * (∑ u : Rˣ, (↑u⁻¹ : R) ^ 2) = 0 := by
  classical
  obtain ⟨b, hb⟩ := h2
  have h : (4 : R) * (∑ u : Rˣ, (↑u : R) ^ 2) = ∑ u : Rˣ, (↑u : R) ^ 2 := by
    calc
      _ = ∑ u : Rˣ, (↑(b * u) : R) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _
        rw [Units.val_mul, hb]
        ring
      _ = _ := Equiv.sum_comp (Equiv.mulLeft b) (fun u : Rˣ => (↑u : R) ^ 2)
  have hi : (∑ u : Rˣ, (↑u⁻¹ : R) ^ 2) = ∑ u : Rˣ, (↑u : R) ^ 2 :=
    Equiv.sum_comp (Equiv.inv Rˣ) (fun u : Rˣ => (↑u : R) ^ 2)
  rw [hi]
  linear_combination h

/-- The inverse-square sum vanishes modulo every positive power of a prime at least five. -/
theorem inverse_square_sum_prime_power (p e : ℕ) [NeZero p] (hp : p.Prime) (h5 : 5 ≤ p)
    (he : 0 < e) :
    ∑ u : (ZMod (p ^ e))ˣ, (↑u⁻¹ : ZMod (p ^ e)) ^ 2 = 0 := by
  have hsmall (a : ℕ) (ha : 0 < a) (hb : a < p) : IsUnit (a : ZMod (p ^ e)) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow hp he).2
      (fun h => (Nat.not_le_of_gt hb) (Nat.le_of_dvd ha h))
  have h2 : IsUnit (2 : ZMod (p ^ e)) := by simpa using hsmall 2 (by decide) (by omega)
  have h3 : IsUnit (3 : ZMod (p ^ e)) := by simpa using hsmall 3 (by decide) (by omega)
  exact h3.mul_right_inj.mp (by simpa using three_mul_inverse_square_sum h2)

/-- Differentiating a power relates the index times its coefficient to its exponent. -/
theorem index_mul_coeff (F : ℤ⟦X⟧) (m j : ℕ) :
    coeff (j + 1) (F ^ m) * (j + 1 : ℤ) =
      (m : ℤ) * coeff j (F ^ (m - 1) * derivative ℤ F) := by
  rw [← coeff_derivative, derivative_pow, mul_assoc]
  rw [show (m : ℤ⟦X⟧) = C (m : ℤ) by simp, coeff_C_mul]

/-- In every positive row the row number divides the diagonal coefficient. -/
theorem diagonal_normalization (F : ℤ⟦X⟧) (n k : ℕ) :
    coeff (k + 1) (F ^ (n * (k + 1))) =
      (n : ℤ) * coeff k (F ^ (n * (k + 1) - 1) * derivative ℤ F) := by
  have h := index_mul_coeff F (n * (k + 1)) k
  apply mul_right_cancel₀ (show (k + 1 : ℤ) ≠ 0 by positivity)
  calc
    _ = _ := h
    _ = _ := by push_cast; ring

/-- Every positive Franel number is even. -/
theorem franel_even (n : ℕ) (hn : 0 < n) :
    2 ∣ (∑ k ∈ range (n + 1), (n.choose k) ^ 3) := by
  have cube (x : ZMod 2) : x ^ 3 = x := by decide +revert
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  push_cast
  simp only [cube]
  rw [← Nat.cast_sum, Nat.sum_range_choose]
  push_cast
  rw [show (2 : ZMod 2) = 0 by decide, zero_pow (Nat.ne_of_gt hn)]

#print axioms three_mul_inverse_square_sum
#print axioms inverse_square_sum_prime_power
#print axioms diagonal_normalization
#print axioms franel_even

end BalaFraming
