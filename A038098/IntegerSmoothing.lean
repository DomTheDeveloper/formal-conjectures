module

public import A038098.Middle

public section
namespace Sun.CubeAnalytic
open Real

/-- In the integer explicit formula the affine terms cancel exactly, and the
four one-sided remainders cost at most 3 before dividing by the width. -/
theorem integer_four_point {F Z E : ℕ → ℝ} {k c : ℝ}
    (hF : ∀ m : ℕ, 1 ≤ m → F m = (m:ℝ)^2/2-Z m+k*m+E m+c)
    (hE : ∀ m : ℕ, 1 ≤ m → (m:ℝ)-3/2 ≤ E m ∧ E m ≤ m)
    {x y d : ℕ} (hd : 1 ≤ d) (hxd : d < x) (hy : 1 ≤ y) :
    (F (y+d)-F y-F x+F (x-d))/(d:ℝ) ≤ (y:ℝ)-x+d+
      (|Z (y+d)-Z y-Z x+Z (x-d)|+3)/d := by
  have hd0 : 0 < (d:ℝ) := by exact_mod_cast (show 0 < d by omega)
  have h₁ := (hE (y+d) (by omega)).2
  have h₂ := (hE y hy).1
  have h₃ := (hE x (by omega)).1
  have h₄ := (hE (x-d) (by omega)).2
  have hz := neg_abs_le (Z (y+d)-Z y-Z x+Z (x-d))
  apply (div_le_iff₀ hd0).2
  rw [add_mul,div_mul_cancel₀ _ hd0.ne',hF (y+d) (by omega),hF y hy,
    hF x (by omega),hF (x-d) (by omega)]
  rw [Nat.cast_add] at h₁ ⊢
  rw [Nat.cast_sub hxd.le] at h₄ ⊢
  nlinarith only [hz,h₁,h₂,h₃,h₄]

/-- An integer explicit formula of the form used by Schoenfeld reduces the middle
input to its four-point zero sum. The integral is Mathlib's Chebyshev psi. -/
theorem smoothed_of_integer_zero_sum {n d : ℕ} (hd : 1≤d) (hxd : d<n^3)
    {Z E : ℕ → ℝ} {k c : ℝ}
    (hF : ∀ m : ℕ, 1 ≤ m → (∫ t in (1:ℝ)..(m:ℝ), Chebyshev.psi t) =
      (m:ℝ)^2/2-Z m+k*m+E m+c)
    (hE : ∀ m : ℕ, 1 ≤ m → (m:ℝ)-3/2 ≤ E m ∧ E m ≤ m)
    (hZ : |Z ((n+1)^3+d)-Z ((n+1)^3)-Z (n^3)+Z (n^3-d)|+3 ≤
      (d:ℝ)*(√((n:ℝ)^3)*errorCoeff (log ((n:ℝ)^3)) - d)) :
    SmoothedBound n := by
  have hd0 : 0<(d:ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hy : 1 ≤ (n+1)^3 := Nat.succ_le_of_lt (pow_pos (Nat.succ_pos n) _)
  have H := integer_four_point
    (F := fun m : ℕ => ∫ t in (1:ℝ)..(m:ℝ), Chebyshev.psi t) hF hE hd hxd hy
  have hgain : (|Z ((n+1)^3+d)-Z ((n+1)^3)-Z (n^3)+Z (n^3-d)|+3)/(d:ℝ) ≤
      √((n:ℝ)^3)*errorCoeff (log ((n:ℝ)^3)) - d :=
    (div_le_iff₀ hd0).2 (by simpa only [mul_comm (d:ℝ)] using hZ)
  refine ⟨(d:ℝ),hd0,?_⟩
  simp only [Nat.cast_add,Nat.cast_sub hxd.le,Nat.cast_pow,Nat.cast_one] at H
  exact H.trans (by linarith only [hgain])

end Sun.CubeAnalytic
#print axioms Sun.CubeAnalytic.smoothed_of_integer_zero_sum
