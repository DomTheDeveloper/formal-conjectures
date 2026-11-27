module

public import A038098.Envelope
public import Mathlib.NumberTheory.AbelSummation

public section
namespace Sun.CubeAnalytic
open MeasureTheory ArithmeticFunction Finset

/-- At an integer the integral of ψ used here is exactly the finite weighted
von Mangoldt sum used in the integer explicit formula. -/
theorem integral_psi_eq_weighted_sum (k : ℕ) (hk : 1≤k) :
    (∫ t in (1:ℝ)..(k:ℝ), Chebyshev.psi t) =
      ∑ n ∈ range (k+1), (vonMangoldt n : ℝ)*((k:ℝ)-n) := by
  have der : deriv (fun t : ℝ => (k:ℝ)-t) = fun _ => -1 := by
    funext x
    exact ((hasDerivAt_id x).const_sub (k:ℝ)).deriv
  have h := sum_mul_eq_sub_integral_mul₀' (fun n => (vonMangoldt n:ℝ))
    (f := fun t : ℝ => (k:ℝ)-t) (by simp) k (fun _ _ => by fun_prop) (by
      rw [der]
      exact integrableOn_const (by simp))
  rw [der] at h
  simp only [sub_self,zero_mul,zero_sub,neg_one_mul,integral_neg,neg_neg,
    ← Chebyshev.psi_eq_sum_Icc] at h
  rw [intervalIntegral.integral_of_le (by exact_mod_cast hk),← h,Nat.range_succ_eq_Icc_zero]
  exact sum_congr rfl fun _ _ => mul_comm _ _

end Sun.CubeAnalytic
#print axioms Sun.CubeAnalytic.integral_psi_eq_weighted_sum
