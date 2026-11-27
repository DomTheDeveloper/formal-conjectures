import A038098.FiniteEnvelope
import Schoenfeld.PsiCert.Final

/-! The previously certified bound for ψ through ten billion suffices for the
next cube comparisons. Its numerical input uses native_decide. -/
namespace Sun.CubeBridge
open Sun.CubeAnalytic Real

theorem cubes_200_to_2153_checked (n : ℕ) (hn : 200 ≤ n) (hi : n ≤ 2153) :
    (((n+1)^3).primeCounting : ℚ) / (((n+1)^3:ℕ):ℚ) <
      ((n^3).primeCounting : ℚ) / ((n^3:ℕ):ℚ) :=
  cubes_200_to_2153 Schoenfeld.psiCert n hn hi

/-- Only the part of Büthe's published estimate above the end of the
existing finite certificate is needed when combining both results. -/
theorem finitePsi_of_above_ten_billion
    (hB : ∀ x : ℝ, 10^10 < x → x ≤ 10^19 →
      |Chebyshev.psi x - x| ≤ 0.94 * √x) : FinitePsi (10^19) := by
  intro x hmin hmax
  by_cases hx : x ≤ 10^10
  · exact (Schoenfeld.psiCert x hmin hx).trans
      (mul_le_mul_of_nonneg_right (by norm_num) (sqrt_nonneg x))
  exact hB x (lt_of_not_ge hx) hmax

end Sun.CubeBridge
#print axioms Sun.CubeBridge.cubes_200_to_2153_checked
