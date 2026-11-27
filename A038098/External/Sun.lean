import A038098.Cases
import A038098.External.Riemann
import A038098.External.Small
import SunPrimeDensity.Main

/-! Sun's first OEIS A038098 conjecture from ordinary RH and Theorem 2
of Büthe, "An analytic method for bounding ψ(x)" (Math. Comp. 87).
The earlier theorem for exponents at least four and for cubes outside
the middle interval comes from senamakel/conjectures-lean at f34a54829210. -/

namespace Sun.CubeBridge
open Sun.CubeAnalytic

/-- The full statement, for all exponents at least three, conditional on RH
and the published finite estimate for Chebyshev's ψ through 10^19. -/
theorem conjecture1_of_RH_and_buthe (hRH : RiemannHypothesis)
    (hB : FinitePsi (10^19)) (k : ℕ) (hk : 2 < k) (n : ℕ) (hn : 2 ≤ n) :
    (Nat.primeCounting ((n + 1) ^ k) : ℚ) / ((n + 1) ^ k : ℚ) <
      (Nat.primeCounting (n ^ k) : ℚ) / (n ^ k : ℚ) := by
  refine ((SunPrimeDensity.sunConjecture_iff_of_RH hRH).2 ?_) k hk n hn
  intro m hlo hhi
  by_cases hs : m ≤ 200
  · simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
      Sun.CubeSieve.cubes_two_to_two_hundred m (by omega) hs
  have ht : m ≤ 10000000 := by norm_num at hhi; omega
  simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
    cubes_200_to_ten_million hRH hB m (by omega) ht

/-- The same conjecture needs the published bound only above 10^10 when the
previous finite ψ computation is included. -/
theorem conjecture1_of_RH_and_upper_finite_bound (hRH : RiemannHypothesis)
    (hB : ∀ x : ℝ, 10^10 < x → x ≤ 10^19 →
      |Chebyshev.psi x - x| ≤ 0.94 * Real.sqrt x)
    (k : ℕ) (hk : 2 < k) (n : ℕ) (hn : 2 ≤ n) :
    (Nat.primeCounting ((n + 1) ^ k) : ℚ) / ((n + 1) ^ k : ℚ) <
      (Nat.primeCounting (n ^ k) : ℚ) / (n ^ k : ℚ) :=
  conjecture1_of_RH_and_buthe hRH (finitePsi_of_above_ten_billion hB) k hk n hn

end Sun.CubeBridge

#print axioms Sun.CubeBridge.conjecture1_of_RH_and_buthe
#print axioms Sun.CubeBridge.conjecture1_of_RH_and_upper_finite_bound
