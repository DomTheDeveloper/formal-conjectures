import RNAQuasiPowers.Radicand

namespace RNAQuasiPowers

noncomputable section

/-- A named copy of `sqrt 5`, used to keep the algebra readable. -/
def sqrtFive : Real := Real.sqrt 5

/-- The small root of `t^2 - 3t + 1`. -/
def rho : Real := (3 - sqrtFive) / 2

/-- The other real root of `t^2 - 3t + 1`. -/
def rhoLarge : Real := (3 + sqrtFive) / 2

theorem sqrtFive_nonneg : 0 <= sqrtFive := by
  unfold sqrtFive
  exact Real.sqrt_nonneg 5

theorem sqrtFive_sq : sqrtFive ^ 2 = 5 := by
  unfold sqrtFive
  simpa using (Real.sq_sqrt (show (0 : Real) <= 5 by norm_num))

theorem sqrtFive_pos : 0 < sqrtFive := by
  nlinarith [sqrtFive_sq, sqrtFive_nonneg]

theorem two_lt_sqrtFive : 2 < sqrtFive := by
  nlinarith [sqrtFive_sq, sqrtFive_nonneg]

theorem sqrtFive_lt_three : sqrtFive < 3 := by
  nlinarith [sqrtFive_sq, sqrtFive_nonneg]

theorem rho_pos : 0 < rho := by
  unfold rho
  linarith [sqrtFive_lt_three]

theorem rho_lt_one : rho < 1 := by
  unfold rho
  linarith [two_lt_sqrtFive]

theorem rhoLarge_gt_one : 1 < rhoLarge := by
  unfold rhoLarge
  linarith [sqrtFive_pos]

theorem rho_quadratic : rho ^ 2 - 3 * rho + 1 = 0 := by
  unfold rho
  nlinarith [sqrtFive_sq]

theorem quadratic_factor (t : Real) :
    t ^ 2 - 3 * t + 1 = (t - rho) * (t - rhoLarge) := by
  unfold rho rhoLarge
  nlinarith [sqrtFive_sq]

theorem quadratic_roots {t : Real} (h : t ^ 2 - 3 * t + 1 = 0) :
    Or (t = rho) (t = rhoLarge) := by
  rw [quadratic_factor] at h
  rcases mul_eq_zero.mp h with hsmall | hlarge
  · left
    linarith
  · right
    linarith

/-- `rho` is the unique root of the quadratic factor in the open unit interval. -/
theorem rho_unique_in_unit {t : Real}
    (ht0 : 0 < t) (ht1 : t < 1) (hquad : t ^ 2 - 3 * t + 1 = 0) :
    t = rho := by
  rcases quadratic_roots hquad with hsmall | hlarge
  · exact hsmall
  · exfalso
    rw [hlarge] at ht1
    linarith [rhoLarge_gt_one]

/-- The proposed dominant singularity is a zero of the unmarked radicand. -/
theorem radicand_rho : radicand rho 1 1 = 0 := by
  rw [radicand_at_one_factor, rho_quadratic]
  ring

/-- The derivative value at the proposed dominant singularity. -/
theorem dRadicandAtOne_rho :
    dRadicandAtOne rho = 30 - 14 * sqrtFive := by
  rw [dRadicandAtOne_reduction, rho_quadratic]
  unfold rho
  ring

/-- The root is simple at the unmarked point. -/
theorem dRadicandAtOne_rho_ne_zero : Not (dRadicandAtOne rho = 0) := by
  rw [dRadicandAtOne_rho]
  intro h
  have hs : sqrtFive = (15 : Real) / 7 := by
    linarith
  have hsq := congrArg (fun y : Real => y ^ 2) hs
  rw [sqrtFive_sq] at hsq
  norm_num at hsq

end

end RNAQuasiPowers
