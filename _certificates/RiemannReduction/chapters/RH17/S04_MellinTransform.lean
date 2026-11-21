import RH17.S02_SingleCharacter
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.MellinRamp

/-! # 4. See the ramp in the transform
Integrate the ramp against y^(−s−1). For y ≥ n the ramp is y/n−1, so the
integral is a difference of two elementary integrals. Their denominators give
1/(s−1) − 1/s. The factor n^(−s) turns a sum over prime powers into the
Dirichlet series for the logarithmic derivative of zeta. -/

namespace RH17

open MeasureTheory Set

theorem rampTransform (n : ℕ) (hn : 1 ≤ n) (s : ℂ) (hs : 1 < s.re) :
    (∫ y in Ioi (1 : ℝ), ((max (y / n - 1) 0 : ℝ) : ℂ) * (y : ℂ) ^ (-s-1)) *
      (s * (s-1)) = (n : ℂ) ^ (-s) := by
  rw [Deduction.mellin_ramp n hn s hs]
  have h0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have h1 : s ≠ 1 := by rintro rfl; norm_num at hs
  exact div_mul_cancel₀ _ (mul_ne_zero h0 (sub_ne_zero.mpr h1))

end RH17
