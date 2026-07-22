import RNAQuasiPowers.Covariance

namespace RNAQuasiPowers

noncomputable section

/-!
# Algebraic check of the density correction

The density printed in the source paper has precision matrix

`[[1, -c], [-c, 1]]`.

Its covariance matrix is therefore

`(1 / (1-c^2)) • [[1, c], [c, 1]]`.

The scalar certificate below proves that its marginal variance is strictly
larger than one. Hence the printed density cannot be the weak limit after each
coordinate has been divided by its exact standard deviation. The corrected
density uses covariance matrix `[[1,c],[c,1]]`.
-/

/-- Marginal variance of the Gaussian density as literally printed. -/
def printedMarginalVariance : Real := 1 / (1 - correlationSquare)

theorem correlationSquare_pos : 0 < correlationSquare := by
  unfold correlationSquare
  nlinarith [correlationNumerator_pos]

theorem correlationSquare_lt_one : correlationSquare < 1 := by
  unfold correlationSquare
  nlinarith [sqrtFive_lt_three]

theorem one_sub_correlationSquare_pos : 0 < 1 - correlationSquare := by
  linarith [correlationSquare_lt_one]

/-- The printed density has marginal variance greater than one. -/
theorem printedMarginalVariance_gt_one : 1 < printedMarginalVariance := by
  unfold printedMarginalVariance
  rw [lt_div_iff₀ one_sub_correlationSquare_pos]
  linarith [correlationSquare_pos]

/-- The printed density is incompatible with unit marginal variances. -/
theorem printedMarginalVariance_ne_one : printedMarginalVariance ≠ 1 := by
  exact ne_of_gt printedMarginalVariance_gt_one

end

end RNAQuasiPowers
