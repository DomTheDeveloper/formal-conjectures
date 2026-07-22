/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjecturesUtil

/-!
# Density erratum for the RNA hairpin/basepair conjecture

The conjecture in Bu--Kauers--Zeilberger standardizes each coordinate by its
own exact standard deviation, and therefore intends a Gaussian limit with unit
marginal variances.  The density displayed in the paper instead has precision
matrix

`[[1, -c], [-c, 1]]`,

so its covariance matrix is

`(1 / (1 - c^2)) • [[1, c], [c, 1]]`.

For the paper's value `c = sqrt (5 * sqrt 5 - 11) / 2`, the marginal variance
`1 / (1 - c^2)` is strictly greater than one.  Thus the displayed density is
not the density of the standardized Gaussian claimed in the same conjecture.
The corrected density inserts the missing factor `1 / (1 - c^2)` in the
quadratic form in the exponent.

*Reference:* [arXiv:2602.19255](https://arxiv.org/abs/2602.19255), p. 3.
-/

namespace Arxiv.«2602.19255»

noncomputable section

/-- A named copy of `sqrt 5`. -/
def sqrtFive : ℝ := Real.sqrt 5

/-- The square of the correlation claimed in the paper. -/
def correlationSquare : ℝ := (5 * sqrtFive - 11) / 4

/-- The marginal variance of the Gaussian density literally printed in the paper. -/
def printedMarginalVariance : ℝ := 1 / (1 - correlationSquare)

private theorem sqrtFive_nonneg : 0 ≤ sqrtFive := by
  exact Real.sqrt_nonneg 5

private theorem sqrtFive_sq : sqrtFive ^ 2 = 5 := by
  unfold sqrtFive
  simpa using Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)

private theorem sqrtFive_lt_three : sqrtFive < 3 := by
  nlinarith [sqrtFive_sq, sqrtFive_nonneg]

private theorem correlationSquare_pos : 0 < correlationSquare := by
  unfold correlationSquare
  nlinarith [sqrtFive_sq, sqrtFive_nonneg]

private theorem correlationSquare_lt_one : correlationSquare < 1 := by
  unfold correlationSquare
  nlinarith [sqrtFive_lt_three]

private theorem one_sub_correlationSquare_pos : 0 < 1 - correlationSquare := by
  linarith [correlationSquare_lt_one]

/-- The displayed density has marginal variance strictly greater than one. -/
theorem printedMarginalVariance_gt_one : 1 < printedMarginalVariance := by
  unfold printedMarginalVariance
  rw [lt_div_iff₀ one_sub_correlationSquare_pos]
  linarith [correlationSquare_pos]

/--
The density printed in the conjecture cannot be the unit-marginal Gaussian
obtained after coordinatewise standardization.
-/
@[category research solved, AMS 60]
theorem printed_density_not_unit_marginal : printedMarginalVariance ≠ 1 := by
  exact ne_of_gt printedMarginalVariance_gt_one

end

end Arxiv.«2602.19255»
