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

import RNAQuasiPowers.GoldenRoot

namespace RNAQuasiPowers

noncomputable section

/-- Linear coefficient of the expected number of hairpins. -/
def meanHairpins : Real := 1 - 2 / sqrtFive

/-- Linear coefficient of the expected number of basepairs. -/
def meanBasepairs : Real := (5 - sqrtFive) / 10

/--
Linear coefficient of the hairpin variance, in a denominator-free form
convenient for exact algebra.
-/
def varianceHairpins : Real := (50 - 22 * sqrtFive) / 25

/-- Linear coefficient of the basepair variance, rationalized. -/
def varianceBasepairs : Real := sqrtFive / 50

/-- Linear coefficient of the covariance. -/
def covarianceHairpinsBasepairs : Real := (25 - 11 * sqrtFive) / 50

/-- Determinant of the limiting covariance matrix. -/
def covarianceDeterminant : Real :=
  varianceHairpins * varianceBasepairs - covarianceHairpinsBasepairs ^ 2

/-- The square of the claimed limiting correlation. -/
def correlationSquare : Real := (5 * sqrtFive - 11) / 4

/-- Correlation computed directly from the covariance entries. -/
def normalizedCorrelation : Real :=
  covarianceHairpinsBasepairs /
    Real.sqrt (varianceHairpins * varianceBasepairs)

/-- The closed form displayed in the OEIS-linked conjecture. -/
def targetCorrelation : Real := Real.sqrt (5 * sqrtFive - 11) / 2

theorem sqrtFive_ne_zero : Not (sqrtFive = 0) := ne_of_gt sqrtFive_pos

/-- The denominator-free variance agrees with the form in the paper. -/
theorem varianceHairpins_paper_form :
    varianceHairpins = 2 - 22 / (5 * sqrtFive) := by
  unfold varianceHairpins
  field_simp [sqrtFive_ne_zero]
  nlinarith [sqrtFive_sq]

/-- The rationalized basepair variance agrees with the form in the paper. -/
theorem varianceBasepairs_paper_form :
    varianceBasepairs = 1 / (10 * sqrtFive) := by
  unfold varianceBasepairs
  field_simp [sqrtFive_ne_zero]
  nlinarith [sqrtFive_sq]

theorem sqrtFive_lt_twentyFive_div_eleven :
    sqrtFive < (25 : Real) / 11 := by
  nlinarith [sqrtFive_sq, sqrtFive_nonneg]

theorem twentyNine_div_thirteen_lt_sqrtFive :
    (29 : Real) / 13 < sqrtFive := by
  nlinarith [sqrtFive_sq, sqrtFive_nonneg]

theorem varianceHairpins_pos : 0 < varianceHairpins := by
  unfold varianceHairpins
  nlinarith [sqrtFive_lt_twentyFive_div_eleven]

theorem varianceBasepairs_pos : 0 < varianceBasepairs := by
  unfold varianceBasepairs
  linarith [sqrtFive_pos]

theorem covarianceHairpinsBasepairs_pos :
    0 < covarianceHairpinsBasepairs := by
  unfold covarianceHairpinsBasepairs
  nlinarith [sqrtFive_lt_twentyFive_div_eleven]

theorem covarianceProduct_pos :
    0 < varianceHairpins * varianceBasepairs :=
  mul_pos varianceHairpins_pos varianceBasepairs_pos

/-- Exact simplification of the covariance determinant. -/
theorem covarianceDeterminant_eq :
    covarianceDeterminant = (13 * sqrtFive - 29) / 50 := by
  apply sub_eq_zero.mp
  calc
    covarianceDeterminant - (13 * sqrtFive - 29) / 50 =
        -33 * (sqrtFive ^ 2 - 5) / 500 := by
          unfold covarianceDeterminant varianceHairpins varianceBasepairs
            covarianceHairpinsBasepairs
          ring
    _ = 0 := by
      rw [sqrtFive_sq]
      ring

/-- The limiting covariance matrix is nonsingular and positive definite. -/
theorem covarianceDeterminant_pos : 0 < covarianceDeterminant := by
  rw [covarianceDeterminant_eq]
  nlinarith [twentyNine_div_thirteen_lt_sqrtFive]

theorem correlationNumerator_pos : 0 < 5 * sqrtFive - 11 := by
  nlinarith [sqrtFive_sq, sqrtFive_nonneg]

/--
The algebraic identity behind the correlation calculation.  It avoids square
roots and is the most stable form for formal verification.
-/
theorem covariance_square_identity :
    covarianceHairpinsBasepairs ^ 2 =
      correlationSquare * (varianceHairpins * varianceBasepairs) := by
  apply sub_eq_zero.mp
  calc
    covarianceHairpinsBasepairs ^ 2 -
          correlationSquare * (varianceHairpins * varianceBasepairs) =
        (11 * sqrtFive - 25) * (sqrtFive ^ 2 - 5) / 500 := by
          unfold covarianceHairpinsBasepairs correlationSquare
            varianceHairpins varianceBasepairs
          ring
    _ = 0 := by
      rw [sqrtFive_sq]
      ring

theorem normalizedCorrelation_sq :
    normalizedCorrelation ^ 2 = correlationSquare := by
  have hsqrt :
      Real.sqrt (varianceHairpins * varianceBasepairs) ^ 2 =
        varianceHairpins * varianceBasepairs :=
    Real.sq_sqrt (le_of_lt covarianceProduct_pos)
  unfold normalizedCorrelation
  rw [div_pow, hsqrt]
  exact (div_eq_iff (ne_of_gt covarianceProduct_pos)).2 covariance_square_identity

theorem targetCorrelation_sq :
    targetCorrelation ^ 2 = correlationSquare := by
  have hnonneg : 0 <= 5 * sqrtFive - 11 :=
    le_of_lt correlationNumerator_pos
  unfold targetCorrelation correlationSquare
  rw [div_pow, Real.sq_sqrt hnonneg]
  ring

theorem normalizedCorrelation_nonneg : 0 <= normalizedCorrelation := by
  unfold normalizedCorrelation
  exact le_of_lt
    (div_pos covarianceHairpinsBasepairs_pos
      (Real.sqrt_pos.2 covarianceProduct_pos))

theorem targetCorrelation_nonneg : 0 <= targetCorrelation := by
  unfold targetCorrelation
  exact le_of_lt
    (div_pos (Real.sqrt_pos.2 correlationNumerator_pos) (by norm_num))

/-- The normalized covariance equals `sqrt(5*sqrt(5)-11)/2`. -/
theorem normalizedCorrelation_eq_target :
    normalizedCorrelation = targetCorrelation := by
  nlinarith [normalizedCorrelation_sq, targetCorrelation_sq,
    normalizedCorrelation_nonneg, targetCorrelation_nonneg]

end

end RNAQuasiPowers
