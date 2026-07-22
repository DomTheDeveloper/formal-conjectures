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

import RNAQuasiPowers.DensityCorrection

namespace RNAQuasiPowers

noncomputable section

/-!
# Exact Gaussian precision-matrix correction

For a standardized bivariate Gaussian with correlation `c`, the covariance
matrix has diagonal entries `1` and off-diagonal entries `c`. Its precision
matrix has diagonal entries `1/(1-c²)` and off-diagonal entries
`-c/(1-c²)`.

The density printed in the source paper instead uses precision entries `1` and
`-c`. Its inverse therefore has diagonal `1/(1-c²)`, explaining the marginal
variance defect proved in `DensityCorrection`.
-/

/-- Diagonal entry of the corrected precision matrix. -/
def correctedPrecisionDiagonal (c : Real) : Real := 1 / (1 - c ^ 2)

/-- Off-diagonal entry of the corrected precision matrix. -/
def correctedPrecisionOffDiagonal (c : Real) : Real := -c / (1 - c ^ 2)

/-- Diagonal entry of the inverse of the precision matrix printed in the paper. -/
def printedCovarianceDiagonal (c : Real) : Real := 1 / (1 - c ^ 2)

/-- Off-diagonal entry of the inverse of the precision matrix printed in the paper. -/
def printedCovarianceOffDiagonal (c : Real) : Real := c / (1 - c ^ 2)

/--
The corrected precision entries multiply the unit-variance covariance row
`(1,c)` to `(1,0)`. Symmetry gives the other row automatically.
-/
theorem correctedPrecision_inverse_entries (c : Real) (h : 1 - c ^ 2 ≠ 0) :
    correctedPrecisionDiagonal c + correctedPrecisionOffDiagonal c * c = 1 ∧
      correctedPrecisionDiagonal c * c + correctedPrecisionOffDiagonal c = 0 := by
  unfold correctedPrecisionDiagonal correctedPrecisionOffDiagonal
  constructor
  · field_simp [h] <;> ring
  · field_simp [h] <;> ring

/--
The unscaled precision entries `(1,-c)` printed in the paper invert to
covariance entries `1/(1-c²)` and `c/(1-c²)`.
-/
theorem printedPrecision_inverse_entries (c : Real) (h : 1 - c ^ 2 ≠ 0) :
    printedCovarianceDiagonal c - c * printedCovarianceOffDiagonal c = 1 ∧
      printedCovarianceOffDiagonal c - c * printedCovarianceDiagonal c = 0 := by
  unfold printedCovarianceDiagonal printedCovarianceOffDiagonal
  constructor
  · field_simp [h] <;> ring
  · field_simp [h] <;> ring

/-- The target correlation lies in the nonsingular Gaussian range. -/
theorem one_sub_targetCorrelation_sq_pos : 0 < 1 - targetCorrelation ^ 2 := by
  rw [targetCorrelation_sq]
  exact one_sub_correlationSquare_pos

/-- The corrected target precision matrix inverts the standardized covariance. -/
theorem correctedTargetPrecision_inverse_entries :
    correctedPrecisionDiagonal targetCorrelation +
          correctedPrecisionOffDiagonal targetCorrelation * targetCorrelation = 1 ∧
      correctedPrecisionDiagonal targetCorrelation * targetCorrelation +
          correctedPrecisionOffDiagonal targetCorrelation = 0 := by
  exact correctedPrecision_inverse_entries targetCorrelation
    (ne_of_gt one_sub_targetCorrelation_sq_pos)

/-- The printed target precision matrix has the scaled covariance inverse. -/
theorem printedTargetPrecision_inverse_entries :
    printedCovarianceDiagonal targetCorrelation -
          targetCorrelation * printedCovarianceOffDiagonal targetCorrelation = 1 ∧
      printedCovarianceOffDiagonal targetCorrelation -
          targetCorrelation * printedCovarianceDiagonal targetCorrelation = 0 := by
  exact printedPrecision_inverse_entries targetCorrelation
    (ne_of_gt one_sub_targetCorrelation_sq_pos)

end

end RNAQuasiPowers
