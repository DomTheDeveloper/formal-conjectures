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

import FormalConjectures.Util.ProblemImports
import RNAQuasiPowers

/-!
# RNA hairpins, basepairs, and quasi-powers certificates

*Reference:* [Bu--Kauers--Zeilberger, arXiv:2602.19255](https://arxiv.org/abs/2602.19255)

This file exposes three sorry-free, kernel-checkable results from the marked
RNA secondary-structure model:

1. the recursive grammar has exactly the radicand displayed in the paper;
2. the dominant-root calculation satisfies all first- and second-order
   implicit-derivative identities and gives a positive-definite covariance
   matrix with the claimed correlation;
3. the Gaussian density printed in the paper is incompatible with exact
   coordinatewise standardization, and the corrected precision entries invert
   the intended unit-variance covariance entries.

The final parameter-uniform singularity-transfer and multivariate
weak-convergence layer is not asserted here.
-/

namespace Arxiv.«2602.19255»

noncomputable section

/- ## Grammar and generating-function certificate -/

abbrev radicand := RNAQuasiPowers.radicand
abbrev grammarA := RNAQuasiPowers.grammarA
abbrev grammarB := RNAQuasiPowers.grammarB
abbrev grammarC := RNAQuasiPowers.grammarC
abbrev grammarDiscriminant := RNAQuasiPowers.grammarDiscriminant

/-- The RNA grammar gives exactly the radicand displayed in the paper. -/
@[category research solved, AMS 5]
theorem grammar_discriminant_eq_radicand (t x z : ℝ) :
    grammarDiscriminant t x z = radicand t x z := by
  exact RNAQuasiPowers.grammar_discriminant_eq_radicand t x z

/- ## Dominant-root and covariance certificate -/

abbrev sqrtFive := RNAQuasiPowers.sqrtFive
abbrev rho := RNAQuasiPowers.rho
abbrev dRadicandAtOne := RNAQuasiPowers.dRadicandAtOne
abbrev meanHairpins := RNAQuasiPowers.meanHairpins
abbrev meanBasepairs := RNAQuasiPowers.meanBasepairs
abbrev varianceHairpins := RNAQuasiPowers.varianceHairpins
abbrev varianceBasepairs := RNAQuasiPowers.varianceBasepairs
abbrev covarianceHairpinsBasepairs := RNAQuasiPowers.covarianceHairpinsBasepairs
abbrev covarianceDeterminant := RNAQuasiPowers.covarianceDeterminant
abbrev normalizedCorrelation := RNAQuasiPowers.normalizedCorrelation
abbrev targetCorrelation := RNAQuasiPowers.targetCorrelation
abbrev qTTAtOne := RNAQuasiPowers.qTTAtOne
abbrev qSAtOne := RNAQuasiPowers.qSAtOne
abbrev qRAtOne := RNAQuasiPowers.qRAtOne
abbrev qSSAtOne := RNAQuasiPowers.qSSAtOne
abbrev qRRAtOne := RNAQuasiPowers.qRRAtOne
abbrev qSRAtOne := RNAQuasiPowers.qSRAtOne
abbrev qTSAtOne := RNAQuasiPowers.qTSAtOne
abbrev qTRAtOne := RNAQuasiPowers.qTRAtOne
abbrev rhoHairpin := RNAQuasiPowers.rhoHairpin
abbrev rhoBasepair := RNAQuasiPowers.rhoBasepair
abbrev rhoHairpinHairpin := RNAQuasiPowers.rhoHairpinHairpin
abbrev rhoBasepairBasepair := RNAQuasiPowers.rhoBasepairBasepair
abbrev rhoHairpinBasepair := RNAQuasiPowers.rhoHairpinBasepair
abbrev implicitDerivativeConditions := RNAQuasiPowers.implicitDerivativeConditions

/--
All model-specific algebraic inputs required after the analytic
implicit-function and transfer theorems: a simple dominant root, all ten
implicit-gradient/Hessian identities, a positive-definite covariance matrix,
and the exact closed-form correlation.
-/
@[category research solved, AMS 5 60]
theorem quasiPowers_algebraic_certificate :
    radicand rho 1 1 = 0 ∧
    dRadicandAtOne rho ≠ 0 ∧
    0 < rho ∧ rho < 1 ∧
    0 < varianceHairpins ∧
    0 < varianceBasepairs ∧
    0 < covarianceDeterminant ∧
    normalizedCorrelation = targetCorrelation ∧
    implicitDerivativeConditions := by
  rcases RNAQuasiPowers.quasiPowers_algebraic_certificate with ⟨hAlg, hDeriv⟩
  rcases hAlg with ⟨hroot, hsimple, hrhoPos, hrhoLtOne, hvarH, hvarB, hdet, hcorr⟩
  exact ⟨hroot, hsimple, hrhoPos, hrhoLtOne, hvarH, hvarB, hdet, hcorr, hDeriv⟩

/- ## Printed-density correction -/

abbrev printedMarginalVariance := RNAQuasiPowers.printedMarginalVarianceAt
abbrev correctedPrecisionDiagonal := RNAQuasiPowers.correctedPrecisionDiagonal
abbrev correctedPrecisionOffDiagonal := RNAQuasiPowers.correctedPrecisionOffDiagonal
abbrev printedCovarianceDiagonal := RNAQuasiPowers.printedCovarianceDiagonal
abbrev printedCovarianceOffDiagonal := RNAQuasiPowers.printedCovarianceOffDiagonal

/--
At the claimed correlation, the density printed in the paper has marginal
variance strictly greater than one, so it cannot be the limit after exact
coordinatewise standardization.
-/
@[category research solved, AMS 60]
theorem printed_density_not_standardized :
    1 < printedMarginalVariance targetCorrelation := by
  exact RNAQuasiPowers.printedMarginalVarianceAt_target_gt_one

/--
The corrected target precision entries invert the intended unit-variance
covariance entries, while the printed precision entries invert to the scaled
covariance with marginal variance `1/(1-c²)`.
-/
@[category research solved, AMS 60]
theorem gaussian_precision_correction :
    (correctedPrecisionDiagonal targetCorrelation +
          correctedPrecisionOffDiagonal targetCorrelation * targetCorrelation = 1 ∧
      correctedPrecisionDiagonal targetCorrelation * targetCorrelation +
          correctedPrecisionOffDiagonal targetCorrelation = 0) ∧
    (printedCovarianceDiagonal targetCorrelation -
          targetCorrelation * printedCovarianceOffDiagonal targetCorrelation = 1 ∧
      printedCovarianceOffDiagonal targetCorrelation -
          targetCorrelation * printedCovarianceDiagonal targetCorrelation = 0) ∧
    1 < printedMarginalVariance targetCorrelation := by
  exact ⟨RNAQuasiPowers.correctedTargetPrecision_inverse_entries,
    RNAQuasiPowers.printedTargetPrecision_inverse_entries,
    RNAQuasiPowers.printedMarginalVarianceAt_target_gt_one⟩

/-- A single public theorem collecting all three finite certificates. -/
@[category research solved, AMS 5 60]
theorem three_track_certificate :
    (∀ t x z : ℝ, grammarDiscriminant t x z = radicand t x z) ∧
    (radicand rho 1 1 = 0 ∧
      dRadicandAtOne rho ≠ 0 ∧
      0 < rho ∧ rho < 1 ∧
      0 < varianceHairpins ∧
      0 < varianceBasepairs ∧
      0 < covarianceDeterminant ∧
      normalizedCorrelation = targetCorrelation ∧
      implicitDerivativeConditions) ∧
    1 < printedMarginalVariance targetCorrelation := by
  exact ⟨grammar_discriminant_eq_radicand,
    quasiPowers_algebraic_certificate,
    printed_density_not_standardized⟩

end

end Arxiv.«2602.19255»
