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
# RNA hairpins, basepairs, and quasi-powers certificates

*Reference:* [Bu--Kauers--Zeilberger, arXiv:2602.19255](https://arxiv.org/abs/2602.19255)

This file records three exact results used in the proposed bivariate quasi-powers
analysis of uniformly random RNA secondary structures:

1. the recursive grammar has exactly the radicand displayed in the paper;
2. the dominant-root derivatives give the stated means, covariance matrix, and
   correlation;
3. the Gaussian density printed in the paper is incompatible with the stated
   coordinatewise standardization.

The full parameter-uniform singularity-transfer and multivariate weak-convergence
layer is deliberately outside the scope of these three finite certificates.
-/

namespace Arxiv.«2602.19255»

noncomputable section

/-- The radicand in the marked algebraic generating function. -/
def radicand (t x z : ℝ) : ℝ :=
  t ^ 6 * x ^ 2 * z ^ 2
    - 2 * t ^ 5 * x * z ^ 2
    - 2 * t ^ 5 * x * z
    + 4 * t ^ 4 * x * z
    + t ^ 4 * z ^ 2
    - 2 * t ^ 4 * z
    - 2 * t ^ 3 * x * z
    + t ^ 4
    + 4 * t ^ 3 * z
    - 4 * t ^ 3
    - 2 * t ^ 2 * z
    + 6 * t ^ 2
    - 4 * t
    + 1

/-- Leading coefficient of the cleared grammar equation. -/
def grammarA (t z : ℝ) : ℝ := t ^ 2 * z * (1 - t)

/-- Linear coefficient of the cleared grammar equation. -/
def grammarB (t x z : ℝ) : ℝ :=
  t ^ 2 * z * (x * t - 1) - (1 - t) ^ 2

/-- Constant coefficient of the cleared grammar equation. -/
def grammarC (t : ℝ) : ℝ := 1 - t

/-- Discriminant of the cleared quadratic grammar equation. -/
def grammarDiscriminant (t x z : ℝ) : ℝ :=
  grammarB t x z ^ 2 - 4 * grammarA t z * grammarC t

/--
The recursive decomposition of RNA secondary structures yields exactly the
radicand displayed in arXiv:2602.19255.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at
    "https://github.com/DomTheDeveloper/formal-conjectures/tree/8c0e4b0149049e177dd111993a57e4e9ffe51846/RNAQuasiPowers"]
theorem grammar_discriminant_eq_radicand (t x z : ℝ) :
    grammarDiscriminant t x z = radicand t x z := by
  sorry

/-- A named copy of `sqrt 5`. -/
def sqrtFive : ℝ := Real.sqrt 5

/-- The small positive root of `t² - 3t + 1`. -/
def rho : ℝ := (3 - sqrtFive) / 2

/-- Formal `t`-derivative of `radicand t 1 1`. -/
def dRadicandAtOne (t : ℝ) : ℝ :=
  6 * t ^ 5 - 20 * t ^ 4 + 16 * t ^ 3 - 6 * t ^ 2 + 8 * t - 4

/-- Linear coefficient of the expected number of hairpins. -/
def meanHairpins : ℝ := 1 - 2 / sqrtFive

/-- Linear coefficient of the expected number of basepairs. -/
def meanBasepairs : ℝ := (5 - sqrtFive) / 10

/-- Linear coefficient of the hairpin variance. -/
def varianceHairpins : ℝ := (50 - 22 * sqrtFive) / 25

/-- Linear coefficient of the basepair variance. -/
def varianceBasepairs : ℝ := sqrtFive / 50

/-- Linear coefficient of the hairpin/basepair covariance. -/
def covarianceHairpinsBasepairs : ℝ := (25 - 11 * sqrtFive) / 50

/-- Determinant of the limiting covariance matrix. -/
def covarianceDeterminant : ℝ :=
  varianceHairpins * varianceBasepairs - covarianceHairpinsBasepairs ^ 2

/-- Correlation computed from the covariance entries. -/
def normalizedCorrelation : ℝ :=
  covarianceHairpinsBasepairs /
    Real.sqrt (varianceHairpins * varianceBasepairs)

/-- Closed form of the correlation. -/
def targetCorrelation : ℝ := Real.sqrt (5 * sqrtFive - 11) / 2

/-- Values of the relevant marked derivatives at the unmarked point. -/
def qTTAtOne (t : ℝ) : ℝ :=
  30 * t ^ 4 - 80 * t ^ 3 + 48 * t ^ 2 - 12 * t + 8

def qSAtOne (t : ℝ) : ℝ :=
  2 * t ^ 6 - 4 * t ^ 5 + 4 * t ^ 4 - 2 * t ^ 3

def qRAtOne (t : ℝ) : ℝ :=
  2 * t ^ 6 - 6 * t ^ 5 + 4 * t ^ 4 + 2 * t ^ 3 - 2 * t ^ 2

def qSSAtOne (t : ℝ) : ℝ :=
  4 * t ^ 6 - 4 * t ^ 5 + 4 * t ^ 4 - 2 * t ^ 3

def qRRAtOne (t : ℝ) : ℝ :=
  4 * t ^ 6 - 10 * t ^ 5 + 6 * t ^ 4 + 2 * t ^ 3 - 2 * t ^ 2

def qSRAtOne (t : ℝ) : ℝ :=
  4 * t ^ 6 - 6 * t ^ 5 + 4 * t ^ 4 - 2 * t ^ 3

def qTSAtOne (t : ℝ) : ℝ :=
  12 * t ^ 5 - 20 * t ^ 4 + 16 * t ^ 3 - 6 * t ^ 2

def qTRAtOne (t : ℝ) : ℝ :=
  12 * t ^ 5 - 30 * t ^ 4 + 16 * t ^ 3 + 6 * t ^ 2 - 4 * t

/-- Candidate derivatives of the analytic dominant-root branch. -/
def rhoHairpin : ℝ := -5 / 2 + 11 * sqrtFive / 10
def rhoBasepair : ℝ := -1 + 2 * sqrtFive / 5
def rhoHairpinHairpin : ℝ := -1 / 2 + 11 * sqrtFive / 50
def rhoBasepairBasepair : ℝ := 3 / 4 - 33 * sqrtFive / 100
def rhoHairpinBasepair : ℝ := 1 / 2 - 11 * sqrtFive / 50

/-- The ten exact implicit-differentiation and Hessian identities. -/
def implicitDerivativeConditions : Prop :=
  (dRadicandAtOne rho * rhoHairpin + qSAtOne rho = 0) ∧
  (dRadicandAtOne rho * rhoBasepair + qRAtOne rho = 0) ∧
  (qTTAtOne rho * rhoHairpin ^ 2 +
      2 * qTSAtOne rho * rhoHairpin + qSSAtOne rho +
        dRadicandAtOne rho * rhoHairpinHairpin = 0) ∧
  (qTTAtOne rho * rhoBasepair ^ 2 +
      2 * qTRAtOne rho * rhoBasepair + qRRAtOne rho +
        dRadicandAtOne rho * rhoBasepairBasepair = 0) ∧
  (qTTAtOne rho * rhoHairpin * rhoBasepair +
      qTSAtOne rho * rhoBasepair + qTRAtOne rho * rhoHairpin +
        qSRAtOne rho + dRadicandAtOne rho * rhoHairpinBasepair = 0) ∧
  (meanHairpins * rho + rhoHairpin = 0) ∧
  (meanBasepairs * rho + rhoBasepair = 0) ∧
  (varianceHairpins * rho ^ 2 =
      rhoHairpin ^ 2 - rho * rhoHairpinHairpin) ∧
  (varianceBasepairs * rho ^ 2 =
      rhoBasepair ^ 2 - rho * rhoBasepairBasepair) ∧
  (covarianceHairpinsBasepairs * rho ^ 2 =
      rhoHairpin * rhoBasepair - rho * rhoHairpinBasepair)

/--
All model-specific algebraic inputs required by the quasi-powers calculation:
the simple dominant root, exact first and second derivatives, positive-definite
covariance matrix, and closed-form correlation.
-/
@[category research solved, AMS 5 60,
  formal_proof using lean4 at
    "https://github.com/DomTheDeveloper/formal-conjectures/tree/8c0e4b0149049e177dd111993a57e4e9ffe51846/RNAQuasiPowers"]
theorem quasiPowers_algebraic_certificate :
    radicand rho 1 1 = 0 ∧
    dRadicandAtOne rho ≠ 0 ∧
    0 < rho ∧ rho < 1 ∧
    0 < varianceHairpins ∧
    0 < varianceBasepairs ∧
    0 < covarianceDeterminant ∧
    normalizedCorrelation = targetCorrelation ∧
    implicitDerivativeConditions := by
  sorry

/-- Marginal variance produced by the density printed in the paper. -/
def printedMarginalVariance (c : ℝ) : ℝ := 1 / (1 - c ^ 2)

/--
The paper's displayed Gaussian density is not compatible with its exact
coordinatewise standardization: at the claimed correlation its marginal
variance is strictly greater than one.
-/
@[category research solved, AMS 60,
  formal_proof using lean4 at
    "https://github.com/DomTheDeveloper/formal-conjectures/tree/8c0e4b0149049e177dd111993a57e4e9ffe51846/RNAQuasiPowers"]
theorem printed_density_not_standardized :
    1 < printedMarginalVariance targetCorrelation := by
  sorry

end

end Arxiv.«2602.19255»
