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
import RNAQuasiPowers.ImplicitDerivatives

namespace RNAQuasiPowers

noncomputable section

/--
A theorem collecting the original exact algebraic facts needed by the proposed
quasi-powers proof. The stronger certificates below also include the complete
first- and second-order implicit-root derivative certificate and the correction
to the displayed Gaussian density. None of these theorems formalizes the
uniform analytic transfer theorem or the final probability limit theorem.
-/
theorem algebraic_certificate :
    And (radicand rho 1 1 = 0)
      (And (Not (dRadicandAtOne rho = 0))
        (And (0 < rho)
          (And (rho < 1)
            (And (0 < varianceHairpins)
              (And (0 < varianceBasepairs)
                (And (0 < covarianceDeterminant)
                  (normalizedCorrelation = targetCorrelation))))))) := by
  exact And.intro radicand_rho
    (And.intro dRadicandAtOne_rho_ne_zero
      (And.intro rho_pos
        (And.intro rho_lt_one
          (And.intro varianceHairpins_pos
            (And.intro varianceBasepairs_pos
              (And.intro covarianceDeterminant_pos
                normalizedCorrelation_eq_target))))))

/--
The strengthened algebraic core: the original root/covariance certificate plus
all implicit first- and second-derivative identities.
-/
theorem quasiPowers_algebraic_certificate :
    (And (radicand rho 1 1 = 0)
      (And (Not (dRadicandAtOne rho = 0))
        (And (0 < rho)
          (And (rho < 1)
            (And (0 < varianceHairpins)
              (And (0 < varianceBasepairs)
                (And (0 < covarianceDeterminant)
                  (normalizedCorrelation = targetCorrelation)))))))) ∧
      implicitDerivativeConditions := by
  exact ⟨algebraic_certificate, implicit_derivative_certificate⟩

/--
The complete finite certificate used by the three solution tracks: algebraic
quasi-powers data, implicit derivatives, and incompatibility of the printed
density with exact unit-variance standardization.
-/
theorem threeTrack_certificate :
    ((And (radicand rho 1 1 = 0)
      (And (Not (dRadicandAtOne rho = 0))
        (And (0 < rho)
          (And (rho < 1)
            (And (0 < varianceHairpins)
              (And (0 < varianceBasepairs)
                (And (0 < covarianceDeterminant)
                  (normalizedCorrelation = targetCorrelation)))))))) ∧
      implicitDerivativeConditions) ∧
      printedMarginalVariance ≠ 1 := by
  exact ⟨quasiPowers_algebraic_certificate, printedMarginalVariance_ne_one⟩

end

end RNAQuasiPowers
