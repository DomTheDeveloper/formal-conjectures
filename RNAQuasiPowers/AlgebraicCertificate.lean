import RNAQuasiPowers.ImplicitDerivatives

namespace RNAQuasiPowers

noncomputable section

/--
A theorem collecting the original exact algebraic facts needed by the proposed
quasi-powers proof.  The stronger `quasiPowers_algebraic_certificate` below also
includes the complete first- and second-order implicit-root derivative
certificate.  Neither theorem formalizes the uniform analytic transfer theorem
or the final probability limit theorem.
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

end

end RNAQuasiPowers
