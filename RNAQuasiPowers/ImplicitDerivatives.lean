import RNAQuasiPowers.Covariance

namespace RNAQuasiPowers

noncomputable section

/-!
# Implicit derivatives of the dominant root

For

`Q(t,s,r) = radicand t (exp s) (exp r)`, 

the functions below are the values at `s = r = 0` of the indicated partial
 derivatives, viewed as polynomials in `t`.  Keeping these derivatives as
explicit polynomials makes the quasi-powers Hessian calculation entirely
algebraic.
-/

/-- `Q_tt(t,0,0)`. -/
def qTTAtOne (t : Real) : Real :=
  30 * t ^ 4 - 80 * t ^ 3 + 48 * t ^ 2 - 12 * t + 8

/-- `Q_s(t,0,0)`, where `x = exp s`. -/
def qSAtOne (t : Real) : Real :=
  2 * t ^ 6 - 4 * t ^ 5 + 4 * t ^ 4 - 2 * t ^ 3

/-- `Q_r(t,0,0)`, where `z = exp r`. -/
def qRAtOne (t : Real) : Real :=
  2 * t ^ 6 - 6 * t ^ 5 + 4 * t ^ 4 + 2 * t ^ 3 - 2 * t ^ 2

/-- `Q_ss(t,0,0)`. -/
def qSSAtOne (t : Real) : Real :=
  4 * t ^ 6 - 4 * t ^ 5 + 4 * t ^ 4 - 2 * t ^ 3

/-- `Q_rr(t,0,0)`. -/
def qRRAtOne (t : Real) : Real :=
  4 * t ^ 6 - 10 * t ^ 5 + 6 * t ^ 4 + 2 * t ^ 3 - 2 * t ^ 2

/-- `Q_sr(t,0,0)`. -/
def qSRAtOne (t : Real) : Real :=
  4 * t ^ 6 - 6 * t ^ 5 + 4 * t ^ 4 - 2 * t ^ 3

/-- `Q_ts(t,0,0)`. -/
def qTSAtOne (t : Real) : Real :=
  12 * t ^ 5 - 20 * t ^ 4 + 16 * t ^ 3 - 6 * t ^ 2

/-- `Q_tr(t,0,0)`. -/
def qTRAtOne (t : Real) : Real :=
  12 * t ^ 5 - 30 * t ^ 4 + 16 * t ^ 3 + 6 * t ^ 2 - 4 * t

/-! Polynomial reductions modulo `t^2 - 3t + 1`. -/

theorem qTTAtOne_reduction (t : Real) :
    qTTAtOne t =
      (30 * t ^ 2 + 10 * t + 48) * (t ^ 2 - 3 * t + 1) + (122 * t - 40) := by
  unfold qTTAtOne
  ring

theorem qSAtOne_reduction (t : Real) :
    qSAtOne t =
      (2 * t ^ 4 + 2 * t ^ 3 + 8 * t ^ 2 + 20 * t + 52) *
          (t ^ 2 - 3 * t + 1) + (136 * t - 52) := by
  unfold qSAtOne
  ring

theorem qRAtOne_reduction (t : Real) :
    qRAtOne t =
      (2 * t ^ 4 + 2 * t ^ 2 + 8 * t + 20) * (t ^ 2 - 3 * t + 1) +
        (52 * t - 20) := by
  unfold qRAtOne
  ring

theorem qSSAtOne_reduction (t : Real) :
    qSSAtOne t =
      (4 * t ^ 4 + 8 * t ^ 3 + 24 * t ^ 2 + 62 * t + 162) *
          (t ^ 2 - 3 * t + 1) + (424 * t - 162) := by
  unfold qSSAtOne
  ring

theorem qRRAtOne_reduction (t : Real) :
    qRRAtOne t =
      (4 * t ^ 4 + 2 * t ^ 3 + 8 * t ^ 2 + 24 * t + 62) *
          (t ^ 2 - 3 * t + 1) + (162 * t - 62) := by
  unfold qRRAtOne
  ring

theorem qSRAtOne_reduction (t : Real) :
    qSRAtOne t =
      (4 * t ^ 4 + 6 * t ^ 3 + 18 * t ^ 2 + 46 * t + 120) *
          (t ^ 2 - 3 * t + 1) + (314 * t - 120) := by
  unfold qSRAtOne
  ring

theorem qTSAtOne_reduction (t : Real) :
    qTSAtOne t =
      (12 * t ^ 3 + 16 * t ^ 2 + 52 * t + 134) *
          (t ^ 2 - 3 * t + 1) + (350 * t - 134) := by
  unfold qTSAtOne
  ring

theorem qTRAtOne_reduction (t : Real) :
    qTRAtOne t =
      (12 * t ^ 3 + 6 * t ^ 2 + 22 * t + 66) *
          (t ^ 2 - 3 * t + 1) + (172 * t - 66) := by
  unfold qTRAtOne
  ring

/-! Exact derivative values at the small root. -/

theorem qTTAtOne_rho : qTTAtOne rho = 143 - 61 * sqrtFive := by
  rw [qTTAtOne_reduction, rho_quadratic]
  unfold rho
  ring

theorem qSAtOne_rho : qSAtOne rho = 152 - 68 * sqrtFive := by
  rw [qSAtOne_reduction, rho_quadratic]
  unfold rho
  ring

theorem qRAtOne_rho : qRAtOne rho = 58 - 26 * sqrtFive := by
  rw [qRAtOne_reduction, rho_quadratic]
  unfold rho
  ring

theorem qSSAtOne_rho : qSSAtOne rho = 474 - 212 * sqrtFive := by
  rw [qSSAtOne_reduction, rho_quadratic]
  unfold rho
  ring

theorem qRRAtOne_rho : qRRAtOne rho = 181 - 81 * sqrtFive := by
  rw [qRRAtOne_reduction, rho_quadratic]
  unfold rho
  ring

theorem qSRAtOne_rho : qSRAtOne rho = 351 - 157 * sqrtFive := by
  rw [qSRAtOne_reduction, rho_quadratic]
  unfold rho
  ring

theorem qTSAtOne_rho : qTSAtOne rho = 391 - 175 * sqrtFive := by
  rw [qTSAtOne_reduction, rho_quadratic]
  unfold rho
  ring

theorem qTRAtOne_rho : qTRAtOne rho = 192 - 86 * sqrtFive := by
  rw [qTRAtOne_reduction, rho_quadratic]
  unfold rho
  ring

/-!
Candidate first and second derivatives of the analytic root branch
`rho(s,r)` at `(0,0)`.
-/

/-- `∂rho/∂s` at the origin. -/
def rhoHairpin : Real := -5 / 2 + 11 * sqrtFive / 10

/-- `∂rho/∂r` at the origin. -/
def rhoBasepair : Real := -1 + 2 * sqrtFive / 5

/-- `∂²rho/∂s²` at the origin. -/
def rhoHairpinHairpin : Real := -1 / 2 + 11 * sqrtFive / 50

/-- `∂²rho/∂r²` at the origin. -/
def rhoBasepairBasepair : Real := 3 / 4 - 33 * sqrtFive / 100

/-- `∂²rho/(∂s∂r)` at the origin. -/
def rhoHairpinBasepair : Real := 1 / 2 - 11 * sqrtFive / 50

/-- First implicit-derivative equation in the hairpin direction. -/
theorem rhoHairpin_implicit_equation :
    dRadicandAtOne rho * rhoHairpin + qSAtOne rho = 0 := by
  rw [dRadicandAtOne_rho, qSAtOne_rho]
  unfold rhoHairpin
  calc
    (30 - 14 * sqrtFive) * (-5 / 2 + 11 * sqrtFive / 10) +
          (152 - 68 * sqrtFive) =
        (-77 / 5 : Real) * (sqrtFive ^ 2 - 5) := by ring
    _ = 0 := by rw [sqrtFive_sq]; ring

/-- First implicit-derivative equation in the basepair direction. -/
theorem rhoBasepair_implicit_equation :
    dRadicandAtOne rho * rhoBasepair + qRAtOne rho = 0 := by
  rw [dRadicandAtOne_rho, qRAtOne_rho]
  unfold rhoBasepair
  calc
    (30 - 14 * sqrtFive) * (-1 + 2 * sqrtFive / 5) +
          (58 - 26 * sqrtFive) =
        (-28 / 5 : Real) * (sqrtFive ^ 2 - 5) := by ring
    _ = 0 := by rw [sqrtFive_sq]; ring

/-- Second implicit-derivative equation in the hairpin direction. -/
theorem rhoHairpinHairpin_implicit_equation :
    qTTAtOne rho * rhoHairpin ^ 2 +
        2 * qTSAtOne rho * rhoHairpin + qSSAtOne rho +
          dRadicandAtOne rho * rhoHairpinHairpin = 0 := by
  rw [qTTAtOne_rho, qTSAtOne_rho, qSSAtOne_rho, dRadicandAtOne_rho]
  unfold rhoHairpin rhoHairpinHairpin
  calc
    (143 - 61 * sqrtFive) * (-5 / 2 + 11 * sqrtFive / 10) ^ 2 +
          2 * (391 - 175 * sqrtFive) * (-5 / 2 + 11 * sqrtFive / 10) +
          (474 - 212 * sqrtFive) +
          (30 - 14 * sqrtFive) * (-1 / 2 + 11 * sqrtFive / 50) =
        (-11 * (671 * sqrtFive - 1095) / 100) *
          (sqrtFive ^ 2 - 5) := by ring
    _ = 0 := by rw [sqrtFive_sq]; ring

/-- Second implicit-derivative equation in the basepair direction. -/
theorem rhoBasepairBasepair_implicit_equation :
    qTTAtOne rho * rhoBasepair ^ 2 +
        2 * qTRAtOne rho * rhoBasepair + qRRAtOne rho +
          dRadicandAtOne rho * rhoBasepairBasepair = 0 := by
  rw [qTTAtOne_rho, qTRAtOne_rho, qRRAtOne_rho, dRadicandAtOne_rho]
  unfold rhoBasepair rhoBasepairBasepair
  calc
    (143 - 61 * sqrtFive) * (-1 + 2 * sqrtFive / 5) ^ 2 +
          2 * (192 - 86 * sqrtFive) * (-1 + 2 * sqrtFive / 5) +
          (181 - 81 * sqrtFive) +
          (30 - 14 * sqrtFive) * (3 / 4 - 33 * sqrtFive / 100) =
        (-(488 * sqrtFive - 375) / 50) * (sqrtFive ^ 2 - 5) := by ring
    _ = 0 := by rw [sqrtFive_sq]; ring

/-- Mixed implicit-derivative equation. -/
theorem rhoHairpinBasepair_implicit_equation :
    qTTAtOne rho * rhoHairpin * rhoBasepair +
        qTSAtOne rho * rhoBasepair + qTRAtOne rho * rhoHairpin +
          qSRAtOne rho + dRadicandAtOne rho * rhoHairpinBasepair = 0 := by
  rw [qTTAtOne_rho, qTSAtOne_rho, qTRAtOne_rho, qSRAtOne_rho,
    dRadicandAtOne_rho]
  unfold rhoHairpin rhoBasepair rhoHairpinBasepair
  calc
    (143 - 61 * sqrtFive) * (-5 / 2 + 11 * sqrtFive / 10) *
          (-1 + 2 * sqrtFive / 5) +
          (391 - 175 * sqrtFive) * (-1 + 2 * sqrtFive / 5) +
          (192 - 86 * sqrtFive) * (-5 / 2 + 11 * sqrtFive / 10) +
          (351 - 157 * sqrtFive) +
          (30 - 14 * sqrtFive) * (1 / 2 - 11 * sqrtFive / 50) =
        (-(1342 * sqrtFive - 1475) / 50) * (sqrtFive ^ 2 - 5) := by ring
    _ = 0 := by rw [sqrtFive_sq]; ring

/-!
The exponent in the quasi-powers moment-generating function is
`u(s,r) = log (rho / rho(s,r))`.  The next identities prove that the proposed
linear means and covariance matrix are exactly its gradient and Hessian at the
origin, assuming the analytic root branch exists.
-/

theorem meanHairpins_rationalized :
    meanHairpins = 1 - 2 * sqrtFive / 5 := by
  unfold meanHairpins
  field_simp [sqrtFive_ne_zero]
  nlinarith [sqrtFive_sq]

theorem meanHairpins_root_identity :
    meanHairpins * rho + rhoHairpin = 0 := by
  rw [meanHairpins_rationalized]
  unfold rho rhoHairpin
  calc
    (1 - 2 * sqrtFive / 5) * ((3 - sqrtFive) / 2) +
          (-5 / 2 + 11 * sqrtFive / 10) =
        (sqrtFive ^ 2 - 5) / 5 := by ring
    _ = 0 := by rw [sqrtFive_sq]; ring

theorem meanBasepairs_root_identity :
    meanBasepairs * rho + rhoBasepair = 0 := by
  unfold meanBasepairs rho rhoBasepair
  calc
    ((5 - sqrtFive) / 10) * ((3 - sqrtFive) / 2) +
          (-1 + 2 * sqrtFive / 5) =
        (sqrtFive ^ 2 - 5) / 20 := by ring
    _ = 0 := by rw [sqrtFive_sq]; ring

theorem varianceHairpins_root_identity :
    varianceHairpins * rho ^ 2 =
      rhoHairpin ^ 2 - rho * rhoHairpinHairpin := by
  apply sub_eq_zero.mp
  calc
    varianceHairpins * rho ^ 2 -
          (rhoHairpin ^ 2 - rho * rhoHairpinHairpin) =
        (-(11 * sqrtFive - 25) / 50) * (sqrtFive ^ 2 - 5) := by
          unfold varianceHairpins rho rhoHairpin rhoHairpinHairpin
          ring
    _ = 0 := by rw [sqrtFive_sq]; ring

theorem varianceBasepairs_root_identity :
    varianceBasepairs * rho ^ 2 =
      rhoBasepair ^ 2 - rho * rhoBasepairBasepair := by
  apply sub_eq_zero.mp
  calc
    varianceBasepairs * rho ^ 2 -
          (rhoBasepair ^ 2 - rho * rhoBasepairBasepair) =
        ((sqrtFive - 5) / 200) * (sqrtFive ^ 2 - 5) := by
          unfold varianceBasepairs rho rhoBasepair rhoBasepairBasepair
          ring
    _ = 0 := by rw [sqrtFive_sq]; ring

theorem covariance_root_identity :
    covarianceHairpinsBasepairs * rho ^ 2 =
      rhoHairpin * rhoBasepair - rho * rhoHairpinBasepair := by
  apply sub_eq_zero.mp
  calc
    covarianceHairpinsBasepairs * rho ^ 2 -
          (rhoHairpin * rhoBasepair - rho * rhoHairpinBasepair) =
        (-(11 * sqrtFive - 25) / 200) * (sqrtFive ^ 2 - 5) := by
          unfold covarianceHairpinsBasepairs rho rhoHairpin rhoBasepair
            rhoHairpinBasepair
          ring
    _ = 0 := by rw [sqrtFive_sq]; ring

/-- The conjunction packaged by `implicit_derivative_certificate`. -/
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
Collected derivative certificate: all five implicit differentiation equations
and all five gradient/Hessian identities required by quasi-powers.
-/
theorem implicit_derivative_certificate : implicitDerivativeConditions := by
  unfold implicitDerivativeConditions
  exact ⟨rhoHairpin_implicit_equation,
    rhoBasepair_implicit_equation,
    rhoHairpinHairpin_implicit_equation,
    rhoBasepairBasepair_implicit_equation,
    rhoHairpinBasepair_implicit_equation,
    meanHairpins_root_identity,
    meanBasepairs_root_identity,
    varianceHairpins_root_identity,
    varianceBasepairs_root_identity,
    covariance_root_identity⟩

end

end RNAQuasiPowers
