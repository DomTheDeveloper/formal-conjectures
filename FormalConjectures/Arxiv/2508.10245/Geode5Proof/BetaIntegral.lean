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

import FormalConjectures.Arxiv.«2508.10245».Geode5Proof.Recurrence
import FormalConjectures.Arxiv.«2508.10245».Geode5Proof.ReducedSum

/-!
# Algebraic beta integral for the Geode reduction

No analytic integration theory is needed.  The coefficientwise polynomial
integral and its fundamental theorem give the beta identity by induction and
integration by parts.
-/

namespace Arxiv.«2508.10245».Geode5Proof

noncomputable section

/-- The algebraic integral of `t^r (1-t)^n`. -/
def qBetaIntegral (r n : ℕ) : QYPoly :=
  integral01 (qt ^ r * (1 - qt) ^ n)

/-- Base case of the beta integral. -/
theorem qBetaIntegral_zero (r : ℕ) :
    qBetaIntegral r 0 = Polynomial.C ((r + 1 : ℚ)⁻¹) := by
  simp [qBetaIntegral, qt, integral01_monomial,
    Polynomial.X_pow_eq_monomial]

/-- Integration-by-parts recurrence for the beta integral. -/
theorem qBetaIntegral_succ (r n : ℕ) :
    (r + 1 : QYPoly) * qBetaIntegral r (n + 1) =
      (n + 1 : QYPoly) * qBetaIntegral (r + 1) n := by
  have hboundary :
      integral01 ((qt ^ (r + 1) * (1 - qt) ^ (n + 1)).derivative) = 0 := by
    rw [integral01_derivative]
    simp [qt, Polynomial.eval_mul]
  have hderiv :
      (qt ^ (r + 1) * (1 - qt) ^ (n + 1)).derivative =
        Polynomial.C (r + 1 : QYPoly) *
            (qt ^ r * (1 - qt) ^ (n + 1)) -
          Polynomial.C (n + 1 : QYPoly) *
            (qt ^ (r + 1) * (1 - qt) ^ n) := by
    rw [Polynomial.derivative_mul, Polynomial.derivative_X_pow,
      Polynomial.derivative_pow_succ]
    simp [qt]
    ring
  rw [hderiv] at hboundary
  simp only [map_sub, ← Polynomial.smul_eq_C_mul, map_smul,
    smul_eq_mul, qBetaIntegral] at hboundary
  linear_combination hboundary

/-- The exact factorial beta identity. -/
theorem qBetaIntegral_eq_factorial (r n : ℕ) :
    qBetaIntegral r n =
      Polynomial.C
        (qFactorial r * qFactorial n / qFactorial (r + n + 1)) := by
  induction n generalizing r with
  | zero =>
      rw [qBetaIntegral_zero]
      simp [qFactorial, Nat.factorial_succ]
  | succ n ih =>
      have hrec := qBetaIntegral_succ r n
      rw [ih (r + 1)] at hrec
      have hr : (r + 1 : QYPoly) ≠ 0 := by norm_num
      apply (mul_left_cancel₀ hr)
      rw [hrec]
      simp only [← Polynomial.C_mul]
      congr 1
      simp [qFactorial, Nat.factorial_succ]
      field_simp
      ring

#print axioms qBetaIntegral_succ
#print axioms qBetaIntegral_eq_factorial

end

end Arxiv.«2508.10245».Geode5Proof
