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

import FormalConjectures.Arxiv.«2508.10245».Geode5Proof.RecurrenceStep

/-!
# Coefficient formula for the five-dimensional Geode diagonal

The certificate evaluates

`(5n)!/(n!)^5 * [x^(5n)] (1+x)^(10n+2) J_{n,0}(1+x)`.

This module formalizes that expression and the coefficient-extraction identity
used by the modular evaluator.
-/

namespace Arxiv.«2508.10245».Geode5Proof

open scoped BigOperators

noncomputable section

/-- Substitute `y = 1 + x` into a rational polynomial in `y`. -/
def shiftByOne (p : QYPoly) : Polynomial ℚ :=
  p.comp (Polynomial.X + 1)

/-- The coefficient appearing in the univariate Geode formula. -/
def momentCoefficient (n : ℕ) : ℚ :=
  (((Polynomial.X + 1) ^ (10 * n + 2)) * shiftByOne (qMoment n 0)).coeff (5 * n)

/-- The exact rational form of the diagonal Geode number. -/
def momentGeode (n : ℕ) : ℚ :=
  (Nat.factorial (5 * n) : ℚ) /
      (Nat.factorial n : ℚ) ^ 5 * momentCoefficient n

/-- Coefficient extraction after substituting `y = 1 + x`. -/
theorem shifted_coefficient_eq_sum (p : Polynomial ℚ) (A m : ℕ) :
    (((Polynomial.X + 1) ^ A) * p.comp (Polynomial.X + 1)).coeff m =
      p.sum (fun j a => a * (Nat.choose (A + j) m : ℚ)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.add_comp, mul_add, Polynomial.coeff_add, hp, hq]
      rw [Polynomial.sum_add_index]
      intro n
      simp
  | monomial n a =>
      rw [Polynomial.monomial_comp]
      rw [← mul_assoc, ← Polynomial.C_mul]
      rw [← pow_add]
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_add_one_pow]
      simp [Polynomial.sum_monomial_index]

/-- The finite extraction sum used at the end of the C++ certificate. -/
def extractionSum (n : ℕ) : ℚ :=
  (qMoment n 0).sum fun j a =>
    a * (Nat.choose (10 * n + 2 + j) (5 * n) : ℚ)

theorem momentCoefficient_eq_extractionSum (n : ℕ) :
    momentCoefficient n = extractionSum n := by
  exact shifted_coefficient_eq_sum (qMoment n 0) (10 * n + 2) (5 * n)

#print axioms shifted_coefficient_eq_sum
#print axioms momentCoefficient_eq_extractionSum

end

end Arxiv.«2508.10245».Geode5Proof
