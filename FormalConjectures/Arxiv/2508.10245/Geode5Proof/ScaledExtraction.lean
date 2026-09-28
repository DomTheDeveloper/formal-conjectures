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

import FormalConjectures.Arxiv.«2508.10245».Geode5Proof.ScaledRecurrenceCorrect
import FormalConjectures.Arxiv.«2508.10245».Geode5Proof.MomentToReduced

/-!
# Integer-scaled final coefficient extraction

The common moment denominator and the factorial denominator are cleared at the
end.  The result is an exact equality in `ℤ`, suitable for reduction modulo any
certificate prime.
-/

namespace Arxiv.«2508.10245».Geode5Proof

noncomputable section

/-- Weighted coefficient extraction from an integer polynomial. -/
def zWeightedExtraction (n : ℕ) (p : ZYPoly) : ℤ :=
  p.sum fun j a => a * (Nat.choose (10 * n + 2 + j) (5 * n) : ℤ)

/-- Weighted coefficient extraction from a rational polynomial. -/
def qWeightedExtraction (n : ℕ) (p : QYPoly) : ℚ :=
  p.sum fun j a => a * (Nat.choose (10 * n + 2 + j) (5 * n) : ℚ)

/-- Final integer extraction from the scaled zero-th moment. -/
def zScaledExtraction (n : ℕ) : ℤ :=
  zWeightedExtraction n (zScaledMoment n 0)

/-- Coefficientwise casting commutes with weighted extraction. -/
theorem cast_zWeightedExtraction (n : ℕ) (p : ZYPoly) :
    (zWeightedExtraction n p : ℚ) =
      qWeightedExtraction n (castZY p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp [zWeightedExtraction, qWeightedExtraction, castZY, hp, hq,
        Polynomial.sum_add_index]
  | monomial k a =>
      simp [zWeightedExtraction, qWeightedExtraction, castZY,
        Polynomial.sum_monomial_index]

/-- Weighted extraction is linear under multiplication by a rational constant. -/
theorem qWeightedExtraction_const_mul (n : ℕ) (c : ℚ) (p : QYPoly) :
    qWeightedExtraction n (Polynomial.C c * p) =
      c * qWeightedExtraction n p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp [qWeightedExtraction, mul_add, hp, hq,
        Polynomial.sum_add_index]
      ring
  | monomial k a =>
      simp [qWeightedExtraction, Polynomial.sum_monomial_index]
      ring

/-- The scaled extraction is the common denominator times the rational extraction. -/
theorem cast_zScaledExtraction (n : ℕ) :
    (zScaledExtraction n : ℚ) =
      (scaledDenominator n : ℚ) * extractionSum n := by
  unfold zScaledExtraction
  rw [cast_zWeightedExtraction]
  rw [castZY_zScaledMoment n 0 (by omega)]
  change qWeightedExtraction n
      (Polynomial.C (scaledDenominator n : ℚ) * qMoment n 0) = _
  rw [qWeightedExtraction_const_mul]
  rfl

/-- Exact integer identity underlying every modular certificate computation. -/
theorem geode5_scaled_extraction_identity (n : ℕ) :
    geode5Diagonal n *
        (scaledDenominator n * Nat.factorial n ^ 5 : ℕ) =
      (Nat.factorial (5 * n) : ℤ) * zScaledExtraction n := by
  have hg := cast_geode5Diagonal_eq_momentGeode n
  rw [momentGeode, momentCoefficient_eq_extractionSum] at hg
  have he := cast_zScaledExtraction n
  have hnfac : (Nat.factorial n : ℚ) ≠ 0 := by positivity
  have hD : (scaledDenominator n : ℚ) ≠ 0 := by
    positivity
  have hq :
      (geode5Diagonal n : ℚ) *
          ((scaledDenominator n : ℚ) * (Nat.factorial n : ℚ) ^ 5) =
        (Nat.factorial (5 * n) : ℚ) *
          (zScaledExtraction n : ℚ) := by
    rw [hg, he]
    field_simp [qFactorial, hnfac, hD]
    ring
  exact_mod_cast hq

#print axioms cast_zScaledExtraction
#print axioms geode5_scaled_extraction_identity

end

end Arxiv.«2508.10245».Geode5Proof
