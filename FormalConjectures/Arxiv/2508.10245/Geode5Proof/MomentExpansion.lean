/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Arxiv.«2508.10245».Geode5Proof.KernelExpansion

/-!
# Explicit finite expansion of the zero-th Geode moment

Each four-index term is reduced to a scalar polynomial in `y` times the beta
integral.  This is the exact algebraic form used in the ZIP derivation.
-/

namespace Arxiv.«2508.10245».Geode5Proof

open scoped BigOperators

noncomputable section

/-- Sum of the four binomial indices. -/
def fourIndexSum (a b c d : ℕ) : ℕ := a + b + c + d

/-- Weighted sum of the four binomial indices. -/
def fourIndexWeight (a b c d : ℕ) : ℕ := a + 2 * b + 3 * c + 4 * d

/-- Scalar coefficient polynomial of one expanded moment term. -/
def qMomentTermCoefficient (n a b c d : ℕ) : QYPoly :=
  (-1 : QYPoly) ^ fourIndexSum a b c d *
    (Nat.choose n a : QYPoly) * (Nat.choose n b : QYPoly) *
    (Nat.choose n c : QYPoly) * (Nat.choose n d : QYPoly) *
    qy ^ (10 * n - fourIndexWeight a b c d)

/-- The integrated value of one expanded four-index term. -/
def qMomentExpandedTerm (n a b c d : ℕ) : QYPoly :=
  qMomentTermCoefficient n a b c d *
    Polynomial.C
      (qFactorial (fourIndexSum a b c d) * qFactorial n /
        qFactorial (n + fourIndexSum a b c d + 1))

/-- Full finite expansion of `J_{n,0}(y)`. -/
def qMomentExpanded (n : ℕ) : QYPoly :=
  ∑ a ∈ Finset.range (n + 1),
    ∑ b ∈ Finset.range (n + 1),
      ∑ c ∈ Finset.range (n + 1),
        ∑ d ∈ Finset.range (n + 1),
          qMomentExpandedTerm n a b c d

/-- The product of four factor terms has the collected `t` and `y` exponents. -/
theorem qFactorTerm_product_eq (n a b c d : ℕ)
    (ha : a ≤ n) (hb : b ≤ n) (hc : c ≤ n) (hd : d ≤ n) :
    qFactorTerm 1 n a * qFactorTerm 2 n b *
        qFactorTerm 3 n c * qFactorTerm 4 n d =
      Polynomial.C (qMomentTermCoefficient n a b c d) *
        qt ^ fourIndexSum a b c d := by
  have hy :
      (n - a) + 2 * (n - b) + 3 * (n - c) + 4 * (n - d) =
        10 * n - fourIndexWeight a b c d := by
    simp [fourIndexWeight]
    omega
  have ht :
      qt ^ a * qt ^ b * qt ^ c * qt ^ d =
        qt ^ fourIndexSum a b c d := by
    simp [fourIndexSum, pow_add]
  have hs :
      (-1 : QYPoly) ^ a * (-1 : QYPoly) ^ b *
          (-1 : QYPoly) ^ c * (-1 : QYPoly) ^ d =
        (-1 : QYPoly) ^ fourIndexSum a b c d := by
    simp [fourIndexSum, pow_add]
  simp only [qFactorTerm]
  rw [← Polynomial.C_mul, ← Polynomial.C_mul, ← Polynomial.C_mul]
  simp only [Polynomial.C_inj]
  rw [ht, hs]
  simp only [qMomentTermCoefficient]
  have hypow :
      qy ^ (n - a) * qy ^ (2 * (n - b)) *
          qy ^ (3 * (n - c)) * qy ^ (4 * (n - d)) =
        qy ^ (10 * n - fourIndexWeight a b c d) := by
    rw [← pow_add, ← pow_add, ← pow_add, hy]
  simp [hypow]
  ring

/-- Integral of one expanded kernel term. -/
theorem integral01_expanded_kernel_term (n a b c d : ℕ)
    (ha : a ≤ n) (hb : b ≤ n) (hc : c ≤ n) (hd : d ≤ n) :
    integral01
        ((1 - qt) ^ n *
          (qFactorTerm 1 n a * qFactorTerm 2 n b *
            qFactorTerm 3 n c * qFactorTerm 4 n d)) =
      qMomentExpandedTerm n a b c d := by
  rw [qFactorTerm_product_eq n a b c d ha hb hc hd]
  have hreorder :
      (1 - qt) ^ n *
          (Polynomial.C (qMomentTermCoefficient n a b c d) *
            qt ^ fourIndexSum a b c d) =
        Polynomial.C (qMomentTermCoefficient n a b c d) *
          (qt ^ fourIndexSum a b c d * (1 - qt) ^ n) := by
    ring
  rw [hreorder, ← Polynomial.smul_eq_C_mul, map_smul]
  simp only [smul_eq_mul, qBetaIntegral]
  rw [qBetaIntegral_eq_factorial]
  rfl

/-- The exact zero-th moment is the finite beta expansion. -/
theorem qMoment_zero_eq_expanded (n : ℕ) :
    qMoment n 0 = qMomentExpanded n := by
  simp only [qMoment, pow_zero, one_mul]
  rw [qKernel_pow_eq_beta_mul_expansion]
  unfold qFourExpansion qMomentExpanded
  simp only [Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  apply integral01_expanded_kernel_term
  all_goals omega

#print axioms qFactorTerm_product_eq
#print axioms qMoment_zero_eq_expanded

end

end Arxiv.«2508.10245».Geode5Proof
