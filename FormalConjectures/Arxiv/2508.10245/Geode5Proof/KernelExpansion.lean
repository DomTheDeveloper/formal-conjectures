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

import FormalConjectures.Arxiv.«2508.10245».Geode5Proof.BetaIntegral
import Mathlib.Data.Nat.Choose.Sum

/-!
# Binomial expansion of the Geode kernel power

The factor with weight zero is kept as `(1-t)^n`.  The other four factors are
expanded independently, exactly matching the four indices in the original
alternating sum.
-/

namespace Arxiv.«2508.10245».Geode5Proof

open scoped BigOperators

noncomputable section

/-- One term in the binomial expansion of `(y^w-t)^n`. -/
def qFactorTerm (w n j : ℕ) : TQYPoly :=
  Polynomial.C
      (((-1 : QYPoly) ^ j) * (Nat.choose n j : QYPoly) *
        qy ^ (w * (n - j))) *
    qt ^ j

/-- The finite binomial expansion of `(y^w-t)^n`. -/
def qFactorExpansion (w n : ℕ) : TQYPoly :=
  ∑ j ∈ Finset.range (n + 1), qFactorTerm w n j

/-- One nonzero-weight kernel factor has the expected expansion. -/
theorem qFactor_pow_eq_expansion (w n : ℕ) :
    (Polynomial.C (qy ^ w) - qt) ^ n = qFactorExpansion w n := by
  rw [show Polynomial.C (qy ^ w) - qt = -qt + Polynomial.C (qy ^ w) by ring]
  rw [add_pow]
  unfold qFactorExpansion
  apply Finset.sum_congr rfl
  intro j hj
  unfold qFactorTerm
  simp [Polynomial.C_pow]
  ring

/-- The kernel as its five explicit factors. -/
theorem qKernel_eq_explicit :
    qKernel =
      (1 - qt) * (Polynomial.C qy - qt) *
        (Polynomial.C (qy ^ 2) - qt) *
        (Polynomial.C (qy ^ 3) - qt) *
        (Polynomial.C (qy ^ 4) - qt) := by
  simp [qKernel, qy, Finset.prod_range_succ]
  ring

/-- Product of the four nonzero-weight binomial sums. -/
def qFourExpansion (n : ℕ) : TQYPoly :=
  ∑ a ∈ Finset.range (n + 1),
    ∑ b ∈ Finset.range (n + 1),
      ∑ c ∈ Finset.range (n + 1),
        ∑ d ∈ Finset.range (n + 1),
          qFactorTerm 1 n a * qFactorTerm 2 n b *
            qFactorTerm 3 n c * qFactorTerm 4 n d

/-- Full kernel-power expansion, retaining the beta factor. -/
theorem qKernel_pow_eq_beta_mul_expansion (n : ℕ) :
    qKernel ^ n = (1 - qt) ^ n * qFourExpansion n := by
  rw [qKernel_eq_explicit]
  simp only [mul_pow]
  rw [qFactor_pow_eq_expansion 1 n, qFactor_pow_eq_expansion 2 n,
    qFactor_pow_eq_expansion 3 n, qFactor_pow_eq_expansion 4 n]
  simp only [qFourExpansion, qFactorExpansion, Finset.mul_sum,
    Finset.sum_mul]
  ring

#print axioms qFactor_pow_eq_expansion
#print axioms qKernel_pow_eq_beta_mul_expansion

end

end Arxiv.«2508.10245».Geode5Proof
