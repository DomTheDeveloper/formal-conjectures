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

import FormalConjectures.Arxiv.«2508.10245».Geode5Proof.MomentExpansion
import FormalConjectures.Arxiv.«2508.10245».Geode5Proof.MomentFormula

/-!
# Identification of the moment formula with the reduced Geode sum

After the beta integral, every four-index term is a single monomial in `y`.
The coefficient extraction therefore contributes the final binomial coefficient
from the ZIP derivation.
-/

namespace Arxiv.«2508.10245».Geode5Proof

open scoped BigOperators

noncomputable section

/-- Rational factorial quotient equals the cast binomial coefficient. -/
theorem qBinomial_eq_choose {n k : ℕ} (hk : k ≤ n) :
    qBinomial n k = (Nat.choose n k : ℚ) := by
  have hfac := Nat.choose_mul_factorial_mul_factorial hk
  simp only [qBinomial, qFactorial]
  field_simp
  exact_mod_cast hfac

/-- One scalar term after the final coefficient extraction. -/
def qExtractedMomentTerm (n a b c d : ℕ) : ℚ :=
  (-1 : ℚ) ^ fourIndexSum a b c d *
    (Nat.choose n a : ℚ) * (Nat.choose n b : ℚ) *
    (Nat.choose n c : ℚ) * (Nat.choose n d : ℚ) *
    (qFactorial (fourIndexSum a b c d) * qFactorial n /
      qFactorial (n + fourIndexSum a b c d + 1)) *
    (Nat.choose (20 * n + 2 - fourIndexWeight a b c d) (5 * n) : ℚ)

/-- A moment term is a single monomial in `y`. -/
theorem qMomentExpandedTerm_eq_monomial (n a b c d : ℕ) :
    qMomentExpandedTerm n a b c d =
      Polynomial.monomial (10 * n - fourIndexWeight a b c d)
        ((-1 : ℚ) ^ fourIndexSum a b c d *
          (Nat.choose n a : ℚ) * (Nat.choose n b : ℚ) *
          (Nat.choose n c : ℚ) * (Nat.choose n d : ℚ) *
          (qFactorial (fourIndexSum a b c d) * qFactorial n /
            qFactorial (n + fourIndexSum a b c d + 1))) := by
  simp [qMomentExpandedTerm, qMomentTermCoefficient, qy,
    Polynomial.X_pow_eq_monomial, ← Polynomial.C_mul]
  ring

/-- Extraction of one expanded term gives the ZIP binomial factor. -/
theorem qMomentExpandedTerm_extract (n a b c d : ℕ)
    (ha : a ≤ n) (hb : b ≤ n) (hc : c ≤ n) (hd : d ≤ n) :
    (qMomentExpandedTerm n a b c d).sum
        (fun j x => x * (Nat.choose (10 * n + 2 + j) (5 * n) : ℚ)) =
      qExtractedMomentTerm n a b c d := by
  rw [qMomentExpandedTerm_eq_monomial]
  have hexp :
      10 * n + 2 + (10 * n - fourIndexWeight a b c d) =
        20 * n + 2 - fourIndexWeight a b c d := by
    simp [fourIndexWeight]
    omega
  simp [Polynomial.sum_monomial_index, qExtractedMomentTerm, hexp]
  ring

/-- The extraction sum is the finite sum of extracted four-index terms. -/
theorem extractionSum_eq_four_sum (n : ℕ) :
    extractionSum n =
      ∑ a ∈ Finset.range (n + 1),
        ∑ b ∈ Finset.range (n + 1),
          ∑ c ∈ Finset.range (n + 1),
            ∑ d ∈ Finset.range (n + 1),
              qExtractedMomentTerm n a b c d := by
  unfold extractionSum
  rw [qMoment_zero_eq_expanded]
  unfold qMomentExpanded
  simp only [Polynomial.sum_add_index]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  apply qMomentExpandedTerm_extract
  all_goals omega

/-- One extracted moment term matches one reduced Geode summand after scaling. -/
theorem scaled_qExtractedMomentTerm_eq_qReducedSummand
    (n a b c d : ℕ)
    (ha : a ≤ n) (hb : b ≤ n) (hc : c ≤ n) (hd : d ≤ n) :
    qFactorial (5 * n) / qFactorial n ^ 5 *
        qExtractedMomentTerm n a b c d =
      qReducedSummand n a b c d := by
  have htop : 5 * n ≤ 20 * n + 2 - fourIndexWeight a b c d := by
    simp [fourIndexWeight]
    omega
  rw [← qBinomial_eq_choose ha, ← qBinomial_eq_choose hb,
    ← qBinomial_eq_choose hc, ← qBinomial_eq_choose hd,
    ← qBinomial_eq_choose htop]
  simp only [qExtractedMomentTerm, qReducedSummand, fourIndexSum,
    fourIndexWeight]
  field_simp [qFactorial]
  ring

/-- The moment coefficient formula is exactly the reduced rational Geode sum. -/
theorem momentGeode_eq_qReducedGeode (n : ℕ) :
    momentGeode n = qReducedGeode n := by
  rw [momentGeode, momentCoefficient_eq_extractionSum,
    extractionSum_eq_four_sum]
  unfold qReducedGeode
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  apply scaled_qExtractedMomentTerm_eq_qReducedSummand
  all_goals omega

/-- The exact benchmark cast equals the moment formula for every `n`. -/
theorem cast_geode5Diagonal_eq_momentGeode (n : ℕ) :
    (geode5Diagonal n : ℚ) = momentGeode n := by
  rw [cast_geode5Diagonal_eq_qReducedGeode,
    ← momentGeode_eq_qReducedGeode]

#print axioms extractionSum_eq_four_sum
#print axioms momentGeode_eq_qReducedGeode
#print axioms cast_geode5Diagonal_eq_momentGeode

end

end Arxiv.«2508.10245».Geode5Proof
