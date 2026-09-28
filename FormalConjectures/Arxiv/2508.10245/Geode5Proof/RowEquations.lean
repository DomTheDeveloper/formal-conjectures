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

import FormalConjectures.Arxiv.«2508.10245».Geode5Proof.RecurrenceCorrect

/-!
# Explicit triangular row equations for the Geode recurrence

These equations are the denominator-free contracts used by the scaled integer
recurrence.  They are direct specializations of the audited integration-by-parts
identity and exact sparse remainder tables.
-/

namespace Arxiv.«2508.10245».Geode5Proof

noncomputable section

/-- Triangular recurrence row zero. -/
theorem qRowEquation0 (n : ℕ) :
    (recurrenceDiagonal n 0 : QYPoly) * qMoment (n + 1) 0 =
      -(n + 1 : QYPoly) * qSparseAction r0Terms (qMoment n) := by
  have h := qMoment_recurrence_raw n 1 (by omega)
  rw [qMomentRemainder_eq_r0, integral01_qSparsePolynomial,
    integral01_qMomentQuotient] at h
  simp [qQuotientAction, qPowerSum_zero, recurrenceDiagonal,
    Finset.sum_range_succ] at h ⊢
  linear_combination h

/-- Triangular recurrence row one. -/
theorem qRowEquation1 (n : ℕ) :
    (recurrenceDiagonal n 1 : QYPoly) * qMoment (n + 1) 1 +
        (n + 1 : QYPoly) * qPowerSum 1 * qMoment (n + 1) 0 =
      -(n + 1 : QYPoly) * qSparseAction r1Terms (qMoment n) := by
  have h := qMoment_recurrence_raw n 2 (by omega)
  rw [qMomentRemainder_eq_r1, integral01_qSparsePolynomial,
    integral01_qMomentQuotient] at h
  simp [qQuotientAction, qPowerSum_zero, recurrenceDiagonal,
    Finset.sum_range_succ] at h ⊢
  linear_combination h

/-- Triangular recurrence row two. -/
theorem qRowEquation2 (n : ℕ) :
    (recurrenceDiagonal n 2 : QYPoly) * qMoment (n + 1) 2 +
        (n + 1 : QYPoly) *
          (qPowerSum 2 * qMoment (n + 1) 0 +
            qPowerSum 1 * qMoment (n + 1) 1) =
      -(n + 1 : QYPoly) * qSparseAction r2Terms (qMoment n) := by
  have h := qMoment_recurrence_raw n 3 (by omega)
  rw [qMomentRemainder_eq_r2, integral01_qSparsePolynomial,
    integral01_qMomentQuotient] at h
  simp [qQuotientAction, qPowerSum_zero, recurrenceDiagonal,
    Finset.sum_range_succ] at h ⊢
  linear_combination h

/-- Triangular recurrence row three. -/
theorem qRowEquation3 (n : ℕ) :
    (recurrenceDiagonal n 3 : QYPoly) * qMoment (n + 1) 3 +
        (n + 1 : QYPoly) *
          (qPowerSum 3 * qMoment (n + 1) 0 +
            qPowerSum 2 * qMoment (n + 1) 1 +
            qPowerSum 1 * qMoment (n + 1) 2) =
      -(n + 1 : QYPoly) * qSparseAction r3Terms (qMoment n) := by
  have h := qMoment_recurrence_raw n 4 (by omega)
  rw [qMomentRemainder_eq_r3, integral01_qSparsePolynomial,
    integral01_qMomentQuotient] at h
  simp [qQuotientAction, qPowerSum_zero, recurrenceDiagonal,
    Finset.sum_range_succ] at h ⊢
  linear_combination h

/-- Triangular recurrence row four. -/
theorem qRowEquation4 (n : ℕ) :
    (recurrenceDiagonal n 4 : QYPoly) * qMoment (n + 1) 4 +
        (n + 1 : QYPoly) *
          (qPowerSum 4 * qMoment (n + 1) 0 +
            qPowerSum 3 * qMoment (n + 1) 1 +
            qPowerSum 2 * qMoment (n + 1) 2 +
            qPowerSum 1 * qMoment (n + 1) 3) =
      -(n + 1 : QYPoly) * qSparseAction r4Terms (qMoment n) := by
  have h := qMoment_recurrence_raw n 5 (by omega)
  rw [qMomentRemainder_eq_r4, integral01_qSparsePolynomial,
    integral01_qMomentQuotient] at h
  simp [qQuotientAction, qPowerSum_zero, recurrenceDiagonal,
    Finset.sum_range_succ] at h ⊢
  linear_combination h

#print axioms qRowEquation0
#print axioms qRowEquation4

end

end Arxiv.«2508.10245».Geode5Proof
