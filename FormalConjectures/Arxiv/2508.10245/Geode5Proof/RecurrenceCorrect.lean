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
# Correctness of the executable five-state Geode recurrence

Each row follows from the audited integration-by-parts identity after expanding
the corresponding quotient and exact sparse remainder table.
-/

namespace Arxiv.«2508.10245».Geode5Proof

noncomputable section

/-- The rational zero-th power sum is five. -/
theorem qPowerSum_zero : qPowerSum 0 = 5 := by
  norm_num [qPowerSum, qy, Finset.sum_range_succ]

/-- Solving a positive constant diagonal recovers the unique polynomial solution. -/
theorem solveDiagonal_eq_of_mul_eq (d : ℕ) (hd : 0 < d)
    (rhs x : QYPoly) (h : (d : QYPoly) * x = rhs) :
    solveDiagonal d rhs = x := by
  rw [← h]
  simp [solveDiagonal, ← Polynomial.C_mul, hd.ne']

/-- Correctness of recurrence row zero. -/
theorem qRow0_correct (n : ℕ) :
    qRow0 n (qMoment n) = qMoment (n + 1) 0 := by
  unfold qRow0
  apply solveDiagonal_eq_of_mul_eq _ (recurrenceDiagonal_pos n 0)
  have h := qMoment_recurrence_raw n 1 (by omega)
  rw [qMomentRemainder_eq_r0, integral01_qSparsePolynomial,
    integral01_qMomentQuotient] at h
  simp [qQuotientAction, qPowerSum_zero, recurrenceDiagonal,
    Finset.sum_range_succ] at h ⊢
  linear_combination h

/-- Correctness of recurrence row one. -/
theorem qRow1_correct (n : ℕ) :
    qRow1 n (qMoment n) = qMoment (n + 1) 1 := by
  unfold qRow1
  rw [qRow0_correct]
  apply solveDiagonal_eq_of_mul_eq _ (recurrenceDiagonal_pos n 1)
  have h := qMoment_recurrence_raw n 2 (by omega)
  rw [qMomentRemainder_eq_r1, integral01_qSparsePolynomial,
    integral01_qMomentQuotient] at h
  simp [qQuotientAction, qPowerSum_zero, recurrenceDiagonal,
    Finset.sum_range_succ] at h ⊢
  linear_combination h

/-- Correctness of recurrence row two. -/
theorem qRow2_correct (n : ℕ) :
    qRow2 n (qMoment n) = qMoment (n + 1) 2 := by
  unfold qRow2
  rw [qRow0_correct, qRow1_correct]
  apply solveDiagonal_eq_of_mul_eq _ (recurrenceDiagonal_pos n 2)
  have h := qMoment_recurrence_raw n 3 (by omega)
  rw [qMomentRemainder_eq_r2, integral01_qSparsePolynomial,
    integral01_qMomentQuotient] at h
  simp [qQuotientAction, qPowerSum_zero, recurrenceDiagonal,
    Finset.sum_range_succ] at h ⊢
  linear_combination h

/-- Correctness of recurrence row three. -/
theorem qRow3_correct (n : ℕ) :
    qRow3 n (qMoment n) = qMoment (n + 1) 3 := by
  unfold qRow3
  rw [qRow0_correct, qRow1_correct, qRow2_correct]
  apply solveDiagonal_eq_of_mul_eq _ (recurrenceDiagonal_pos n 3)
  have h := qMoment_recurrence_raw n 4 (by omega)
  rw [qMomentRemainder_eq_r3, integral01_qSparsePolynomial,
    integral01_qMomentQuotient] at h
  simp [qQuotientAction, qPowerSum_zero, recurrenceDiagonal,
    Finset.sum_range_succ] at h ⊢
  linear_combination h

/-- Correctness of recurrence row four. -/
theorem qRow4_correct (n : ℕ) :
    qRow4 n (qMoment n) = qMoment (n + 1) 4 := by
  unfold qRow4
  rw [qRow0_correct, qRow1_correct, qRow2_correct, qRow3_correct]
  apply solveDiagonal_eq_of_mul_eq _ (recurrenceDiagonal_pos n 4)
  have h := qMoment_recurrence_raw n 5 (by omega)
  rw [qMomentRemainder_eq_r4, integral01_qSparsePolynomial,
    integral01_qMomentQuotient] at h
  simp [qQuotientAction, qPowerSum_zero, recurrenceDiagonal,
    Finset.sum_range_succ] at h ⊢
  linear_combination h

/-- The executable step reproduces all five exact moments. -/
theorem qRecurrenceStep_correct (n i : ℕ) (hi : i < 5) :
    qRecurrenceStep n (qMoment n) i = qMoment (n + 1) i := by
  interval_cases i <;>
    simp [qRecurrenceStep, qRow0_correct, qRow1_correct, qRow2_correct,
      qRow3_correct, qRow4_correct]

#print axioms qRecurrenceStep_correct

end

end Arxiv.«2508.10245».Geode5Proof
