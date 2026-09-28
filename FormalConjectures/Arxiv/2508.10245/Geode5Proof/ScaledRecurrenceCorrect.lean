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

import FormalConjectures.Arxiv.«2508.10245».Geode5Proof.ScaledRecurrence
import FormalConjectures.Arxiv.«2508.10245».Geode5Proof.RowEquations

/-!
# Correctness of the denominator-free integer Geode recurrence

The proof follows the same forward-substitution order as the computational
certificate.  Prefix-scaled numerators clear the current row's denominator;
suffix products then put all five rows over one common denominator.
-/

namespace Arxiv.«2508.10245».Geode5Proof

noncomputable section

/-- Sparse action commutes with multiplication of the whole moment vector. -/
theorem qSparseAction_scale (terms : List SparseTerm) (s : QYPoly)
    (v : ℕ → QYPoly) :
    qSparseAction terms (fun i => s * v i) =
      s * qSparseAction terms v := by
  induction terms with
  | nil => simp [qSparseAction]
  | cons a terms ih =>
      simp [qSparseAction, ih]
      ring

/-- Sparse action only depends on the listed source entries. -/
theorem qSparseAction_congr_sources (terms : List SparseTerm)
    (v w : ℕ → QYPoly)
    (h : ∀ a ∈ terms, v a.source = w a.source) :
    qSparseAction terms v = qSparseAction terms w := by
  induction terms with
  | nil => simp [qSparseAction]
  | cons a terms ih =>
      simp only [qSparseAction, List.foldr_cons]
      rw [h a (by simp)]
      rw [ih]
      intro b hb
      exact h b (by simp [hb])

private theorem castSparseTable
    (terms : List SparseTerm) (hsrc : ∀ a ∈ terms, a.source < 5)
    (prev : ℕ → ZYPoly) (n : ℕ)
    (hprev : ∀ i, i < 5 →
      castZY (prev i) = (scaledDenominator n : QYPoly) * qMoment n i) :
    castZY (zSparseAction terms prev) =
      (scaledDenominator n : QYPoly) * qSparseAction terms (qMoment n) := by
  rw [castZY_zSparseAction]
  calc
    qSparseAction terms (fun i => castZY (prev i)) =
        qSparseAction terms
          (fun i => (scaledDenominator n : QYPoly) * qMoment n i) := by
      apply qSparseAction_congr_sources
      intro a ha
      exact hprev a.source (hsrc a ha)
    _ = (scaledDenominator n : QYPoly) *
        qSparseAction terms (qMoment n) :=
      qSparseAction_scale terms _ _

/-- Prefix-scaled row zero has the claimed rational value. -/
theorem castZY_zK0 (n : ℕ) (prev : ℕ → ZYPoly)
    (hprev : ∀ i, i < 5 →
      castZY (prev i) = (scaledDenominator n : QYPoly) * qMoment n i) :
    castZY (zK0 n prev) =
      (scaledDenominator n * recurrenceDiagonal n 0 : ℕ) *
        qMoment (n + 1) 0 := by
  have hs := castSparseTable r0Terms r0Terms_source_lt_five prev n hprev
  have hrow := qRowEquation0 n
  simp only [zK0, castZY_neg, castZY_mul, castZY_natCast]
  rw [hs]
  norm_cast
  linear_combination (scaledDenominator n : QYPoly) * hrow

/-- Prefix-scaled row one has the claimed rational value. -/
theorem castZY_zK1 (n : ℕ) (prev : ℕ → ZYPoly)
    (hprev : ∀ i, i < 5 →
      castZY (prev i) = (scaledDenominator n : QYPoly) * qMoment n i) :
    castZY (zK1 n prev) =
      (scaledDenominator n * recurrenceDiagonal n 0 *
          recurrenceDiagonal n 1 : ℕ) * qMoment (n + 1) 1 := by
  have hs := castSparseTable r1Terms r1Terms_source_lt_five prev n hprev
  have hk0 := castZY_zK0 n prev hprev
  have hrow := qRowEquation1 n
  simp only [zK1, castZY_neg, castZY_mul, castZY_add,
    castZY_natCast, castZY_zPowerSum]
  rw [hs, hk0]
  norm_cast
  linear_combination
    (scaledDenominator n * recurrenceDiagonal n 0 : QYPoly) * hrow

/-- Prefix-scaled row two has the claimed rational value. -/
theorem castZY_zK2 (n : ℕ) (prev : ℕ → ZYPoly)
    (hprev : ∀ i, i < 5 →
      castZY (prev i) = (scaledDenominator n : QYPoly) * qMoment n i) :
    castZY (zK2 n prev) =
      (scaledDenominator n * recurrenceDiagonal n 0 *
          recurrenceDiagonal n 1 * recurrenceDiagonal n 2 : ℕ) *
        qMoment (n + 1) 2 := by
  have hs := castSparseTable r2Terms r2Terms_source_lt_five prev n hprev
  have hk0 := castZY_zK0 n prev hprev
  have hk1 := castZY_zK1 n prev hprev
  have hrow := qRowEquation2 n
  simp only [zK2, castZY_neg, castZY_mul, castZY_add,
    castZY_natCast, castZY_zPowerSum]
  rw [hs, hk0, hk1]
  norm_cast
  linear_combination
    (scaledDenominator n * recurrenceDiagonal n 0 *
      recurrenceDiagonal n 1 : QYPoly) * hrow

/-- Prefix-scaled row three has the claimed rational value. -/
theorem castZY_zK3 (n : ℕ) (prev : ℕ → ZYPoly)
    (hprev : ∀ i, i < 5 →
      castZY (prev i) = (scaledDenominator n : QYPoly) * qMoment n i) :
    castZY (zK3 n prev) =
      (scaledDenominator n * recurrenceDiagonal n 0 *
          recurrenceDiagonal n 1 * recurrenceDiagonal n 2 *
          recurrenceDiagonal n 3 : ℕ) * qMoment (n + 1) 3 := by
  have hs := castSparseTable r3Terms r3Terms_source_lt_five prev n hprev
  have hk0 := castZY_zK0 n prev hprev
  have hk1 := castZY_zK1 n prev hprev
  have hk2 := castZY_zK2 n prev hprev
  have hrow := qRowEquation3 n
  simp only [zK3, castZY_neg, castZY_mul, castZY_add,
    castZY_natCast, castZY_zPowerSum]
  rw [hs, hk0, hk1, hk2]
  norm_cast
  linear_combination
    (scaledDenominator n * recurrenceDiagonal n 0 *
      recurrenceDiagonal n 1 * recurrenceDiagonal n 2 : QYPoly) * hrow

/-- Prefix-scaled row four has the claimed rational value. -/
theorem castZY_zK4 (n : ℕ) (prev : ℕ → ZYPoly)
    (hprev : ∀ i, i < 5 →
      castZY (prev i) = (scaledDenominator n : QYPoly) * qMoment n i) :
    castZY (zK4 n prev) =
      (scaledDenominator n * recurrenceDiagonal n 0 *
          recurrenceDiagonal n 1 * recurrenceDiagonal n 2 *
          recurrenceDiagonal n 3 * recurrenceDiagonal n 4 : ℕ) *
        qMoment (n + 1) 4 := by
  have hs := castSparseTable r4Terms r4Terms_source_lt_five prev n hprev
  have hk0 := castZY_zK0 n prev hprev
  have hk1 := castZY_zK1 n prev hprev
  have hk2 := castZY_zK2 n prev hprev
  have hk3 := castZY_zK3 n prev hprev
  have hrow := qRowEquation4 n
  simp only [zK4, castZY_neg, castZY_mul, castZY_add,
    castZY_natCast, castZY_zPowerSum]
  rw [hs, hk0, hk1, hk2, hk3]
  norm_cast
  linear_combination
    (scaledDenominator n * recurrenceDiagonal n 0 *
      recurrenceDiagonal n 1 * recurrenceDiagonal n 2 *
      recurrenceDiagonal n 3 : QYPoly) * hrow

/-- One integer step represents the next rational moment vector. -/
theorem castZY_zScaledStep (n : ℕ) (prev : ℕ → ZYPoly)
    (hprev : ∀ i, i < 5 →
      castZY (prev i) = (scaledDenominator n : QYPoly) * qMoment n i)
    (i : ℕ) (hi : i < 5) :
    castZY (zScaledStep n prev i) =
      (scaledDenominator (n + 1) : QYPoly) * qMoment (n + 1) i := by
  have hk0 := castZY_zK0 n prev hprev
  have hk1 := castZY_zK1 n prev hprev
  have hk2 := castZY_zK2 n prev hprev
  have hk3 := castZY_zK3 n prev hprev
  have hk4 := castZY_zK4 n prev hprev
  interval_cases i <;>
    simp [zScaledStep, scaledDenominator, diagonalProduct,
      recurrenceDiagonal] at hk0 hk1 hk2 hk3 hk4 ⊢ <;>
    norm_cast at hk0 hk1 hk2 hk3 hk4 ⊢ <;>
    ring_nf at hk0 hk1 hk2 hk3 hk4 ⊢ <;>
    assumption

/-- Every denominator-free iterate represents the exact rational moment. -/
theorem castZY_zScaledMoment (n i : ℕ) (hi : i < 5) :
    castZY (zScaledMoment n i) =
      (scaledDenominator n : QYPoly) * qMoment n i := by
  induction n with
  | zero => exact castZY_zInitialMoment i hi
  | succ n ih =>
      exact castZY_zScaledStep n (zScaledMoment n)
        (fun j hj => ih j hj) i hi

#print axioms castZY_zK4
#print axioms castZY_zScaledStep
#print axioms castZY_zScaledMoment

end

end Arxiv.«2508.10245».Geode5Proof
