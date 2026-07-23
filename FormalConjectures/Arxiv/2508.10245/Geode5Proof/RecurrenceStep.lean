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
import FormalConjectures.Arxiv.«2508.10245».Geode5Proof.RemainderTables

/-!
# Expanded five-state recurrence for the Geode moments

This module transports the exact integer sparse tables into the rational
polynomial ring used by `qMoment`, proves that integration of a table is the
corresponding sparse action on the five moments, and exposes the lower
triangular recurrence as an executable polynomial step.
-/

namespace Arxiv.«2508.10245».Geode5Proof

open scoped BigOperators

noncomputable section

/-- Interpret a sparse table over the rational nested polynomial ring. -/
def qSparsePolynomial (terms : List SparseTerm) : TQYPoly :=
  terms.foldr (fun a p =>
    Polynomial.C ((a.coefficient : QYPoly) * qy ^ a.shift) * qt ^ a.source + p) 0

/-- View a five-vector as a total natural-indexed function. -/
def finVectorToNat (v : Fin 5 → QYPoly) (j : ℕ) : QYPoly :=
  if h : j < 5 then v ⟨j, h⟩ else 0

/-- Apply a sparse remainder table to a vector of polynomial moments. -/
def qSparseAction (terms : List SparseTerm) (v : ℕ → QYPoly) : QYPoly :=
  terms.foldr (fun a s =>
    (a.coefficient : QYPoly) * qy ^ a.shift * v a.source + s) 0

set_option maxHeartbeats 1000000 in
theorem qMomentRemainder_eq_r0 : qMomentRemainder 1 = qSparsePolynomial r0Terms := by
  simp [qMomentRemainder, qKernel, qMomentQuotient, qPowerSum, qSparsePolynomial,
    r0Terms, qy, qt, Finset.prod_range_succ,
    Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_X, Polynomial.derivative_pow]
  have hfive : (Polynomial.C (5 : QYPoly) : TQYPoly) = 5 := by norm_num
  rw [hfive]
  ring_nf

set_option maxHeartbeats 1000000 in
theorem qMomentRemainder_eq_r1 : qMomentRemainder 2 = qSparsePolynomial r1Terms := by
  simp [qMomentRemainder, qKernel, qMomentQuotient, qPowerSum, qSparsePolynomial,
    r1Terms, qy, qt, Finset.prod_range_succ,
    Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_X, Polynomial.derivative_pow]
  ring_nf

set_option maxHeartbeats 1000000 in
theorem qMomentRemainder_eq_r2 : qMomentRemainder 3 = qSparsePolynomial r2Terms := by
  simp [qMomentRemainder, qKernel, qMomentQuotient, qPowerSum, qSparsePolynomial,
    r2Terms, qy, qt, Finset.prod_range_succ,
    Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_X, Polynomial.derivative_pow]
  ring_nf

set_option maxHeartbeats 1000000 in
theorem qMomentRemainder_eq_r3 : qMomentRemainder 4 = qSparsePolynomial r3Terms := by
  simp [qMomentRemainder, qKernel, qMomentQuotient, qPowerSum, qSparsePolynomial,
    r3Terms, qy, qt, Finset.prod_range_succ,
    Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_X, Polynomial.derivative_pow]
  ring_nf

set_option maxHeartbeats 1000000 in
theorem qMomentRemainder_eq_r4 : qMomentRemainder 5 = qSparsePolynomial r4Terms := by
  simp [qMomentRemainder, qKernel, qMomentQuotient, qPowerSum, qSparsePolynomial,
    r4Terms, qy, qt, Finset.prod_range_succ,
    Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_X, Polynomial.derivative_pow]
  ring_nf

/-- Integration of a sparse table is its sparse action on the moment vector. -/
theorem integral01_qSparsePolynomial (terms : List SparseTerm) (n : ℕ) :
    integral01 (qSparsePolynomial terms * qKernel ^ n) =
      qSparseAction terms (qMoment n) := by
  induction terms with
  | nil => simp [qSparsePolynomial, qSparseAction]
  | cons a terms ih =>
      simp only [qSparsePolynomial, qSparseAction, List.foldr_cons]
      rw [add_mul, map_add]
      rw [mul_assoc]
      rw [← Polynomial.smul_eq_C_mul, map_smul]
      simp only [smul_eq_mul, qMoment]
      rw [ih]

/-- Expand the quotient integral into its lower moment combination. -/
def qQuotientAction (k : ℕ) (v : ℕ → QYPoly) : QYPoly :=
  ∑ ell ∈ Finset.range k, qPowerSum (k - 1 - ell) * v ell

theorem integral01_qMomentQuotient (n k : ℕ) :
    integral01 (qMomentQuotient k * qKernel ^ n) =
      qQuotientAction k (qMoment n) := by
  simp [qMomentQuotient, qQuotientAction, Finset.sum_mul, map_sum,
    ← Polynomial.smul_eq_C_mul, map_smul, smul_eq_mul, qMoment, mul_assoc]

/-- Select the exact sparse remainder row for `i = 0, ..., 4`. -/
def remainderTerms : Fin 5 → List SparseTerm
  | 0 => r0Terms
  | 1 => r1Terms
  | 2 => r2Terms
  | 3 => r3Terms
  | 4 => r4Terms

/-- Solve one diagonal row over `Polynomial ℚ`. -/
def solveDiagonal (d : ℕ) (rhs : QYPoly) : QYPoly :=
  Polynomial.C ((d : ℚ)⁻¹) * rhs

/-- Explicit lower-triangular five-state recurrence step. -/
def qRecurrenceStep (n : ℕ) (prev : Fin 5 → QYPoly) : Fin 5 → QYPoly :=
  fun i =>
    Fin.cases
      (solveDiagonal (recurrenceDiagonal n 0)
        (-(n + 1 : QYPoly) * qSparseAction r0Terms finVectorToNat prev))
      (fun i1 =>
        Fin.cases
          (let x0 := solveDiagonal (recurrenceDiagonal n 0)
              (-(n + 1 : QYPoly) * qSparseAction r0Terms finVectorToNat prev)
           solveDiagonal (recurrenceDiagonal n 1)
             (-(n + 1 : QYPoly) *
               (qSparseAction r1Terms finVectorToNat prev + qPowerSum 1 * x0)))
          (fun i2 =>
            Fin.cases
              (let x0 := solveDiagonal (recurrenceDiagonal n 0)
                    (-(n + 1 : QYPoly) * qSparseAction r0Terms finVectorToNat prev)
               let x1 := solveDiagonal (recurrenceDiagonal n 1)
                    (-(n + 1 : QYPoly) *
                      (qSparseAction r1Terms finVectorToNat prev + qPowerSum 1 * x0))
               solveDiagonal (recurrenceDiagonal n 2)
                 (-(n + 1 : QYPoly) *
                   (qSparseAction r2Terms finVectorToNat prev +
                     qPowerSum 2 * x0 + qPowerSum 1 * x1)))
              (fun i3 =>
                Fin.cases
                  (let x0 := solveDiagonal (recurrenceDiagonal n 0)
                        (-(n + 1 : QYPoly) * qSparseAction r0Terms finVectorToNat prev)
                   let x1 := solveDiagonal (recurrenceDiagonal n 1)
                        (-(n + 1 : QYPoly) *
                          (qSparseAction r1Terms finVectorToNat prev + qPowerSum 1 * x0))
                   let x2 := solveDiagonal (recurrenceDiagonal n 2)
                        (-(n + 1 : QYPoly) *
                          (qSparseAction r2Terms finVectorToNat prev +
                            qPowerSum 2 * x0 + qPowerSum 1 * x1))
                   solveDiagonal (recurrenceDiagonal n 3)
                     (-(n + 1 : QYPoly) *
                       (qSparseAction r3Terms finVectorToNat prev +
                         qPowerSum 3 * x0 + qPowerSum 2 * x1 + qPowerSum 1 * x2)))
                  (fun _ =>
                    let x0 := solveDiagonal (recurrenceDiagonal n 0)
                          (-(n + 1 : QYPoly) * qSparseAction r0Terms finVectorToNat prev)
                    let x1 := solveDiagonal (recurrenceDiagonal n 1)
                          (-(n + 1 : QYPoly) *
                            (qSparseAction r1Terms finVectorToNat prev + qPowerSum 1 * x0))
                    let x2 := solveDiagonal (recurrenceDiagonal n 2)
                          (-(n + 1 : QYPoly) *
                            (qSparseAction r2Terms finVectorToNat prev +
                              qPowerSum 2 * x0 + qPowerSum 1 * x1))
                    let x3 := solveDiagonal (recurrenceDiagonal n 3)
                          (-(n + 1 : QYPoly) *
                            (qSparseAction r3Terms finVectorToNat prev +
                              qPowerSum 3 * x0 + qPowerSum 2 * x1 + qPowerSum 1 * x2))
                    solveDiagonal (recurrenceDiagonal n 4)
                      (-(n + 1 : QYPoly) *
                        (qSparseAction r4Terms finVectorToNat prev +
                          qPowerSum 4 * x0 + qPowerSum 3 * x1 +
                          qPowerSum 2 * x2 + qPowerSum 1 * x3))) i3) i2) i1) i

#print axioms integral01_qSparsePolynomial
#print axioms integral01_qMomentQuotient

end

end Arxiv.«2508.10245».Geode5Proof
