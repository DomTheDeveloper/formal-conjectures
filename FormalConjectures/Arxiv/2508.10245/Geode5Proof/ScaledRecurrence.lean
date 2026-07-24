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
import FormalConjectures.Arxiv.«2508.10245».Geode5Proof.MomentToReduced

/-!
# Denominator-free integer recurrence for the Geode moments

The rational triangular recurrence can be scaled by a common denominator.
At level `n`, all five moment polynomials are represented as integer
polynomials divided by `scaledDenominator n`.  A complete level multiplies the
common denominator by the five diagonal entries.  Prefix products clear every
forward-substitution division, leaving only integer polynomial arithmetic.
-/

namespace Arxiv.«2508.10245».Geode5Proof

open scoped BigOperators

/-- Integer polynomials in the parameter `y`. -/
abbrev ZYPoly := Polynomial ℤ

/-- The integer polynomial variable. -/
def zy : ZYPoly := Polynomial.X

/-- Cast an integer polynomial coefficientwise to `Polynomial ℚ`. -/
def castZY (p : ZYPoly) : QYPoly :=
  p.map (Int.castRingHom ℚ)

/-- Integer version of the power-sum coefficient. -/
def zPowerSum (d : ℕ) : ZYPoly :=
  ∑ w ∈ Finset.range 5, zy ^ (d * w)

/-- Integer sparse action of one exact remainder table. -/
def zSparseAction (terms : List SparseTerm) (v : ℕ → ZYPoly) : ZYPoly :=
  terms.foldr (fun a s =>
    (a.coefficient : ZYPoly) * zy ^ a.shift * v a.source + s) 0

@[simp]
theorem castZY_zero : castZY 0 = 0 := by
  simp [castZY]

@[simp]
theorem castZY_add (a b : ZYPoly) :
    castZY (a + b) = castZY a + castZY b := by
  simp [castZY]

@[simp]
theorem castZY_mul (a b : ZYPoly) :
    castZY (a * b) = castZY a * castZY b := by
  simp [castZY]

@[simp]
theorem castZY_neg (a : ZYPoly) :
    castZY (-a) = -castZY a := by
  simp [castZY]

@[simp]
theorem castZY_natCast (n : ℕ) :
    castZY (n : ZYPoly) = (n : QYPoly) := by
  simp [castZY]

@[simp]
theorem castZY_zPowerSum (d : ℕ) :
    castZY (zPowerSum d) = qPowerSum d := by
  simp [castZY, zPowerSum, qPowerSum, zy, qy]

/-- Casting an integer sparse action gives the rational sparse action. -/
theorem castZY_zSparseAction (terms : List SparseTerm) (v : ℕ → ZYPoly) :
    castZY (zSparseAction terms v) =
      qSparseAction terms (fun i => castZY (v i)) := by
  induction terms with
  | nil => simp [zSparseAction, qSparseAction]
  | cons a terms ih =>
      simp [zSparseAction, qSparseAction, ih, castZY, zy, qy]

/-- Product of the first `i+1` diagonal entries at recurrence level `n`. -/
def diagonalPrefix (n i : ℕ) : ℕ :=
  ∏ j ∈ Finset.range (i + 1), recurrenceDiagonal n j

/-- Product of the diagonal entries strictly after row `i`. -/
def diagonalSuffix (n i : ℕ) : ℕ :=
  ∏ j ∈ Finset.Ico (i + 1) 5, recurrenceDiagonal n j

/-- Product of all five diagonal entries. -/
def diagonalProduct (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range 5, recurrenceDiagonal n j

/-- Common denominator for the five scaled moments. -/
def scaledDenominator : ℕ → ℕ
  | 0 => 120
  | n + 1 => scaledDenominator n * diagonalProduct n

/-- Initial integer vector, representing `120 * (1,1/2,...,1/5)`. -/
def zInitialMoment : ℕ → ZYPoly
  | 0 => 120
  | 1 => 60
  | 2 => 40
  | 3 => 30
  | 4 => 24
  | _ => 0

/-- Prefix-scaled row zero numerator. -/
def zK0 (n : ℕ) (prev : ℕ → ZYPoly) : ZYPoly :=
  -(n + 1 : ZYPoly) * zSparseAction r0Terms prev

/-- Prefix-scaled row one numerator. -/
def zK1 (n : ℕ) (prev : ℕ → ZYPoly) : ZYPoly :=
  -(n + 1 : ZYPoly) *
    ((recurrenceDiagonal n 0 : ZYPoly) * zSparseAction r1Terms prev +
      zPowerSum 1 * zK0 n prev)

/-- Prefix-scaled row two numerator. -/
def zK2 (n : ℕ) (prev : ℕ → ZYPoly) : ZYPoly :=
  -(n + 1 : ZYPoly) *
    ((recurrenceDiagonal n 0 * recurrenceDiagonal n 1 : ℕ) *
        zSparseAction r2Terms prev +
      (recurrenceDiagonal n 1 : ZYPoly) * zPowerSum 2 * zK0 n prev +
      zPowerSum 1 * zK1 n prev)

/-- Prefix-scaled row three numerator. -/
def zK3 (n : ℕ) (prev : ℕ → ZYPoly) : ZYPoly :=
  -(n + 1 : ZYPoly) *
    ((recurrenceDiagonal n 0 * recurrenceDiagonal n 1 *
          recurrenceDiagonal n 2 : ℕ) * zSparseAction r3Terms prev +
      (recurrenceDiagonal n 1 * recurrenceDiagonal n 2 : ℕ) *
        zPowerSum 3 * zK0 n prev +
      (recurrenceDiagonal n 2 : ZYPoly) * zPowerSum 2 * zK1 n prev +
      zPowerSum 1 * zK2 n prev)

/-- Prefix-scaled row four numerator. -/
def zK4 (n : ℕ) (prev : ℕ → ZYPoly) : ZYPoly :=
  -(n + 1 : ZYPoly) *
    ((recurrenceDiagonal n 0 * recurrenceDiagonal n 1 *
          recurrenceDiagonal n 2 * recurrenceDiagonal n 3 : ℕ) *
        zSparseAction r4Terms prev +
      (recurrenceDiagonal n 1 * recurrenceDiagonal n 2 *
          recurrenceDiagonal n 3 : ℕ) * zPowerSum 4 * zK0 n prev +
      (recurrenceDiagonal n 2 * recurrenceDiagonal n 3 : ℕ) *
        zPowerSum 3 * zK1 n prev +
      (recurrenceDiagonal n 3 : ZYPoly) * zPowerSum 2 * zK2 n prev +
      zPowerSum 1 * zK3 n prev)

/-- One denominator-free integer recurrence step. -/
def zScaledStep (n : ℕ) (prev : ℕ → ZYPoly) : ℕ → ZYPoly
  | 0 =>
      (recurrenceDiagonal n 1 * recurrenceDiagonal n 2 *
        recurrenceDiagonal n 3 * recurrenceDiagonal n 4 : ℕ) * zK0 n prev
  | 1 =>
      (recurrenceDiagonal n 2 * recurrenceDiagonal n 3 *
        recurrenceDiagonal n 4 : ℕ) * zK1 n prev
  | 2 =>
      (recurrenceDiagonal n 3 * recurrenceDiagonal n 4 : ℕ) * zK2 n prev
  | 3 => (recurrenceDiagonal n 4 : ZYPoly) * zK3 n prev
  | 4 => zK4 n prev
  | _ => 0

/-- Iteration of the denominator-free recurrence. -/
def zScaledMoment : ℕ → ℕ → ZYPoly
  | 0 => zInitialMoment
  | n + 1 => zScaledStep n (zScaledMoment n)

/-- The initial integer vector has exactly the claimed rational meaning. -/
theorem castZY_zInitialMoment (i : ℕ) (hi : i < 5) :
    castZY (zInitialMoment i) =
      (scaledDenominator 0 : QYPoly) * qMoment 0 i := by
  interval_cases i <;>
    norm_num [zInitialMoment, scaledDenominator, qMoment_zero, castZY]

/-- The complete diagonal product agrees with the existing determinant factor. -/
theorem diagonalProduct_eq (n : ℕ) :
    diagonalProduct n =
      5 * (n + 2) * (5 * n + 6) * (5 * n + 7) *
        (5 * n + 8) * (5 * n + 9) := by
  simpa [diagonalProduct] using recurrenceDiagonal_product n

#print axioms castZY_zSparseAction
#print axioms castZY_zInitialMoment
#print axioms diagonalProduct_eq

end Arxiv.«2508.10245».Geode5Proof
