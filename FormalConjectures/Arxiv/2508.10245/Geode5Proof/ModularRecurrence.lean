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
import Mathlib.Data.ZMod.Basic

/-!
# Modular form of the scaled Geode recurrence

This is the same denominator-free recurrence over `ZMod p`.  A coefficientwise
map theorem proves it is exactly the reduction modulo `p` of the integer
recurrence; no numerical result is trusted without that theorem.
-/

namespace Arxiv.«2508.10245».Geode5Proof

open scoped BigOperators

/-- Polynomials over a modular coefficient ring. -/
abbrev ModYPoly (p : ℕ) := Polynomial (ZMod p)

/-- Coefficientwise reduction of an integer polynomial modulo `p`. -/
def reduceZY (p : ℕ) (f : ZYPoly) : ModYPoly p :=
  f.map (Int.castRingHom (ZMod p))

/-- Modular polynomial variable. -/
def my (p : ℕ) : ModYPoly p := Polynomial.X

/-- Modular power-sum coefficient. -/
def mPowerSum (p d : ℕ) : ModYPoly p :=
  ∑ w ∈ Finset.range 5, my p ^ (d * w)

/-- Modular sparse table action. -/
def mSparseAction (p : ℕ) (terms : List SparseTerm)
    (v : ℕ → ModYPoly p) : ModYPoly p :=
  terms.foldr (fun a s =>
    (a.coefficient : ModYPoly p) * my p ^ a.shift * v a.source + s) 0

@[simp]
theorem reduceZY_zero (p : ℕ) : reduceZY p 0 = 0 := by
  simp [reduceZY]

@[simp]
theorem reduceZY_add (p : ℕ) (a b : ZYPoly) :
    reduceZY p (a + b) = reduceZY p a + reduceZY p b := by
  simp [reduceZY]

@[simp]
theorem reduceZY_mul (p : ℕ) (a b : ZYPoly) :
    reduceZY p (a * b) = reduceZY p a * reduceZY p b := by
  simp [reduceZY]

@[simp]
theorem reduceZY_neg (p : ℕ) (a : ZYPoly) :
    reduceZY p (-a) = -reduceZY p a := by
  simp [reduceZY]

@[simp]
theorem reduceZY_natCast (p n : ℕ) :
    reduceZY p (n : ZYPoly) = (n : ModYPoly p) := by
  simp [reduceZY]

@[simp]
theorem reduceZY_zPowerSum (p d : ℕ) :
    reduceZY p (zPowerSum d) = mPowerSum p d := by
  simp [reduceZY, zPowerSum, mPowerSum, zy, my]

/-- Reduction commutes with every sparse table action. -/
theorem reduceZY_zSparseAction (p : ℕ) (terms : List SparseTerm)
    (v : ℕ → ZYPoly) :
    reduceZY p (zSparseAction terms v) =
      mSparseAction p terms (fun i => reduceZY p (v i)) := by
  induction terms with
  | nil => simp [zSparseAction, mSparseAction]
  | cons a terms ih =>
      simp [zSparseAction, mSparseAction, ih, reduceZY, zy, my]

/-- Modular prefix-scaled row zero. -/
def mK0 (p n : ℕ) (prev : ℕ → ModYPoly p) : ModYPoly p :=
  -(n + 1 : ModYPoly p) * mSparseAction p r0Terms prev

/-- Modular prefix-scaled row one. -/
def mK1 (p n : ℕ) (prev : ℕ → ModYPoly p) : ModYPoly p :=
  -(n + 1 : ModYPoly p) *
    ((recurrenceDiagonal n 0 : ModYPoly p) * mSparseAction p r1Terms prev +
      mPowerSum p 1 * mK0 p n prev)

/-- Modular prefix-scaled row two. -/
def mK2 (p n : ℕ) (prev : ℕ → ModYPoly p) : ModYPoly p :=
  -(n + 1 : ModYPoly p) *
    ((recurrenceDiagonal n 0 * recurrenceDiagonal n 1 : ℕ) *
        mSparseAction p r2Terms prev +
      (recurrenceDiagonal n 1 : ModYPoly p) *
        mPowerSum p 2 * mK0 p n prev +
      mPowerSum p 1 * mK1 p n prev)

/-- Modular prefix-scaled row three. -/
def mK3 (p n : ℕ) (prev : ℕ → ModYPoly p) : ModYPoly p :=
  -(n + 1 : ModYPoly p) *
    ((recurrenceDiagonal n 0 * recurrenceDiagonal n 1 *
          recurrenceDiagonal n 2 : ℕ) * mSparseAction p r3Terms prev +
      (recurrenceDiagonal n 1 * recurrenceDiagonal n 2 : ℕ) *
        mPowerSum p 3 * mK0 p n prev +
      (recurrenceDiagonal n 2 : ModYPoly p) *
        mPowerSum p 2 * mK1 p n prev +
      mPowerSum p 1 * mK2 p n prev)

/-- Modular prefix-scaled row four. -/
def mK4 (p n : ℕ) (prev : ℕ → ModYPoly p) : ModYPoly p :=
  -(n + 1 : ModYPoly p) *
    ((recurrenceDiagonal n 0 * recurrenceDiagonal n 1 *
          recurrenceDiagonal n 2 * recurrenceDiagonal n 3 : ℕ) *
        mSparseAction p r4Terms prev +
      (recurrenceDiagonal n 1 * recurrenceDiagonal n 2 *
          recurrenceDiagonal n 3 : ℕ) *
        mPowerSum p 4 * mK0 p n prev +
      (recurrenceDiagonal n 2 * recurrenceDiagonal n 3 : ℕ) *
        mPowerSum p 3 * mK1 p n prev +
      (recurrenceDiagonal n 3 : ModYPoly p) *
        mPowerSum p 2 * mK2 p n prev +
      mPowerSum p 1 * mK3 p n prev)

/-- One modular scaled recurrence step. -/
def mScaledStep (p n : ℕ) (prev : ℕ → ModYPoly p) : ℕ → ModYPoly p
  | 0 =>
      (recurrenceDiagonal n 1 * recurrenceDiagonal n 2 *
        recurrenceDiagonal n 3 * recurrenceDiagonal n 4 : ℕ) * mK0 p n prev
  | 1 =>
      (recurrenceDiagonal n 2 * recurrenceDiagonal n 3 *
        recurrenceDiagonal n 4 : ℕ) * mK1 p n prev
  | 2 =>
      (recurrenceDiagonal n 3 * recurrenceDiagonal n 4 : ℕ) * mK2 p n prev
  | 3 => (recurrenceDiagonal n 4 : ModYPoly p) * mK3 p n prev
  | 4 => mK4 p n prev
  | _ => 0

/-- Initial modular scaled vector. -/
def mInitialMoment (p : ℕ) : ℕ → ModYPoly p
  | 0 => 120
  | 1 => 60
  | 2 => 40
  | 3 => 30
  | 4 => 24
  | _ => 0

/-- Iterated modular scaled recurrence. -/
def mScaledMoment (p : ℕ) : ℕ → ℕ → ModYPoly p
  | 0 => mInitialMoment p
  | n + 1 => mScaledStep p n (mScaledMoment p n)

/-- Reduction of each integer prefix row is the corresponding modular row. -/
theorem reduceZY_zK0 (p n : ℕ) (prev : ℕ → ZYPoly) :
    reduceZY p (zK0 n prev) =
      mK0 p n (fun i => reduceZY p (prev i)) := by
  simp [zK0, mK0, reduceZY_zSparseAction]

theorem reduceZY_zK1 (p n : ℕ) (prev : ℕ → ZYPoly) :
    reduceZY p (zK1 n prev) =
      mK1 p n (fun i => reduceZY p (prev i)) := by
  simp [zK1, mK1, reduceZY_zSparseAction]

theorem reduceZY_zK2 (p n : ℕ) (prev : ℕ → ZYPoly) :
    reduceZY p (zK2 n prev) =
      mK2 p n (fun i => reduceZY p (prev i)) := by
  simp [zK2, mK2, reduceZY_zSparseAction]

theorem reduceZY_zK3 (p n : ℕ) (prev : ℕ → ZYPoly) :
    reduceZY p (zK3 n prev) =
      mK3 p n (fun i => reduceZY p (prev i)) := by
  simp [zK3, mK3, reduceZY_zSparseAction]

theorem reduceZY_zK4 (p n : ℕ) (prev : ℕ → ZYPoly) :
    reduceZY p (zK4 n prev) =
      mK4 p n (fun i => reduceZY p (prev i)) := by
  simp [zK4, mK4, reduceZY_zSparseAction]

/-- Reduction commutes with one complete scaled recurrence step. -/
theorem reduceZY_zScaledStep (p n : ℕ) (prev : ℕ → ZYPoly) (i : ℕ) :
    reduceZY p (zScaledStep n prev i) =
      mScaledStep p n (fun j => reduceZY p (prev j)) i := by
  cases i <;> simp [zScaledStep, mScaledStep, reduceZY_zK0,
    reduceZY_zK1, reduceZY_zK2, reduceZY_zK3, reduceZY_zK4]

/-- The modular recurrence is exactly reduction of the integer recurrence. -/
theorem reduceZY_zScaledMoment (p n i : ℕ) :
    reduceZY p (zScaledMoment n i) = mScaledMoment p n i := by
  induction n with
  | zero =>
      cases i <;> simp [zScaledMoment, zInitialMoment,
        mScaledMoment, mInitialMoment, reduceZY]
  | succ n ih =>
      simp only [zScaledMoment, mScaledMoment]
      rw [reduceZY_zScaledStep]
      congr 1
      funext j
      exact ih j

#print axioms reduceZY_zSparseAction
#print axioms reduceZY_zScaledMoment

end Arxiv.«2508.10245».Geode5Proof
