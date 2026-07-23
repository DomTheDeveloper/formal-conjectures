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

import FormalConjectures.Arxiv.«2508.10245».Geode5Proof.ModularRecurrence
import FormalConjectures.Arxiv.«2508.10245».Geode5Proof.ScaledExtraction

/-!
# Sound modular extraction for the Geode certificate

The exact integer identity is reduced into `ZMod p`.  Provided the one final
common denominator is nonzero, division recovers the residue of the original
integer benchmark definition.
-/

namespace Arxiv.«2508.10245».Geode5Proof

noncomputable section

/-- Weighted extraction from a modular polynomial. -/
def mWeightedExtraction (p n : ℕ) (f : ModYPoly p) : ZMod p :=
  f.sum fun j a => a * (Nat.choose (10 * n + 2 + j) (5 * n) : ZMod p)

/-- Final extraction from the modular scaled zero-th moment. -/
def mScaledExtraction (p n : ℕ) : ZMod p :=
  mWeightedExtraction p n (mScaledMoment p n 0)

/-- The single denominator cleared by the scaled integer identity. -/
def modularDenominator (p n : ℕ) : ZMod p :=
  (scaledDenominator n * Nat.factorial n ^ 5 : ℕ)

/-- Numerator of the modular Geode value. -/
def modularNumerator (p n : ℕ) : ZMod p :=
  (Nat.factorial (5 * n) : ZMod p) * mScaledExtraction p n

/-- Value returned by the polynomial modular recurrence. -/
def modularGeode (p n : ℕ) [Fact p.Prime] : ZMod p :=
  modularNumerator p n / modularDenominator p n

/-- Reduction commutes with weighted extraction. -/
theorem reduceZY_zWeightedExtraction (p n : ℕ) (f : ZYPoly) :
    ((zWeightedExtraction n f : ℤ) : ZMod p) =
      mWeightedExtraction p n (reduceZY p f) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
      simp [zWeightedExtraction, mWeightedExtraction, reduceZY,
        Polynomial.sum_add_index, hf, hg]
  | monomial k a =>
      simp [zWeightedExtraction, mWeightedExtraction, reduceZY,
        Polynomial.sum_monomial_index]

/-- The modular extraction is reduction of the integer extraction. -/
theorem reduce_zScaledExtraction (p n : ℕ) :
    ((zScaledExtraction n : ℤ) : ZMod p) = mScaledExtraction p n := by
  unfold zScaledExtraction mScaledExtraction
  rw [reduceZY_zWeightedExtraction]
  rw [reduceZY_zScaledMoment]

/-- The original Geode integer satisfies the modular numerator equation. -/
theorem geode5_modular_numerator_identity (p n : ℕ) :
    (geode5Diagonal n : ZMod p) * modularDenominator p n =
      modularNumerator p n := by
  have h := geode5_scaled_extraction_identity n
  exact_mod_cast h.trans (by
    simp [modularDenominator, modularNumerator, reduce_zScaledExtraction])

/-- Soundness of the modular Geode recurrence and extraction. -/
theorem modularGeode_eq_cast (p n : ℕ) [Fact p.Prime]
    (hden : modularDenominator p n ≠ 0) :
    modularGeode p n = (geode5Diagonal n : ZMod p) := by
  rw [modularGeode, div_eq_iff hden]
  exact (geode5_modular_numerator_identity p n).symm

#print axioms reduce_zScaledExtraction
#print axioms modularGeode_eq_cast

end

end Arxiv.«2508.10245».Geode5Proof
