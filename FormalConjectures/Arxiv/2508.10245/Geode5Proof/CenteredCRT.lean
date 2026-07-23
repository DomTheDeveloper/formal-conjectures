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

import FormalConjectures.Arxiv.«2508.10245».Geode5Proof.AbsoluteBound
import FormalConjectures.Arxiv.«2508.10245».Geode5Proof.ExtendedCertificate

/-!
# Centered CRT uniqueness for the exact Geode value

The original alternating sum is an integer that may a priori have either sign.
We shift both it and the proposed answer by `2^35618`.  The absolute bound puts
both shifted values in `[0,2^35619)`, while the 608-prime product is larger than
`2^35620`.  Natural-number CRT uniqueness then gives the original equality.
-/

namespace Arxiv.«2508.10245».Geode5Proof

/-- Centering shift used to turn the signed coefficient into a natural number. -/
def crtShift : ℕ := 2 ^ 35618

/-- Shifted natural representative of the true Geode coefficient. -/
def shiftedGeode : ℕ :=
  Int.toNat (geode5Diagonal 1000 + crtShift)

/-- Shifted natural representative of the proposed exact answer. -/
def shiftedAnswer : ℕ := answerValue + crtShift

/-- The proposed answer is much smaller than the centering shift. -/
theorem answerValue_lt_crtShift : answerValue < crtShift := by
  native_decide

/-- The absolute bound gives both signed inequalities for the true coefficient. -/
theorem geode5_1000_center_bounds :
    -(crtShift : ℤ) < geode5Diagonal 1000 ∧
      geode5Diagonal 1000 < (crtShift : ℤ) := by
  have hnat := geode5_1000_natAbs_lt_two_pow
  have habs : |geode5Diagonal 1000| < (crtShift : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hnat
  simpa only [abs_lt] using habs

/-- The shifted true coefficient is exactly the corresponding integer sum. -/
theorem shiftedGeode_cast :
    (shiftedGeode : ℤ) = geode5Diagonal 1000 + crtShift := by
  have hnonneg : 0 ≤ geode5Diagonal 1000 + (crtShift : ℤ) := by
    have h := geode5_1000_center_bounds.1
    omega
  simpa [shiftedGeode] using Int.toNat_of_nonneg hnonneg

/-- The shifted true coefficient lies below twice the shift. -/
theorem shiftedGeode_lt_two_mul_shift : shiftedGeode < 2 * crtShift := by
  have hupper :
      geode5Diagonal 1000 + (crtShift : ℤ) < (2 * crtShift : ℕ) := by
    have h := geode5_1000_center_bounds.2
    norm_num at h ⊢
    omega
  rw [← shiftedGeode_cast] at hupper
  exact_mod_cast hupper

/-- The shifted proposed answer also lies below twice the shift. -/
theorem shiftedAnswer_lt_two_mul_shift : shiftedAnswer < 2 * crtShift := by
  unfold shiftedAnswer
  omega

/-- Twice the shift is below the 608-prime CRT modulus. -/
theorem two_mul_shift_lt_extendedCertificateModulus :
    2 * crtShift < extendedCertificateModulus := by
  have h := two_pow_35620_lt_extendedCertificateModulus
  unfold crtShift
  have hp : 2 * 2 ^ 35618 < 2 ^ 35620 := by
    norm_num [pow_succ]
  exact hp.trans h

/-- Combine all shifted congruences into one congruence modulo the full product. -/
theorem shifted_modEq_extended_product
    (hres : ∀ pr ∈ extendedResiduePairs,
      shiftedGeode ≡ shiftedAnswer [MOD pr.1]) :
    shiftedGeode ≡ shiftedAnswer [MOD extendedCertificateModulus] := by
  apply (Nat.modEq_list_map_prod_iff extendedModuli_pairwise_coprime).2
  intro pr hpr
  exact hres pr hpr

/-- Centered CRT uniqueness forces the exact integer equality. -/
theorem geode5_1000_eq_answer_of_shifted_residues
    (hres : ∀ pr ∈ extendedResiduePairs,
      shiftedGeode ≡ shiftedAnswer [MOD pr.1]) :
    geode5Diagonal 1000 = (answerValue : ℤ) := by
  have hmod := shifted_modEq_extended_product hres
  have heq : shiftedGeode = shiftedAnswer :=
    hmod.eq_of_lt_of_lt
      (shiftedGeode_lt_two_mul_shift.trans
        two_mul_shift_lt_extendedCertificateModulus)
      (shiftedAnswer_lt_two_mul_shift.trans
        two_mul_shift_lt_extendedCertificateModulus)
  have heqz : (shiftedGeode : ℤ) = (shiftedAnswer : ℤ) := by
    exact_mod_cast heq
  rw [shiftedGeode_cast] at heqz
  simp only [shiftedAnswer, Nat.cast_add] at heqz
  omega

#print axioms geode5_1000_eq_answer_of_shifted_residues

end Arxiv.«2508.10245».Geode5Proof
