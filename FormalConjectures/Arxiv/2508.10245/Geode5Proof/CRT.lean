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

import FormalConjectures.Arxiv.«2508.10245».Geode5
import FormalConjectures.Arxiv.«2508.10245».Geode5Proof.CertificateData
import Mathlib.Data.Nat.ChineseRemainder

/-!
# CRT certificate layer for the five-dimensional Geode computation

This module checks the exact 480-prime Chinese-remainder certificate and proves
uniqueness below the rigorous hyper-Catalan upper bound.
-/

namespace Arxiv.«2508.10245».Geode5Proof

open scoped Function

/-- The rigorous hyper-Catalan upper bound from the certificate. -/
def upperBound : ℕ :=
  Nat.factorial 20002 /
    (Nat.factorial 15002 * Nat.factorial 1001 * Nat.factorial 1000 ^ 4)

/-- Product of all 480 certificate moduli. -/
def certificateModulus : ℕ := (residuePairs.map Prod.fst).prod

/-- The stored moduli are pairwise coprime. -/
theorem residueModuli_pairwise_coprime :
    residuePairs.Pairwise (Nat.Coprime on Prod.fst) := by
  native_decide

/-- Every stored residue is canonical. -/
theorem residueValues_canonical :
    ∀ pr ∈ residuePairs, pr.2 < pr.1 := by
  native_decide

/-- The proposed exact answer has every stored residue. -/
theorem answer_modEq_residue :
    ∀ pr ∈ residuePairs, answerValue ≡ pr.2 [MOD pr.1] := by
  native_decide

/-- The hyper-Catalan upper bound is strictly smaller than the CRT modulus. -/
theorem upperBound_lt_certificateModulus :
    upperBound < certificateModulus := by
  native_decide

/-- The proposed answer lies below the rigorous upper bound. -/
theorem answerValue_lt_upperBound : answerValue < upperBound := by
  native_decide

/-- Combine the 480 congruences into one congruence modulo their product. -/
theorem modEq_answerValue_of_residues (z : ℕ)
    (hz : ∀ pr ∈ residuePairs, z ≡ pr.2 [MOD pr.1]) :
    z ≡ answerValue [MOD certificateModulus] := by
  apply (Nat.modEq_list_map_prod_iff residueModuli_pairwise_coprime).2
  intro pr hpr
  exact (hz pr hpr).trans (answer_modEq_residue pr hpr).symm

/-- CRT uniqueness below the rigorous Geode upper bound. -/
theorem eq_answerValue_of_residues_of_lt_upperBound (z : ℕ)
    (hz : ∀ pr ∈ residuePairs, z ≡ pr.2 [MOD pr.1])
    (hzlt : z < upperBound) :
    z = answerValue := by
  exact (modEq_answerValue_of_residues z hz).eq_of_lt_of_lt
    (hzlt.trans upperBound_lt_certificateModulus)
    (answerValue_lt_upperBound.trans upperBound_lt_certificateModulus)

/--
Final arithmetic bridge: once the moment recurrence supplies nonnegativity, the
upper bound, and all 480 residues for the Formal Conjectures definition, the
exact 8,367-digit equality follows.
-/
theorem geode5_1000_of_certificate
    (hnonneg : 0 ≤ geode5Diagonal 1000)
    (hbound : Int.toNat (geode5Diagonal 1000) < upperBound)
    (hres : ∀ pr ∈ residuePairs,
      Int.toNat (geode5Diagonal 1000) ≡ pr.2 [MOD pr.1]) :
    geode5Diagonal 1000 = (answerValue : ℤ) := by
  have hnat : Int.toNat (geode5Diagonal 1000) = answerValue :=
    eq_answerValue_of_residues_of_lt_upperBound _ hres hbound
  calc
    geode5Diagonal 1000 = Int.toNat (geode5Diagonal 1000) := by
      symm
      exact Int.toNat_of_nonneg hnonneg
    _ = answerValue := by exact_mod_cast hnat

#print axioms residueModuli_pairwise_coprime
#print axioms answer_modEq_residue
#print axioms upperBound_lt_certificateModulus
#print axioms geode5_1000_of_certificate

end Arxiv.«2508.10245».Geode5Proof
