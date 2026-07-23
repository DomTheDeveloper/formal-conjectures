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

import FormalConjectures.Arxiv.«2508.10245».Geode5Proof.CRT

/-!
# Extended Geode CRT certificate

The ZIP supplied five independent held-out 59-bit residues. Thirteen further
59-bit residues were evaluated by the same independently compiled C++
recurrence. The resulting 498-prime modulus is large enough for a direct
absolute-value triangle bound, so the final proof need not assume or separately
formalize nonnegativity of the Geode coefficient.
-/

namespace Arxiv.«2508.10245».Geode5Proof

/-- Five held-out ZIP residues and thirteen independently reproduced residues. -/
def extraResiduePairs : List (ℕ × ℕ) := [
  (576460752303299797, 327718321886832208),
  (576460752303299863, 423641906617630847),
  (576460752303299821, 347006306158823866),
  (576460752303299933, 206611125298715198),
  (576460752303299687, 453389533131839477),
  (576460752303299543, 186016919201673100),
  (576460752303298013, 63544640585865593),
  (576460752303298021, 468323385122980284),
  (576460752303298097, 85457251407509296),
  (576460752303298211, 113004847477017170),
  (576460752303298243, 202708756634276441),
  (576460752303298363, 471041901716053767),
  (576460752303298397, 410831671984623212),
  (576460752303298433, 345513146660740669),
  (576460752303298453, 184190636185675670),
  (576460752303298463, 261341561174140556),
  (576460752303298537, 135501421446546013),
  (576460752303298591, 281682552906510882)
]

/-- The complete 498-prime certificate. -/
def extendedResiduePairs : List (ℕ × ℕ) :=
  residuePairs ++ extraResiduePairs

/-- Product of all 498 moduli. -/
def extendedCertificateModulus : ℕ :=
  (extendedResiduePairs.map Prod.fst).prod

/-- The eighteen additional moduli are prime. -/
theorem extraResiduePrimes :
    ∀ pr ∈ extraResiduePairs, Nat.Prime pr.1 := by
  native_decide

/-- The eighteen additional residues are canonical. -/
theorem extraResidues_canonical :
    ∀ pr ∈ extraResiduePairs, pr.2 < pr.1 := by
  native_decide

/-- The additional primes are disjoint from the original 480-prime set. -/
theorem extraResidues_disjoint :
    List.Disjoint (residuePairs.map Prod.fst)
      (extraResiduePairs.map Prod.fst) := by
  native_decide

/-- All 498 moduli are pairwise coprime. -/
theorem extendedModuli_pairwise_coprime :
    extendedResiduePairs.Pairwise (Nat.Coprime on Prod.fst) := by
  native_decide

/-- The candidate agrees with all eighteen additional residues. -/
theorem answer_modEq_extraResidue :
    ∀ pr ∈ extraResiduePairs, answerValue ≡ pr.2 [MOD pr.1] := by
  native_decide

/-- The candidate agrees with every residue in the extended certificate. -/
theorem answer_modEq_extendedResidue :
    ∀ pr ∈ extendedResiduePairs, answerValue ≡ pr.2 [MOD pr.1] := by
  native_decide

/-- The extended modulus exceeds the centered-CRT threshold. -/
theorem two_pow_29192_lt_extendedCertificateModulus :
    2 ^ 29192 < extendedCertificateModulus := by
  native_decide

/-- Combine all 498 residues into one congruence. -/
theorem modEq_answerValue_of_extendedResidues (z : ℕ)
    (hz : ∀ pr ∈ extendedResiduePairs, z ≡ pr.2 [MOD pr.1]) :
    z ≡ answerValue [MOD extendedCertificateModulus] := by
  apply (Nat.modEq_list_map_prod_iff extendedModuli_pairwise_coprime).2
  intro pr hpr
  exact (hz pr hpr).trans (answer_modEq_extendedResidue pr hpr).symm

#print axioms extendedModuli_pairwise_coprime
#print axioms answer_modEq_extendedResidue
#print axioms two_pow_29192_lt_extendedCertificateModulus

end Arxiv.«2508.10245».Geode5Proof
