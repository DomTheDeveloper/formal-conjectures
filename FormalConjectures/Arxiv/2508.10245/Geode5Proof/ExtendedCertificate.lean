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

The ZIP supplied five independent held-out 59-bit residues.  One additional
59-bit prime was evaluated by the same independently compiled C++ recurrence.
Adding these six residues gives enough modulus for a direct absolute-value
triangle bound, so the final proof need not assume or separately formalize
nonnegativity of the Geode coefficient.
-/

namespace Arxiv.«2508.10245».Geode5Proof

/-- Five held-out residues from the ZIP, followed by one newly reproduced residue. -/
def extraResiduePairs : List (ℕ × ℕ) := [
  (576460752303299797, 327718321886832208),
  (576460752303299863, 423641906617630847),
  (576460752303299821, 347006306158823866),
  (576460752303299933, 206611125298715198),
  (576460752303299687, 453389533131839477),
  (576460752303299543, 186016919201673100)
]

/-- The complete 486-prime certificate. -/
def extendedResiduePairs : List (ℕ × ℕ) :=
  residuePairs ++ extraResiduePairs

/-- Product of all 486 moduli. -/
def extendedCertificateModulus : ℕ :=
  (extendedResiduePairs.map Prod.fst).prod

/-- The six additional moduli are prime. -/
theorem extraResiduePrimes :
    ∀ pr ∈ extraResiduePairs, Nat.Prime pr.1 := by
  native_decide

/-- The six additional residues are canonical. -/
theorem extraResidues_canonical :
    ∀ pr ∈ extraResiduePairs, pr.2 < pr.1 := by
  native_decide

/-- The additional primes are disjoint from the original 480-prime set. -/
theorem extraResidues_disjoint :
    List.Disjoint (residuePairs.map Prod.fst)
      (extraResiduePairs.map Prod.fst) := by
  native_decide

/-- All 486 moduli are pairwise coprime. -/
theorem extendedModuli_pairwise_coprime :
    extendedResiduePairs.Pairwise (Nat.Coprime on Prod.fst) := by
  native_decide

/-- The 8,367-digit candidate agrees with all six additional residues. -/
theorem answer_modEq_extraResidue :
    ∀ pr ∈ extraResiduePairs, answerValue ≡ pr.2 [MOD pr.1] := by
  native_decide

/-- The candidate agrees with every residue in the extended certificate. -/
theorem answer_modEq_extendedResidue :
    ∀ pr ∈ extendedResiduePairs, answerValue ≡ pr.2 [MOD pr.1] := by
  native_decide

/-- The extended modulus has more than 28,628 binary digits of headroom. -/
theorem two_pow_28628_lt_extendedCertificateModulus :
    2 ^ 28628 < extendedCertificateModulus := by
  native_decide

/-- Combine all 486 residues into one congruence. -/
theorem modEq_answerValue_of_extendedResidues (z : ℕ)
    (hz : ∀ pr ∈ extendedResiduePairs, z ≡ pr.2 [MOD pr.1]) :
    z ≡ answerValue [MOD extendedCertificateModulus] := by
  apply (Nat.modEq_list_map_prod_iff extendedModuli_pairwise_coprime).2
  intro pr hpr
  exact (hz pr hpr).trans (answer_modEq_extendedResidue pr hpr).symm

#print axioms extendedModuli_pairwise_coprime
#print axioms answer_modEq_extendedResidue
#print axioms two_pow_28628_lt_extendedCertificateModulus

end Arxiv.«2508.10245».Geode5Proof
