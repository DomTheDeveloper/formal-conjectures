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

import FormalConjectures.Arxiv.«2508.10245».Geode5Proof.ResidueVerifier

/-!
# Verification of all 608 Geode residue certificates

`native_decide` compiles the proved denominator-free recurrence and checks every
stored prime/residue pair.  The theorem after it transports those computations
to congruences of the original `geode5Diagonal` definition.
-/

namespace Arxiv.«2508.10245».Geode5Proof

/-- Every pair in the extended certificate passes the verified evaluator. -/
set_option maxHeartbeats 0 in
theorem allExtendedResidues_verified :
    ∀ pr ∈ extendedResiduePairs, residueVerified pr := by
  native_decide

/-- All 608 shifted congruences required by centered CRT. -/
theorem allExtendedResidues_shifted_modEq :
    ∀ pr ∈ extendedResiduePairs,
      shiftedGeode ≡ shiftedAnswer [MOD pr.1] := by
  intro pr hpr
  exact shifted_modEq_of_residueVerified pr
    (allExtendedResidues_verified pr hpr)
    (answer_modEq_extendedResidue pr hpr)

#print axioms allExtendedResidues_verified
#print axioms allExtendedResidues_shifted_modEq

end Arxiv.«2508.10245».Geode5Proof
