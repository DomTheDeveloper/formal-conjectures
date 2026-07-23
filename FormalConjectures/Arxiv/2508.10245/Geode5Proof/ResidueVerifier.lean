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

import FormalConjectures.Arxiv.«2508.10245».Geode5Proof.ShiftedResidue

/-!
# Computable verifier for one Geode residue certificate

The primality proof is selected dependently.  In the prime branch, the checker
executes the denominator-free modular recurrence and compares it with the stored
residue.  The accompanying theorem exposes the resulting shifted congruence.
-/

namespace Arxiv.«2508.10245».Geode5Proof

/-- Complete check performed for one `(prime,residue)` certificate pair. -/
def residueVerified (pr : ℕ × ℕ) : Prop :=
  if hp : pr.1.Prime then
    letI : Fact pr.1.Prime := ⟨hp⟩
    modularDenominator pr.1 1000 ≠ 0 ∧
      modularGeode pr.1 1000 = (pr.2 : ZMod pr.1)
  else
    False

/-- A successful one-pair check implies its centered CRT congruence. -/
theorem shifted_modEq_of_residueVerified (pr : ℕ × ℕ)
    (h : residueVerified pr)
    (hanswer : answerValue ≡ pr.2 [MOD pr.1]) :
    shiftedGeode ≡ shiftedAnswer [MOD pr.1] := by
  unfold residueVerified at h
  split at h
  next hp =>
    letI : Fact pr.1.Prime := ⟨hp⟩
    exact shifted_modEq_of_modular_value pr.1 pr.2 h.1 h.2 hanswer
  next hnp =>
    contradiction

/-- One genuine certificate pair, used to benchmark the verified evaluator. -/
set_option maxHeartbeats 0 in
theorem residueVerifier_smoke :
    residueVerified (576460752303404051, 464097493913787811) := by
  native_decide

#print axioms shifted_modEq_of_residueVerified
#print axioms residueVerifier_smoke

end Arxiv.«2508.10245».Geode5Proof
