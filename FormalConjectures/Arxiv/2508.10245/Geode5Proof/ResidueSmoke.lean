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

import FormalConjectures.Arxiv.«2508.10245».Geode5Proof.ModularExtraction

/-!
# Performance smoke test for one genuine Geode certificate prime

This file is intentionally isolated so the modular evaluator can be timed before
the 480 residue checks are split into parallel certificate modules.
-/

namespace Arxiv.«2508.10245».Geode5Proof

private def smokePrime : ℕ := 576460752303404051
private def smokeResidue : ℕ := 464097493913787811

private theorem smokePrime_prime : Nat.Prime smokePrime := by
  native_decide

local instance : Fact smokePrime.Prime := ⟨smokePrime_prime⟩

set_option maxHeartbeats 0 in
theorem smoke_denominator_nonzero :
    modularDenominator smokePrime 1000 ≠ 0 := by
  native_decide

set_option maxHeartbeats 0 in
theorem smoke_residue :
    modularGeode smokePrime 1000 = (smokeResidue : ZMod smokePrime) := by
  native_decide

/-- The smoke residue is a genuine congruence of the original benchmark. -/
theorem smoke_original_congruence :
    (geode5Diagonal 1000 : ZMod smokePrime) =
      (smokeResidue : ZMod smokePrime) := by
  rw [← modularGeode_eq_cast smokePrime 1000 smoke_denominator_nonzero]
  exact smoke_residue

#print axioms smoke_original_congruence

end Arxiv.«2508.10245».Geode5Proof
