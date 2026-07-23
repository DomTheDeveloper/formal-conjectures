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

import FormalConjectures.OEIS.A147983.ClosedResponseSet
import FormalConjectures.OEIS.A147983.ChompRank

/-!
# Closed response strategies for the 10 × 42 Chomp witness

It is unnecessary to classify every non-losing position. A set containing the three target roots
is enough when every legal opponent move from the set has a legal reply back into the set. Chomp
area strictly decreases across the two moves, so the response strategy terminates and proves each
root losing.
-/

namespace OeisA147983

/-- A symbolic second-player strategy closed under every opponent move. -/
structure StrategyCertificate where
  carrier : Set (List ℕ)
  reply : ∀ ⦃p⦄, p ∈ carrier → ∀ ⦃q⦄, Move p q →
    ∃ r ∈ carrier, Move q r
  child₁_mem : child₁ ∈ carrier
  child₂_mem : child₂ ∈ carrier
  child₃_mem : child₃ ∈ carrier

namespace StrategyCertificate

/-- Turn a closed symbolic strategy into the generic well-founded response certificate. -/
def closedResponseSet (C : StrategyCertificate) :
    KernelCertificate.ClosedResponseSet Move List.sum where
  carrier := C.carrier
  reply := by
    intro p hp q hpq
    obtain ⟨r, hr, hqr⟩ := C.reply hp hpq
    refine ⟨r, hr, hqr, ?_⟩
    exact lt_trans (move_sum_lt hqr) (move_sum_lt hpq)

/-- A closed response strategy proves the exact three-opening statement. -/
@[category API, AMS 5]
theorem three_openings (C : StrategyCertificate) :
    IsWinningOpening rectangle child₁ ∧
      IsWinningOpening rectangle child₂ ∧
      IsWinningOpening rectangle child₃ ∧
      child₁ ≠ child₂ ∧ child₁ ≠ child₃ ∧ child₂ ≠ child₃ := by
  apply three_openings_of_losing
  · exact (C.closedResponseSet).isLosing C.child₁_mem
  · exact (C.closedResponseSet).isLosing C.child₂_mem
  · exact (C.closedResponseSet).isLosing C.child₃_mem

end StrategyCertificate
end OeisA147983