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

import FormalConjectures.OEIS.A147983.MDDCertificate

/-!
# Symbolic certificate interface for the 10 × 42 Chomp witness

A concrete decision-diagram checker only has to establish the two standard P-set laws and membership
of the three displayed roots. This file turns those finite symbolic obligations into the exact
three-opening theorem with no trusted external computation.
-/

namespace OeisA147983

/-- The complete mathematical interface required from a symbolic losing-set certificate. -/
structure SymbolicPSetCertificate where
  losingSet : List ℕ → Prop
  noMove : ∀ {p : List ℕ}, losingSet p → ∀ q, Move p q → ¬ losingSet q
  hasReply : ∀ {p : List ℕ}, ¬ losingSet p → ∃ q, Move p q ∧ losingSet q
  child₁_mem : losingSet child₁
  child₂_mem : losingSet child₂
  child₃_mem : losingSet child₃

namespace SymbolicPSetCertificate

/-- A complete symbolic P-set certificate proves the exact three-opening statement. -/
theorem three_openings (C : SymbolicPSetCertificate) :
    IsWinningOpening rectangle child₁ ∧
      IsWinningOpening rectangle child₂ ∧
      IsWinningOpening rectangle child₃ ∧
      child₁ ≠ child₂ ∧ child₁ ≠ child₃ ∧ child₂ ≠ child₃ := by
  apply three_openings_of_losing
  · exact KernelCertificate.RankedGame.losing_of_pSet
      (G := rankedGame) C.losingSet C.noMove C.hasReply C.child₁_mem
  · exact KernelCertificate.RankedGame.losing_of_pSet
      (G := rankedGame) C.losingSet C.noMove C.hasReply C.child₂_mem
  · exact KernelCertificate.RankedGame.losing_of_pSet
      (G := rankedGame) C.losingSet C.noMove C.hasReply C.child₃_mem

end SymbolicPSetCertificate
end OeisA147983