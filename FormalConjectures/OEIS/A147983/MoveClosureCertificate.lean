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

import FormalConjectures.OEIS.A147983.StrategyCertificate

/-!
# Factored symbolic move-closure certificate

For decision diagrams it is convenient to represent the one-move image of the losing language and
the language of positions having a move back to the losing language separately. One inclusion
between those languages then gives the closed response strategy required by the final proof.
-/

namespace OeisA147983

/-- A factored certificate for closure of a proposed losing set under two-ply responses. -/
structure MoveClosureCertificate where
  losingSet : List ℕ → Prop
  postSet : List ℕ → Prop
  preSet : List ℕ → Prop
  move_to_post : ∀ {p q}, losingSet p → Move p q → postSet q
  post_to_pre : ∀ {q}, postSet q → preSet q
  pre_has_reply : ∀ {q}, preSet q → ∃ r, Move q r ∧ losingSet r
  child₁_mem : losingSet child₁
  child₂_mem : losingSet child₂
  child₃_mem : losingSet child₃

namespace MoveClosureCertificate

/-- The factored move-language obligations produce a closed response strategy. -/
def strategy (C : MoveClosureCertificate) : StrategyCertificate where
  carrier := {p | C.losingSet p}
  reply := by
    intro p hp q hpq
    have hpost : C.postSet q := C.move_to_post hp hpq
    have hpre : C.preSet q := C.post_to_pre hpost
    obtain ⟨r, hqr, hr⟩ := C.pre_has_reply hpre
    exact ⟨r, hr, hqr⟩
  child₁_mem := C.child₁_mem
  child₂_mem := C.child₂_mem
  child₃_mem := C.child₃_mem

/-- A complete move-closure certificate proves the exact three-opening statement. -/
theorem three_openings (C : MoveClosureCertificate) :
    IsWinningOpening rectangle child₁ ∧
      IsWinningOpening rectangle child₂ ∧
      IsWinningOpening rectangle child₃ ∧
      child₁ ≠ child₂ ∧ child₁ ≠ child₃ ∧ child₂ ≠ child₃ :=
  C.strategy.three_openings

end MoveClosureCertificate
end OeisA147983