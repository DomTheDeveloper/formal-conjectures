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

import FormalConjectures.OEIS.A147983.KernelCertificate

/-!
# Direct two-ply response certificates

This variant records the strict decrease of the selected two-ply response directly. Therefore the
certificate does not need a separate global proof that every possible game move decreases the
measure; the kernel checks exactly the moves used by the second-player strategy.
-/

namespace OeisA147983.KernelCertificate

variable {P : Type} {Move : P → P → Prop} {n : ℕ}

/-- A compressed losing-position certificate with a directly checked decreasing measure. -/
structure DirectResponseCertificate (Move : P → P → Prop) (n : ℕ) where
  pos : Fin n → P
  measure : P → ℕ
  replyIndex : Fin n → P → Fin n
  reply_sound : ∀ (i : Fin n) (q : P), Move (pos i) q →
    Move q (pos (replyIndex i q))
  reply_decreases : ∀ (i : Fin n) (q : P) (h : Move (pos i) q),
    measure (pos (replyIndex i q)) < measure (pos i)

namespace DirectResponseCertificate

/-- Every stored position is genuinely losing in the represented normal-play game. -/
@[category API, AMS 5]
theorem outcome (C : DirectResponseCertificate Move n) (i : Fin n) :
    Outcome Move (C.pos i) false := by
  have all : ∀ k : ℕ, ∀ i : Fin n, C.measure (C.pos i) = k →
      Outcome Move (C.pos i) false := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro i hrank
        exact Outcome.losing (fun q hq ↦ by
          let j := C.replyIndex i q
          have hreply : Move q (C.pos j) := C.reply_sound i q hq
          have hj_lt : C.measure (C.pos j) < k := by
            simpa [← hrank] using C.reply_decreases i q hq
          exact Outcome.winning hreply (ih _ hj_lt j rfl))
  exact all _ i rfl

/-- Every stored position has a kernel-checked losing proof. -/
@[category API, AMS 5]
theorem isLosing (C : DirectResponseCertificate Move n) (i : Fin n) :
    IsLosing Move (C.pos i) :=
  ⟨C.outcome i⟩

end DirectResponseCertificate
end OeisA147983.KernelCertificate