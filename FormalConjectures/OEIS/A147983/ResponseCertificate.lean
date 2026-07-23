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
# Two-ply losing-position certificates

A Chomp P-position certificate does not need to store the intermediate N-positions. It stores
only losing positions and, for every opponent move, a legal reply leading to another stored
losing position. The certificate producer remains untrusted; `reply_sound` is the proof boundary
checked by Lean.
-/

namespace OeisA147983.KernelCertificate
namespace RankedGame

variable {P : Type} {G : RankedGame P} {n : ℕ}

/-- A compressed second-player strategy containing only losing positions. -/
structure ResponseCertificate (G : RankedGame P) (n : ℕ) where
  pos : Fin n → P
  replyIndex : Fin n → P → Fin n
  reply_sound : ∀ (i : Fin n) (q : P), G.Move (pos i) q →
    G.Move q (pos (replyIndex i q))

namespace ResponseCertificate

/-- Every stored position in a sound two-ply response certificate is genuinely losing. -/
@[category API, AMS 5]
theorem outcome (C : ResponseCertificate G n) (i : Fin n) :
    Outcome G.Move (C.pos i) false := by
  have all : ∀ k : ℕ, ∀ i : Fin n, G.rank (C.pos i) = k →
      Outcome G.Move (C.pos i) false := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro i hrank
        exact Outcome.losing (fun q hq ↦ by
          let j := C.replyIndex i q
          have hreply : G.Move q (C.pos j) := C.reply_sound i q hq
          have hq_lt : G.rank q < k := by
            simpa [← hrank] using G.decreases hq
          have hj_lt_q : G.rank (C.pos j) < G.rank q := G.decreases hreply
          have hj_lt : G.rank (C.pos j) < k := lt_trans hj_lt_q hq_lt
          exact Outcome.winning hreply (ih _ hj_lt j rfl))
  exact all _ i rfl

/-- Every stored position has a kernel-checked losing proof. -/
@[category API, AMS 5]
theorem isLosing (C : ResponseCertificate G n) (i : Fin n) :
    IsLosing G.Move (C.pos i) :=
  ⟨C.outcome i⟩

end ResponseCertificate
end RankedGame
end OeisA147983.KernelCertificate