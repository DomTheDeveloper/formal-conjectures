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

import FormalConjectures.OEIS.A147983.ChompRank

/-!
# Certified P-sets give genuine normal-play outcomes

For a progressively bounded game, a predicate is the losing-position predicate when no member can
move to another member and every nonmember has a legal move to a member. These two laws are enough
for Lean to construct the complete normal-play outcome proof by strong induction on the game rank.
-/

namespace OeisA147983.KernelCertificate
namespace RankedGame

variable {P : Type} {G : RankedGame P}

/-- A predicate satisfying the two P-position laws produces genuine losing and winning proofs. -/
theorem outcomes_of_pSet
    (S : P → Prop)
    (noMove : ∀ {p : P}, S p → ∀ q, G.Move p q → ¬ S q)
    (hasReply : ∀ {p : P}, ¬ S p → ∃ q, G.Move p q ∧ S q) :
    ∀ p : P, (S p → Outcome G.Move p false) ∧ (¬ S p → Outcome G.Move p true) := by
  intro p
  have all : ∀ k : ℕ, ∀ p : P, G.rank p = k →
      (S p → Outcome G.Move p false) ∧ (¬ S p → Outcome G.Move p true) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro p hrank
        constructor
        · intro hp
          exact Outcome.losing (fun q hmove ↦ by
            have hnq : ¬ S q := noMove hp q hmove
            have hlt : G.rank q < k := by
              simpa [← hrank] using G.decreases hmove
            exact (ih _ hlt q rfl).2 hnq)
        · intro hnp
          obtain ⟨q, hmove, hq⟩ := hasReply hnp
          have hlt : G.rank q < k := by
            simpa [← hrank] using G.decreases hmove
          exact Outcome.winning hmove ((ih _ hlt q rfl).1 hq)
  exact all _ p rfl

/-- Membership in a certified P-set gives a kernel-checked losing proof. -/
theorem losing_of_pSet
    (S : P → Prop)
    (noMove : ∀ {p : P}, S p → ∀ q, G.Move p q → ¬ S q)
    (hasReply : ∀ {p : P}, ¬ S p → ∃ q, G.Move p q ∧ S q)
    {p : P} (hp : S p) : IsLosing G.Move p := by
  exact ⟨(outcomes_of_pSet S noMove hasReply p).1 hp⟩

/-- Nonmembership in a certified P-set gives a kernel-checked winning proof. -/
theorem winning_of_not_pSet
    (S : P → Prop)
    (noMove : ∀ {p : P}, S p → ∀ q, G.Move p q → ¬ S q)
    (hasReply : ∀ {p : P}, ¬ S p → ∃ q, G.Move p q ∧ S q)
    {p : P} (hp : ¬ S p) : IsWinning G.Move p := by
  exact ⟨(outcomes_of_pSet S noMove hasReply p).2 hp⟩

end RankedGame
end OeisA147983.KernelCertificate