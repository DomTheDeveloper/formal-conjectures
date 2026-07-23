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

import Mathlib

/-!
# Sound strategy certificates for finite ranked games

This file provides the kernel-side theorem needed by the Chomp computation.  A set of positions is
certified losing when every legal opponent move has a legal reply back into the set.  The game rank
strictly decreases on every move, so the certificate is sound by strong induction.
-/

namespace ChompStrategyCertificate

/-- A game equipped with a natural-number rank that strictly decreases after every legal move. -/
structure RankedGame where
  State : Type
  move : State → State → Prop
  rank : State → ℕ
  move_rank_lt : ∀ {p q}, move p q → rank q < rank p

namespace RankedGame

variable (G : RankedGame)

mutual
  /-- The player to move has a move to a losing position. -/
  inductive Winning : G.State → Prop where
    | move {p q : G.State} : G.move p q → Losing q → Winning p

  /-- Every legal move leads to a winning position. -/
  inductive Losing : G.State → Prop where
    | all {p : G.State} : (∀ q, G.move p q → Winning q) → Losing p
end

/-- A reply-closed set: after every move from a certified position, there is a reply in the set. -/
def ReplyClosed (S : G.State → Prop) : Prop :=
  ∀ ⦃p⦄, S p → ∀ ⦃q⦄, G.move p q → ∃ r, G.move q r ∧ S r

/-- Every member of a reply-closed set is a losing position. -/
theorem losing_of_replyClosed {S : G.State → Prop} (hS : G.ReplyClosed S) :
    ∀ p, S p → G.Losing p := by
  intro p hp
  induction h : G.rank p using Nat.strong_induction_on generalizing p with
  | h n ih =>
      apply Losing.all
      intro q hpq
      obtain ⟨r, hqr, hr⟩ := hS hp hpq
      apply Winning.move hqr
      apply ih (G.rank r)
      · rw [← h]
        exact (G.move_rank_lt hqr).trans (G.move_rank_lt hpq)
      · rfl
      · exact hr

end RankedGame

end ChompStrategyCertificate
