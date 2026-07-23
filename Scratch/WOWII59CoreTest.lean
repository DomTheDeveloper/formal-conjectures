import FormalConjecturesUtil

/-!
# Reduced finite certificate for WOWII Conjecture 59

Only vertices `0,…,10` lie on cycles in the explicit counterexample. This module
checks that every seven-vertex subset of that core contains one of the 25 fixed
cycle witnesses.
-/

namespace WOWII59CoreTest

open Finset

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Cycle-bearing vertices are exactly the core `0,…,10`; checking its 2,048
subsets is sufficient for the large-subset certificate. -/
private def Contains3 (s : Finset (Fin 11)) (a b c : Fin 11) : Prop :=
  a ∈ s ∧ b ∈ s ∧ c ∈ s

private def Contains4 (s : Finset (Fin 11)) (a b c d : Fin 11) : Prop :=
  a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ d ∈ s

private def Contains6 (s : Finset (Fin 11)) (a b c d e f : Fin 11) : Prop :=
  a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ d ∈ s ∧ e ∈ s ∧ f ∈ s

private theorem core_cycle_cover :
    ∀ s : Finset (Fin 11), 7 ≤ s.card →
      Contains3 s 4 7 10 ∨
      Contains4 s 1 5 3 8 ∨
      Contains3 s 0 9 10 ∨
      Contains4 s 2 6 4 9 ∨
      Contains3 s 2 6 10 ∨
      Contains4 s 1 6 3 7 ∨
      Contains4 s 0 5 2 9 ∨
      Contains4 s 1 5 4 6 ∨
      Contains4 s 3 7 4 9 ∨
      Contains4 s 0 5 3 8 ∨
      Contains3 s 1 8 10 ∨
      Contains3 s 3 5 10 ∨
      Contains4 s 0 8 3 9 ∨
      Contains4 s 0 5 1 8 ∨
      Contains4 s 3 6 4 7 ∨
      Contains4 s 1 6 4 7 ∨
      Contains4 s 1 5 4 7 ∨
      Contains4 s 1 6 3 8 ∨
      Contains4 s 1 5 2 6 ∨
      Contains6 s 0 8 1 6 2 9 ∨
      Contains4 s 2 6 3 9 ∨
      Contains4 s 2 5 4 6 ∨
      Contains4 s 1 7 3 8 ∨
      Contains6 s 0 8 1 7 4 9 ∨
      Contains4 s 0 5 4 9 := by
  decide

#print axioms core_cycle_cover

end WOWII59CoreTest
