import FormalConjecturesUtil

/-!
# Reduced finite certificate for WOWII Conjecture 59

Only vertices `0,…,10` lie on cycles in the explicit counterexample. This module
checks that every seven-vertex subset of that core contains one of the 25 fixed
cycle witnesses. The finite decision procedure ranges over the `2^11` Boolean
indicator functions, avoiding any classical enumeration of all finsets.
-/

namespace WOWII59CoreTest

open Finset

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private def Contains3 (s : Finset (Fin 11)) (a b c : Fin 11) : Prop :=
  a ∈ s ∧ b ∈ s ∧ c ∈ s

private def Contains4 (s : Finset (Fin 11)) (a b c d : Fin 11) : Prop :=
  a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ d ∈ s

private def Contains6 (s : Finset (Fin 11)) (a b c d e f : Fin 11) : Prop :=
  a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ d ∈ s ∧ e ∈ s ∧ f ∈ s

private def BContains3 (x : Fin 11 → Bool) (a b c : Fin 11) : Prop :=
  x a = true ∧ x b = true ∧ x c = true

private def BContains4 (x : Fin 11 → Bool) (a b c d : Fin 11) : Prop :=
  x a = true ∧ x b = true ∧ x c = true ∧ x d = true

private def BContains6 (x : Fin 11 → Bool) (a b c d e f : Fin 11) : Prop :=
  x a = true ∧ x b = true ∧ x c = true ∧ x d = true ∧ x e = true ∧ x f = true

private def CoreProp (x : Fin 11 → Bool) : Prop :=
  7 ≤ (Finset.univ.filter fun v => x v = true).card →
    BContains3 x 4 7 10 ∨
    BContains4 x 1 5 3 8 ∨
    BContains3 x 0 9 10 ∨
    BContains4 x 2 6 4 9 ∨
    BContains3 x 2 6 10 ∨
    BContains4 x 1 6 3 7 ∨
    BContains4 x 0 5 2 9 ∨
    BContains4 x 1 5 4 6 ∨
    BContains4 x 3 7 4 9 ∨
    BContains4 x 0 5 3 8 ∨
    BContains3 x 1 8 10 ∨
    BContains3 x 3 5 10 ∨
    BContains4 x 0 8 3 9 ∨
    BContains4 x 0 5 1 8 ∨
    BContains4 x 3 6 4 7 ∨
    BContains4 x 1 6 4 7 ∨
    BContains4 x 1 5 4 7 ∨
    BContains4 x 1 6 3 8 ∨
    BContains4 x 1 5 2 6 ∨
    BContains6 x 0 8 1 6 2 9 ∨
    BContains4 x 2 6 3 9 ∨
    BContains4 x 2 5 4 6 ∨
    BContains4 x 1 7 3 8 ∨
    BContains6 x 0 8 1 7 4 9 ∨
    BContains4 x 0 5 4 9

private theorem core_bool_cover : ∀ x : Fin 11 → Bool, CoreProp x := by
  letI : DecidablePred CoreProp := fun x => by
    unfold CoreProp BContains3 BContains4 BContains6
    infer_instance
  letI : Decidable (∀ x : Fin 11 → Bool, CoreProp x) :=
    Fintype.decidableForallFintype
  decide

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
  intro s hs
  let x : Fin 11 → Bool := fun v => decide (v ∈ s)
  have hfilter : (Finset.univ.filter fun v => x v = true) = s := by
    ext v
    simp [x]
  have hx : 7 ≤ (Finset.univ.filter fun v => x v = true).card := by
    simpa [hfilter] using hs
  simpa [CoreProp, x, Contains3, Contains4, Contains6,
    BContains3, BContains4, BContains6] using core_bool_cover x hx

#print axioms core_bool_cover
#print axioms core_cycle_cover

end WOWII59CoreTest
