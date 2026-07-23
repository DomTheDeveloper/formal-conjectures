import FormalConjecturesUtil

namespace WOWII59FiniteTest

open Classical SimpleGraph Finset

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private def counterG : SimpleGraph (Fin 18) where
  Adj u v :=
    u ≠ v ∧
      (u.val = 10 ∨ v.val = 10 ∨
        (u.val = 0 ∧ (v.val = 5 ∨ v.val = 8 ∨ v.val = 9)) ∨
        (v.val = 0 ∧ (u.val = 5 ∨ u.val = 8 ∨ u.val = 9)) ∨
        (u.val = 1 ∧ (v.val = 5 ∨ v.val = 6 ∨ v.val = 7 ∨ v.val = 8)) ∨
        (v.val = 1 ∧ (u.val = 5 ∨ u.val = 6 ∨ u.val = 7 ∨ u.val = 8)) ∨
        (u.val = 2 ∧ (v.val = 5 ∨ v.val = 6 ∨ v.val = 9)) ∨
        (v.val = 2 ∧ (u.val = 5 ∨ u.val = 6 ∨ u.val = 9)) ∨
        (u.val = 3 ∧ (v.val = 5 ∨ v.val = 6 ∨ v.val = 7 ∨ v.val = 8 ∨ v.val = 9)) ∨
        (v.val = 3 ∧ (u.val = 5 ∨ u.val = 6 ∨ u.val = 7 ∨ u.val = 8 ∨ u.val = 9)) ∨
        (u.val = 4 ∧ (v.val = 5 ∨ v.val = 6 ∨ v.val = 7 ∨ v.val = 9)) ∨
        (v.val = 4 ∧ (u.val = 5 ∨ u.val = 6 ∨ u.val = 7 ∨ u.val = 9)))
  symm u v h := ⟨h.1.symm, by tauto⟩
  loopless u h := h.1 rfl

private instance : DecidableRel counterG.Adj := fun u v => by
  unfold counterG
  infer_instance

private theorem residue_test : residue counterG = 10 := by
  unfold residue
  change residueAux [17, 6, 6, 5, 5, 5, 5, 4, 4, 4, 4, 1, 1, 1, 1, 1, 1, 1] = 10
  decide

private def Contains3 (s : Finset (Fin 18)) (a b c : Fin 18) : Prop :=
  a ∈ s ∧ b ∈ s ∧ c ∈ s

private def Contains4 (s : Finset (Fin 18)) (a b c d : Fin 18) : Prop :=
  a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ d ∈ s

private def Contains6 (s : Finset (Fin 18)) (a b c d e f : Fin 18) : Prop :=
  a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ d ∈ s ∧ e ∈ s ∧ f ∈ s

private theorem cycle_cover_test :
    ∀ s : Finset (Fin 18), 14 ≤ s.card →
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
  letI : DecidablePred (fun s : Finset (Fin 18) =>
      14 ≤ s.card →
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
        Contains4 s 0 5 4 9) := by
    intro s
    infer_instance
  exact of_decide_eq_true rfl

universe u

private theorem application_test
    (hP : ∀ (α : Type u) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) [DecidableRel G.Adj] (_h : G.Connected), True) : True := by
  have h := hP (Fin 18) counterG
  trivial

#print axioms residue_test
#print axioms cycle_cover_test
#print axioms application_test

end WOWII59FiniteTest
