/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import ProofAudit.«2_double_star»

namespace WrittenOnTheWallII.GraphConjecture2Audit

open Classical Finset SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

lemma doubleStarSeed_adj_first
    (G : SimpleGraph α) [DecidableRel G.Adj] (x y : α) {z : α}
    (hz : z ∈ G.neighborFinset x) :
    (doubleStarSeed G x y).Adj x z := by
  let Hx := attachLeaves (⊥ : SimpleGraph α) x (firstLeaves G x)
  have hxzAdj : G.Adj x z := (G.mem_neighborFinset x z).1 hz
  have hxz : Hx.Adj x z := by
    apply attachLeaves_adj_of_mem
    · exact G.ne_of_adj hxzAdj
    · simpa [firstLeaves] using hz
  exact (base_le_attachLeaves Hx y (secondLeaves G x y)) hxz

lemma doubleStarSeed_adj_second_sdiff
    (G : SimpleGraph α) [DecidableRel G.Adj] (x y : α) {z : α}
    (hz : z ∈ G.neighborFinset y \ G.neighborFinset x) :
    (doubleStarSeed G x y).Adj y z := by
  have hzparts := Finset.mem_sdiff.mp hz
  have hzy : z ∈ G.neighborFinset y := hzparts.1
  have hznotx : z ∉ G.neighborFinset x := hzparts.2
  by_cases hzx : z = x
  · subst z
    have hyx : G.Adj y x := (G.mem_neighborFinset y x).1 hzy
    have hyNx : y ∈ G.neighborFinset x :=
      (G.mem_neighborFinset x y).2 hyx.symm
    exact (doubleStarSeed_adj_first G x y hyNx).symm
  · have hzLy : z ∈ secondLeaves G x y := by
      simp [secondLeaves, hzy, hznotx, hzx]
    have hyz : G.Adj y z := (G.mem_neighborFinset y z).1 hzy
    exact attachLeaves_adj_of_mem
      (attachLeaves (⊥ : SimpleGraph α) x (firstLeaves G x))
      y (secondLeaves G x y) (G.ne_of_adj hyz) hzLy

lemma degree_le_degree_of_doubleStarSeed_le
    (G T : SimpleGraph α) [DecidableRel G.Adj] [DecidableRel T.Adj]
    (x y : α) (hseed : doubleStarSeed G x y ≤ T) :
    G.degree x ≤ T.degree x := by
  rw [← G.card_neighborFinset_eq_degree, ← T.card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro z hz
  have hTadj : T.Adj x z := hseed (doubleStarSeed_adj_first G x y hz)
  simpa using hTadj

lemma card_sdiff_le_degree_of_doubleStarSeed_le
    (G T : SimpleGraph α) [DecidableRel G.Adj] [DecidableRel T.Adj]
    (x y : α) (hseed : doubleStarSeed G x y ≤ T) :
    (G.neighborFinset y \ G.neighborFinset x).card ≤ T.degree y := by
  rw [← T.card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro z hz
  have hTadj : T.Adj y z := hseed (doubleStarSeed_adj_second_sdiff G x y hz)
  simpa using hTadj

lemma neighbor_union_card_le_degree_sum_of_doubleStarSeed_le
    (G T : SimpleGraph α) [DecidableRel G.Adj] [DecidableRel T.Adj]
    (x y : α) (hseed : doubleStarSeed G x y ≤ T) :
    (G.neighborFinset x ∪ G.neighborFinset y).card ≤
      T.degree x + T.degree y := by
  have hx := degree_le_degree_of_doubleStarSeed_le G T x y hseed
  have hy := card_sdiff_le_degree_of_doubleStarSeed_le G T x y hseed
  have hdecomp :
      G.neighborFinset x ∪ G.neighborFinset y =
        G.neighborFinset x ∪ (G.neighborFinset y \ G.neighborFinset x) := by
    ext z
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  have hdisj : Disjoint (G.neighborFinset x)
      (G.neighborFinset y \ G.neighborFinset x) := by
    rw [Finset.disjoint_left]
    intro z hzx hz
    exact (Finset.mem_sdiff.mp hz).2 hzx
  calc
    (G.neighborFinset x ∪ G.neighborFinset y).card =
        (G.neighborFinset x ∪ (G.neighborFinset y \ G.neighborFinset x)).card := by
          rw [hdecomp]
    _ = (G.neighborFinset x).card +
        (G.neighborFinset y \ G.neighborFinset x).card :=
      Finset.card_union_of_disjoint hdisj
    _ ≤ T.degree x + T.degree y := Nat.add_le_add hx hy

#print axioms doubleStarSeed_adj_first
#print axioms doubleStarSeed_adj_second_sdiff
#print axioms neighbor_union_card_le_degree_sum_of_doubleStarSeed_le

end WrittenOnTheWallII.GraphConjecture2Audit
