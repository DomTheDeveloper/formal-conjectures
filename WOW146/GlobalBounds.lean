/-
Copyright 2026 The WOW-146 Authors.
Licensed under the Apache License, Version 2.0.
-/

import WOW146.GraphSquareRadius
import FormalConjecturesForMathlib.WrittenOnTheWallII.GraphConjecture142Proof
import Mathlib.Combinatorics.SimpleGraph.Hasse

namespace SimpleGraph

open Classical
variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
variable {G : SimpleGraph α}

omit [Fintype α] [Nontrivial α] in
lemma Walk.induce_support_toFinset_isTree_of_length_eq_dist
    {u v : α} (p : G.Walk u v) (hp : p.length = G.dist u v) :
    (G.induce (p.support.toFinset : Set α)).IsTree := by
  induction p with
  | @nil u =>
      have hset :
          (↑(Walk.nil : G.Walk u u).support.toFinset : Set α) = {u} := by
        ext x
        simp
      rw [hset]
      letI : Nonempty ↥({u} : Set α) := ⟨⟨u, by simp⟩⟩
      letI : Subsingleton ↥({u} : Set α) := ⟨fun a b => by
        apply Subtype.ext
        simpa only [Set.mem_singleton_iff] using a.property.trans b.property.symm⟩
      exact IsTree.of_subsingleton
  | @cons u v w huv p ih =>
      have hptail : p.length = G.dist v w :=
        length_eq_dist_of_subwalk hp (Walk.isSubwalk_cons p huv)
      have htree := ih hptail
      have hfullPath := (p.cons huv).isPath_of_length_eq_dist hp
      have huNot : u ∉ p.support.toFinset := by
        simpa using (List.nodup_cons.mp hfullPath.support_nodup).1
      have huniq : ∀ ⦃b : α⦄, b ∈ p.support.toFinset → G.Adj u b → b = v := by
        intro b hb hub
        have hbSupport : b ∈ (p.cons huv).support := by
          simp only [Walk.support_cons, List.mem_cons]
          exact Or.inr (by simpa using hb)
        have hedge := (p.cons huv).chordless_of_length_eq_dist hp
          (by simp) hbSupport hub
        simpa using hfullPath.eq_snd_of_mem_edges hedge
      have hsupp : (Walk.cons huv p).support.toFinset =
          insert u p.support.toFinset := by simp
      rw [hsupp]
      exact htree.induce_insert_of_unique_adj huNot (by simp) huv huniq

omit [DecidableEq α] [Nontrivial α] in
lemma finset_card_le_largestInducedTreeSize {s : Finset α}
    (hs : (G.induce (s : Set α)).IsTree) :
    s.card ≤ largestInducedTreeSize G :=
  hs.card_le_largestInducedTreeSize_splice

lemma diam_succ_le_largestInducedTreeSize (hG : G.Connected) :
    G.diam + 1 ≤ largestInducedTreeSize G :=
  diam_add_one_le_largestInducedTreeSize_splice hG

omit [DecidableEq α] in
lemma eccSet_periphery_add_one_le_diam (hG : G.Connected) :
    eccSet G (maxEccentricityVertices G : Set α) + 1 ≤ G.diam := by
  by_cases hp : eccSet G (maxEccentricityVertices G : Set α) = 0
  · have hd : G.diam ≠ 0 := (connected_iff_diam_ne_zero).mp hG
    omega
  · exact eccSet_maxEccentricityVertices_add_one_le_diam_splice hG
      (Nat.pos_of_ne_zero hp)

#print axioms Walk.induce_support_toFinset_isTree_of_length_eq_dist
#print axioms diam_succ_le_largestInducedTreeSize
#print axioms eccSet_periphery_add_one_le_diam

end SimpleGraph
