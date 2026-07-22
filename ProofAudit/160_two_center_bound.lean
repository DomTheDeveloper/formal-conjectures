/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import ProofAudit.«160_double_star»
import ProofAudit.«160_tree_bridge»

namespace WrittenOnTheWallII.GraphConjecture160Audit

open Classical SimpleGraph Finset

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

lemma neighbor_union_card_le_Ls_add_two160
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    {x y : α} (hxy : x ≠ y) :
    ((G.neighborFinset x ∪ G.neighborFinset y).card : ℝ) ≤ Ls G + 2 := by
  obtain ⟨T, hseedT, hTG, hT⟩ :=
    hG.exists_isTree_le_of_le_of_isAcyclic
      (twoCenterSeed_le G x y) (twoCenterSeed_isAcyclic G x y)
  letI : DecidableRel T.Adj := Classical.decRel T.Adj
  have hUnionNat := union_card_le_degree_sum_of_seed_le G T x y hseedT
  have hUnion :
      ((G.neighborFinset x ∪ G.neighborFinset y).card : ℝ) ≤
        (T.degree x : ℝ) + T.degree y := by
    exact_mod_cast hUnionNat
  have hLeafInt := two_degrees_sub_two_le_treeLeaves160 T hT hxy
  have hLeaf :
      (T.degree x : ℝ) + T.degree y - 2 ≤ ((treeLeaves160 T).card : ℝ) := by
    exact_mod_cast hLeafInt
  have hLs := treeLeaves160_card_le_Ls G T hTG hT
  linarith

#print axioms neighbor_union_card_le_Ls_add_two160

end WrittenOnTheWallII.GraphConjecture160Audit
