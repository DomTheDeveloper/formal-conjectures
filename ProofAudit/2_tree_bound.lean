/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import ProofAudit.«2_double_star_degrees»
import ProofAudit.«2_tree_leaves»

namespace WrittenOnTheWallII.GraphConjecture2Audit

open Classical Finset SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- Every adjacent pair admits a spanning-tree witness with enough leaves to
cover the union of its two neighborhoods, up to the two centers. -/
lemma neighbor_union_card_le_Ls_add_two
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    {x y : α} (hxy : G.Adj x y) :
    ((G.neighborFinset x ∪ G.neighborFinset y).card : ℝ) ≤ Ls G + 2 := by
  obtain ⟨T, hseedT, hmax⟩ :=
    SimpleGraph.exists_maximal_isAcyclic_of_le_isAcyclic
      (G := G) (doubleStarSeed_le G x y) (doubleStarSeed_isAcyclic G x y)
  have hTG : T ≤ G := hmax.prop.1
  have hT : T.IsTree :=
    (hG.maximal_le_isAcyclic_iff_isTree hTG).mp hmax
  letI : DecidableRel T.Adj := Classical.decRel T.Adj
  have hUnionNat :=
    neighbor_union_card_le_degree_sum_of_doubleStarSeed_le G T x y hseedT
  have hUnion :
      ((G.neighborFinset x ∪ G.neighborFinset y).card : ℝ) ≤
        (T.degree x : ℝ) + T.degree y := by
    exact_mod_cast hUnionNat
  have hLeafInt := two_degrees_sub_two_le_treeLeaves T hT hxy.ne
  have hLeaf :
      (T.degree x : ℝ) + T.degree y - 2 ≤ ((treeLeaves T).card : ℝ) := by
    exact_mod_cast hLeafInt
  have hLs : ((treeLeaves T).card : ℝ) ≤ Ls G :=
    treeLeaves_card_le_Ls G T hTG hT
  linarith

#print axioms neighbor_union_card_le_Ls_add_two

end WrittenOnTheWallII.GraphConjecture2Audit
