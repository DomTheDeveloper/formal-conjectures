/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.MaximumLeafDegree

/-!
# Explicit spanning-tree witnesses for lower bounds on `Ls`
-/

namespace SimpleGraph.C217LeafWitness

open Classical
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every valid spanning-tree witness contributes its leaf count to the
supremum defining `Ls`. -/
theorem leafCount_cast_le_Ls_of_spanningTree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : G.Subgraph)
    (hspan : T.IsSpanning)
    (htree : T.IsTree)
    (hle : T ≤ G.toSubgraph) :
    (T.leafCount : ℝ) ≤ Ls G := by
  let A : Set ℝ :=
    {x | ∃ S : G.Subgraph,
      S.IsSpanning ∧ S.IsTree ∧ S ≤ G.toSubgraph ∧ x = (S.leafCount : ℝ)}
  have hnonempty : A.Nonempty := by
    refine ⟨(T.leafCount : ℝ), T, hspan, htree, hle, rfl⟩
  have hbound : BddAbove A := by
    refine ⟨(Fintype.card V : ℝ), ?_⟩
    intro x hx
    rcases hx with ⟨S, _, _, _, rfl⟩
    exact_mod_cast (S.leafCount_le_card_verts.trans_eq hspan.card_verts)
  change (T.leafCount : ℝ) ≤ sSup A
  apply le_csSup hbound
  exact ⟨T, hspan, htree, hle, rfl⟩

#print axioms SimpleGraph.C217LeafWitness.leafCount_cast_le_Ls_of_spanningTree

end SimpleGraph.C217LeafWitness
