/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import FormalConjecturesUtil

namespace WrittenOnTheWallII.GraphConjecture2Audit

open Classical Finset SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- Leaves of a spanning tree represented on the original vertex type. -/
noncomputable def treeLeaves
    (T : SimpleGraph α) [DecidableRel T.Adj] : Finset α :=
  Finset.univ.filter fun v => T.degree v = 1

/-- Any tree contained in `G` gives a legitimate witness in the supremum that
defines `Ls G`. -/
lemma treeLeaves_card_le_Ls
    (G T : SimpleGraph α) [DecidableRel G.Adj] [DecidableRel T.Adj]
    (hTG : T ≤ G) (hT : T.IsTree) :
    ((treeLeaves T).card : ℝ) ≤ Ls G := by
  let S : G.Subgraph := T.toSubgraph G hTG
  have hSspan : S.IsSpanning := SimpleGraph.toSubgraph.isSpanning T hTG
  have hScoe : S.coe.IsTree := by
    have hSpanTree : S.spanningCoe.IsTree := by
      simpa [S] using hT
    exact (SimpleGraph.Iso.isTree_iff
      (S.spanningCoeEquivCoeOfSpanning hSspan)).mp hSpanTree
  unfold Ls
  apply le_csSup
  · refine ⟨(Fintype.card α : ℝ), ?_⟩
    rintro z ⟨U, _hU, rfl⟩
    exact_mod_cast
      (U.verts.toFinset.filter (fun v => U.degree v = 1)).card_le_univ
  · refine ⟨S, ⟨hSspan, hScoe⟩, ?_⟩
    simp [treeLeaves, S, SimpleGraph.toSubgraph]

#print axioms treeLeaves_card_le_Ls

end WrittenOnTheWallII.GraphConjecture2Audit
