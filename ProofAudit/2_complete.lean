/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import ProofAudit.«2_average_pair»
import ProofAudit.«2_tree_bound»

namespace WrittenOnTheWallII.GraphConjecture2Audit

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- Complete proof of the exact current WOWII Conjecture 2 statement. -/
theorem conjecture2_complete
    (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    2 * (averageIndepNeighbors G - 1) ≤ Ls G := by
  obtain ⟨x, y, hxy, hAvg⟩ :=
    exists_adjacent_neighbor_union_ge_two_average G h
  have hTree := neighbor_union_card_le_Ls_add_two G h hxy
  linarith

#print axioms conjecture2_complete

end WrittenOnTheWallII.GraphConjecture2Audit
