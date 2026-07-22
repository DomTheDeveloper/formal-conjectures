/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import ProofAudit.«160_local_structure»

namespace WrittenOnTheWallII.GraphConjecture160Audit

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- In a graph with no four-cycle, any two distinct vertices have at most one
common neighbor. -/
lemma common_neighbors_subsingleton_of_ne
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hC4 : NoFourCycle G) {u v : α} (huv : u ≠ v) :
    (G.neighborSet u ∩ G.neighborSet v).Subsingleton := by
  intro p hp q hq
  by_contra hpq
  apply hC4
  let c : G.Walk p p :=
    .cons hp.1.symm (.cons hq.1 (.cons hq.2.symm (.cons hp.2 .nil)))
  refine ⟨p, c, ?_, by simp [c]⟩
  simp [Walk.isCycle_def, c, Sym2.eq_iff, hpq, huv,
    hp.1.ne, hp.2.ne, hq.1.ne, hq.2.ne]

lemma common_neighborFinset_card_le_one
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hC4 : NoFourCycle G) {u v : α} (huv : u ≠ v) :
    (G.neighborFinset u ∩ G.neighborFinset v).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro p hp q hq
  exact common_neighbors_subsingleton_of_ne G hC4 huv
    (by simpa using hp) (by simpa using hq)

#print axioms common_neighbors_subsingleton_of_ne
#print axioms common_neighborFinset_card_le_one

end WrittenOnTheWallII.GraphConjecture160Audit
