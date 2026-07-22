/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import FormalConjecturesUtil

namespace WrittenOnTheWallII.GraphConjecture160Audit

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- A graph has no (not necessarily induced) cycle of length four. -/
def NoFourCycle (G : SimpleGraph α) : Prop :=
  ¬ ∃ v : α, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = 4

/-- In a graph with no four-cycle, the endpoints of an edge have at most one
common neighbor. Two distinct common neighbors would give the cycle
`p-u-q-v-p`. -/
lemma common_neighbors_of_adj_subsingleton
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hC4 : NoFourCycle G) {u v : α} (huv : G.Adj u v) :
    (G.neighborSet u ∩ G.neighborSet v).Subsingleton := by
  intro p hp q hq
  by_contra hpq
  apply hC4
  let c : G.Walk p p :=
    .cons hp.1.symm (.cons hq.1 (.cons hq.2.symm (.cons hp.2 .nil)))
  refine ⟨p, c, ?_, by simp [c]⟩
  simp [Walk.isCycle_def, c, Sym2.eq_iff, hpq, huv.ne,
    hp.1.ne, hp.2.ne, hq.1.ne, hq.2.ne]

#print axioms common_neighbors_of_adj_subsingleton

end WrittenOnTheWallII.GraphConjecture160Audit
