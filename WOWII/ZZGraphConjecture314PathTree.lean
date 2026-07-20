/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import WOWII.ZZGraphConjecture314DominatingEdge

/-!
Generic path-to-tree lemmas used by the induced-`P₅` bridge for WOWII Graph
Conjecture 314. They are included here directly so the proof does not depend
on any other conjecture statement or proof module.
-/

namespace WrittenOnTheWallII.GraphConjecture314

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma path_toSubgraph_spanningCoe_isAcyclic
    {G : SimpleGraph α} {u v : α} {p : G.Walk u v}
    (hp : p.IsPath) : p.toSubgraph.spanningCoe.IsAcyclic := by
  induction p with
  | nil =>
      change (⊥ : SimpleGraph α).IsAcyclic
      exact isAcyclic_bot
  | @cons u v w huv p ih =>
      rw [Walk.cons_isPath_iff] at hp
      have ihA := ih hp.1
      have hu_not : u ∉ p.toSubgraph.verts := by
        simpa [Walk.mem_verts_toSubgraph] using hp.2
      have hnreach : ¬p.toSubgraph.spanningCoe.Reachable u v := by
        rintro ⟨q⟩
        have hq : ¬q.Nil := Walk.not_nil_of_ne huv.ne
        have hadj := q.adj_snd hq
        exact hu_not (p.toSubgraph.edge_vert hadj)
      have hadd :=
        (isAcyclic_add_edge_iff_of_not_reachable u v hnreach).2 ihA
      simpa [Walk.toSubgraph, sup_comm] using hadd

lemma path_toSubgraph_isTree
    {G : SimpleGraph α} {u v : α} {p : G.Walk u v}
    (hp : p.IsPath) : p.toSubgraph.coe.IsTree := by
  refine ⟨p.toSubgraph_connected.coe, ?_⟩
  let f : p.toSubgraph.coe →g p.toSubgraph.spanningCoe :=
    ⟨Subtype.val, fun h => h⟩
  exact IsAcyclic.comap f Subtype.val_injective
    (path_toSubgraph_spanningCoe_isAcyclic hp)

end WrittenOnTheWallII.GraphConjecture314
