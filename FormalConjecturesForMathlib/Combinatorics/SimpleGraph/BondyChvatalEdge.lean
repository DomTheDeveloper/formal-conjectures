/-
Copyright (c) 2024 Shuhao Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuhao Song
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.BondyChvatalCrossing
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.BondyChvatalReroute
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# One-edge Bondy--Chvátal theorem

This is the source-level single-edge form needed for the WOWII Conjecture 217
traceability reduction.  It is adapted from Shuhao Song's unmerged Mathlib
Bondy--Chvátal development at
`c83689ab8f1abfba1f646e65dc8b131fd256b73f`.
-/

namespace SimpleGraph

open Classical Walk Function

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Deleting a genuinely new edge from `G ⊔ edge u v` recovers `G`. -/
lemma deleteEdges_sup_edge_singleton {u v : V} (hne : u ≠ v) (hnadj : ¬G.Adj u v) :
    (G ⊔ edge u v).deleteEdges {s(u, v)} = G := by
  rw [deleteEdges_sup]
  rw [deleteEdges_edge (by simp)]
  simp only [sup_bot_eq]
  rw [deleteEdges_eq_self]
  simp [Set.disjoint_singleton_right, mem_edgeSet, hnadj]

/-- Adding a nonedge whose endpoint-degree sum is at least the order preserves
Hamiltonicity in the reverse direction. -/
theorem isHamiltonian_of_sup_edge
    {u v : V} (hne : u ≠ v) (hnadj : ¬G.Adj u v)
    (hdeg : G.degree u + G.degree v ≥ Fintype.card V)
    (hadd : IsHamiltonian (G ⊔ edge u v)) : IsHamiltonian G := by
  intro hcard
  obtain ⟨a, p, hp⟩ := hadd hcard
  obtain ⟨d, hd, hd'⟩ : ∃ d ∈ p.darts, ¬G.Adj d.fst d.snd := by
    by_contra h
    simp only [not_exists, not_and, Decidable.not_not] at h
    have edgeSubset (e) (he : e ∈ p.edges) : e ∈ G.edgeSet := by
      simp only [edges, List.mem_map] at he
      obtain ⟨d, hd, hd'⟩ := he
      rw [← hd']
      exact h _ hd
    let q := p.transfer G edgeSubset
    suffices q.IsHamiltonianCycle from ⟨a, q, this⟩
    exact hp.transfer edgeSubset
  have haddEdge : (edge u v).Adj d.fst d.snd := by
    have := d.adj
    simp only [sup_adj] at this
    exact this.resolve_left hd'
  have hedge : s(u, v) = s(d.fst, d.snd) := (adj_edge.mp haddEdge).1
  have hdeg' : G.degree d.fst + G.degree d.snd ≥ Fintype.card V := by
    simp only [edge_adj] at haddEdge
    rcases haddEdge.1 with h | h
    · rw [h.1, h.2]
      exact hdeg
    · rw [h.1, h.2, add_comm]
      exact hdeg
  set x := d.fst
  set y := d.snd
  have hx : x ∈ p.support := Walk.dart_fst_mem_support_of_mem_darts _ hd
  let q := p.rotate x hx
  have hq : q.IsHamiltonianCycle := hp.rotate hx
  have hd_q : d ∈ q.darts := by
    simpa [q] using List.IsRotated.mem_iff (rotate_darts p x hx) |>.mpr hd
  have q_not_nil : ¬q.Nil := by
    erw [rotate_Nil_iff]
    exact hp.1.not_nil
  have next_x_eq_y : q.getVert 1 = y := by
    exact hq.1.next_unique (q.firstDart_mem_darts q_not_nil) hd_q rfl
  have xy_not_edge : s(x, y) ∉ q.tail.edges := by
    have hcons : q = cons (q.adj_getVert_one q_not_nil) q.tail :=
      (q.cons_tail_eq q_not_nil).symm
    have hedges : q.edges = s(x, y) :: q.tail.edges := by
      simp only [hcons, edges_cons]
      simpa using Or.inl next_x_eq_y
    intro h
    have nodup := hq.1.edges_nodup
    rw [hedges] at nodup
    exact List.not_nodup_cons_of_mem h nodup
  have G_del : (G ⊔ edge u v).deleteEdges {s(x, y)} = G := by
    rw [← hedge]
    exact deleteEdges_sup_edge_singleton hne hnadj
  let q' := q.tail
    |>.toDeleteEdge s(x, y) xy_not_edge
    |>.transfer G (by
      simp (config := {singlePass := true}) only [← G_del]
      exact edges_subset_edgeSet _)
    |>.copy next_x_eq_y rfl
  have perm_q' : q'.support ~ Finset.univ.toList := by
    rw [isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one] at hq
    simp only [transfer_transfer, support_copy, support_transfer, support_tail,
      List.perm_iff_count, hq.2, q']
    intro z
    rw [List.count_eq_one_of_mem (Finset.nodup_toList _) (by simp)]
    simpa [← support_tail_of_not_nil _ q_not_nil] using hq.2 z
  have hV : Fintype.card V ≥ 3 := hq.length_eq ▸ hq.isCycle.three_le_length
  have next_x : y = hq.next x := by
    obtain ⟨d', hd'₁, hd'₂, hd'₃⟩ := hq.self_next_in_darts x
    exact hd'₃ ▸ hq.isCycle.next_unique hd_q hd'₁ hd'₂.symm
  obtain ⟨w, w', d', hw, hw', d'_mem, hd'₁, hd'₂⟩ :=
    exists_crossing_dart_of_degree_sum hq hV hdeg' next_x hd'
  have q'_support : q'.support = q.support.tail := by
    simp [q', support_tail_of_not_nil _ q_not_nil]
  obtain ⟨i, i_lt, hi⟩ := List.getElem_of_mem d'_mem
  simp only [length_darts] at i_lt
  rw [← hi, darts_getElem_snd i i_lt] at hd'₂
  rw [← hi, darts_getElem_fst i i_lt] at hd'₁
  have i_nz : i ≠ 0 := by
    intro i_zero
    simp only [i_zero, List.getElem_zero, head_support] at hd'₁
    simp [hd'₁] at hw'
  have i_min_1 : i - 1 < q'.darts.length := by
    have q'_length : q'.length = q.length - 1 := by
      have hlen := length_tail_add_one q_not_nil
      simp [transfer_transfer, length_copy, length_transfer, q']
      omega
    simp [q'_length]
    omega
  have hd''₁ : (q'.darts[i - 1]).fst = w' := by
    rw [darts_getElem_fst _ (by simpa using i_min_1)]
    simp only [q'_support, ← List.drop_one]
    rw [List.getElem_drop, ← hd'₁]
    congr 1
    omega
  have hd''₂ : (q'.darts[i - 1]).snd = w := by
    rw [darts_getElem_snd _ (by simpa using i_min_1)]
    simp only [q'_support, ← List.drop_one]
    rw [List.getElem_drop, ← hd'₂]
    congr 1
    omega
  have w'_ne_x : w' ≠ x := fun eq => by simp [eq] at hw'
  exact isHamiltonian_of_spanning_path_reroute hV perm_q' w'_ne_x hw' hw
    q'.darts[i - 1] (List.getElem_mem _ _ _) hd''₁ hd''₂ hcard

#print axioms SimpleGraph.deleteEdges_sup_edge_singleton
#print axioms SimpleGraph.isHamiltonian_of_sup_edge

end SimpleGraph
