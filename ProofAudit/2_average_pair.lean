/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import ProofAudit.«2_double_count»
import ProofAudit.«2_positive»

namespace WrittenOnTheWallII.GraphConjecture2Audit

open Classical Finset SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The finite set of incidences selected by the maximum independent
neighborhood sets. -/
def selectedPairs (G : SimpleGraph α) : Finset (α × α) :=
  Finset.univ.biUnion fun v =>
    (chosenLocalIndep G v).image fun u => (v, u)

lemma mem_selectedPairs
    (G : SimpleGraph α) {v u : α} :
    (v, u) ∈ selectedPairs G ↔ u ∈ chosenLocalIndep G v := by
  simp [selectedPairs]

/-- Cardinality of the union of the neighborhoods at a selected pair. -/
def selectedUnionCard
    (G : SimpleGraph α) [DecidableRel G.Adj] (p : α × α) : ℕ :=
  (G.neighborFinset p.1 ∪ G.neighborFinset p.2).card

lemma selectedPairs_nonempty_of_connected
    (G : SimpleGraph α) (hG : G.Connected) :
    (selectedPairs G).Nonempty := by
  let v : α := Classical.choice (inferInstance : Nonempty α)
  have hcard : 0 < (chosenLocalIndep G v).card := by
    rw [chosenLocalIndep_card]
    exact indepNeighborsCard_pos_of_connected G hG v
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hcard
  exact ⟨(v, u), (mem_selectedPairs G).2 hu⟩

/-- The double-counting bound is attained by an actual selected incidence,
hence by an actual edge of the graph. -/
lemma exists_adjacent_neighbor_union_ge_two_average
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    ∃ v u : α, G.Adj v u ∧
      2 * averageIndepNeighbors G ≤
        ((G.neighborFinset v ∪ G.neighborFinset u).card : ℝ) := by
  let P := selectedPairs G
  have hP : P.Nonempty := selectedPairs_nonempty_of_connected G hG
  let values : Finset ℕ := P.image (selectedUnionCard G)
  have hvalues : values.Nonempty := hP.image (selectedUnionCard G)
  let M : ℕ := values.max' hvalues
  have hbound : ∀ v u, u ∈ chosenLocalIndep G v →
      ((G.neighborFinset v ∪ G.neighborFinset u).card : ℝ) ≤ (M : ℝ) := by
    intro v u hu
    have hp : (v, u) ∈ P := by
      exact (mem_selectedPairs G).2 hu
    have hv : selectedUnionCard G (v, u) ∈ values := by
      exact Finset.mem_image.mpr ⟨(v, u), hp, rfl⟩
    have hle : selectedUnionCard G (v, u) ≤ M := by
      exact Finset.le_max' values _ hv
    exact_mod_cast hle
  have havg : 2 * averageIndepNeighbors G ≤ (M : ℝ) :=
    two_mul_averageIndepNeighbors_le_of_selected_union_bound G M
      (sum_indepNeighborsCard_cast_pos_of_connected G hG) hbound
  have hMmem : M ∈ values := by
    exact Finset.max'_mem values hvalues
  obtain ⟨p, hpP, hpM⟩ := Finset.mem_image.mp hMmem
  refine ⟨p.1, p.2, ?_, ?_⟩
  · exact chosenLocalIndep_mem_adj G ((mem_selectedPairs G).1 hpP)
  · calc
      2 * averageIndepNeighbors G ≤ (M : ℝ) := havg
      _ = ((G.neighborFinset p.1 ∪ G.neighborFinset p.2).card : ℝ) := by
        exact_mod_cast hpM.symm

#print axioms selectedPairs_nonempty_of_connected
#print axioms exists_adjacent_neighbor_union_ge_two_average

end WrittenOnTheWallII.GraphConjecture2Audit
