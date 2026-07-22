/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import ProofAudit.«2_local_choice»

namespace WrittenOnTheWallII.GraphConjecture2Audit

open Classical Finset SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- Every vertex of a connected nontrivial graph has a nonempty neighborhood,
so its neighborhood independence number is positive. -/
lemma indepNeighborsCard_pos_of_connected
    (G : SimpleGraph α) (hG : G.Connected) (v : α) :
    0 < indepNeighborsCard G v := by
  obtain ⟨u, huv⟩ := hG.preconnected.exists_adj_of_nontrivial v
  let u' : G.neighborSet v := ⟨u, huv⟩
  have hs : (G.induce (G.neighborSet v)).IsIndepSet
      ({u'} : Finset (G.neighborSet v)) := by
    simp
  have hle : 1 ≤ (G.induce (G.neighborSet v)).indepNum := by
    simpa using hs.card_le_indepNum
  simpa [indepNeighborsCard] using hle

/-- The total local-independence mass used in the Cauchy argument is strictly
positive for every connected nontrivial graph. -/
lemma sum_indepNeighborsCard_cast_pos_of_connected
    (G : SimpleGraph α) (hG : G.Connected) :
    0 < ∑ v, (indepNeighborsCard G v : ℝ) := by
  let v : α := Classical.choice (inferInstance : Nonempty α)
  have hv : 0 < (indepNeighborsCard G v : ℝ) := by
    exact_mod_cast indepNeighborsCard_pos_of_connected G hG v
  have hnonneg : ∀ w ∈ (Finset.univ : Finset α),
      0 ≤ (indepNeighborsCard G w : ℝ) := by
    intro w _hw
    positivity
  have hle : (indepNeighborsCard G v : ℝ) ≤
      ∑ w, (indepNeighborsCard G w : ℝ) :=
    (Finset.univ : Finset α).single_le_sum hnonneg (Finset.mem_univ v)
  exact hv.trans_le hle

#print axioms indepNeighborsCard_pos_of_connected
#print axioms sum_indepNeighborsCard_cast_pos_of_connected

end WrittenOnTheWallII.GraphConjecture2Audit
