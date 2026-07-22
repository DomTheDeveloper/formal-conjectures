/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import ProofAudit.«160_triangle_one»

namespace WrittenOnTheWallII.GraphConjecture160Audit

open Classical SimpleGraph Finset

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

lemma c4free_complete_bound
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) (hC4 : NoFourCycle G) :
    ((localMax160 G + triangleMax160 G : ℕ) : ℝ) ≤ Ls G := by
  by_cases hOne : triangleMax160 G = 1
  · exact c4free_triangleMax_one_bound G hG hC4 hOne
  · exact c4free_bound_of_triangleMax_ne_one G hG hC4 hOne

/-- Complete proof of the corrected historical WOWII Conjecture 160 statement.
The C4 characteristic is `1` exactly when there is no four-cycle subgraph. -/
theorem conjecture160_corrected_complete
    (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    let maxL := (Finset.univ.image (indepNeighborsCard G)).max' (by simp)
    let maxT := maxTrianglesAtVertex G
    let cC4 : ℕ :=
      if ∃ v : α, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = 4 then 0 else 1
    (maxL : ℝ) + (maxT : ℝ) * (cC4 : ℝ) ≤ Ls G := by
  dsimp only
  change (localMax160 G : ℝ) + (triangleMax160 G : ℝ) *
      (if ∃ v : α, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = 4 then
        (0 : ℕ) else 1 : ℕ) ≤ Ls G
  by_cases hCycle : ∃ v : α, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = 4
  · simp [hCycle]
    exact localMax160_le_Ls G h
  · have hC4 : NoFourCycle G := hCycle
    have hBound := c4free_complete_bound G h hC4
    norm_num [hCycle, Nat.cast_add] at hBound ⊢
    exact hBound

#print axioms c4free_complete_bound
#print axioms conjecture160_corrected_complete

end WrittenOnTheWallII.GraphConjecture160Audit
