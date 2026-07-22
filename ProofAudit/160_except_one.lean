/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import ProofAudit.«160_triangle_two»

namespace WrittenOnTheWallII.GraphConjecture160Audit

open Classical SimpleGraph Finset

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

lemma c4free_triangleMax_zero_bound
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (hZero : triangleMax160 G = 0) :
    ((localMax160 G + triangleMax160 G : ℕ) : ℝ) ≤ Ls G := by
  have hLocal := localMax160_le_Ls G hG
  simpa [hZero] using hLocal

/-- Corrected C160 is now reduced to exactly the C4-free case with maximum
triangle count equal to one. -/
lemma c4free_bound_of_triangleMax_ne_one
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) (hC4 : NoFourCycle G)
    (hNotOne : triangleMax160 G ≠ 1) :
    ((localMax160 G + triangleMax160 G : ℕ) : ℝ) ≤ Ls G := by
  by_cases hZero : triangleMax160 G = 0
  · exact c4free_triangleMax_zero_bound G hG hZero
  by_cases hTwo : triangleMax160 G = 2
  · exact c4free_triangleMax_two_bound G hG hC4 hTwo
  have hThree : 3 ≤ triangleMax160 G := by
    omega
  exact c4free_large_triangleMax_bound G hG hC4 hThree

#print axioms c4free_triangleMax_zero_bound
#print axioms c4free_bound_of_triangleMax_ne_one

end WrittenOnTheWallII.GraphConjecture160Audit
