/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import ProofAudit.«160_maxima»
import ProofAudit.«160_two_center_bound»
import ProofAudit.«160_common_neighbors»

namespace WrittenOnTheWallII.GraphConjecture160Audit

open Classical SimpleGraph Finset

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The corrected C4-free C160 bound whenever the maximum number of triangles
at a vertex is at least three. The only remaining C4-free cases are triangle
maximum zero, one, and two. -/
lemma c4free_large_triangleMax_bound
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) (hC4 : NoFourCycle G)
    (hThree : 3 ≤ triangleMax160 G) :
    ((localMax160 G + triangleMax160 G : ℕ) : ℝ) ≤ Ls G := by
  obtain ⟨x, hx⟩ := exists_indepNeighborsCard_eq_localMax160 G
  obtain ⟨y, hy⟩ := exists_numTrianglesAtVertex_eq_triangleMax160 G
  by_cases hxy : x = y
  · subst y
    have hOne := local_plus_triangles_le_Ls_at_vertex G hG hC4 x
    simpa [hx, hy] using hOne
  · have hUnion := neighbor_union_card_le_Ls_add_two160 G hG hxy
    have hInter := common_neighborFinset_card_le_one G hC4 hxy
    have hxDeg : localMax160 G ≤ G.degree x := by
      have hLocal := indepNeighborsCard_add_numTrianglesAtVertex_le_degree G hC4 x
      omega
    have hyDeg : 2 * triangleMax160 G ≤ G.degree y := by
      have hTri := two_mul_numTrianglesAtVertex_le_degree G hC4 y
      omega
    have hDiff := Finset.card_sdiff_add_card_inter
      (G.neighborFinset y) (G.neighborFinset x)
    have hUnionCard := Finset.card_sdiff_add_card
      (G.neighborFinset y) (G.neighborFinset x)
    rw [Finset.union_comm] at hUnionCard
    have hLowerNat :
        localMax160 G + 2 * triangleMax160 G ≤
          (G.neighborFinset x ∪ G.neighborFinset y).card + 1 := by
      rw [G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree] at hDiff
      omega
    have hLower :
        (localMax160 G : ℝ) + 2 * (triangleMax160 G : ℝ) ≤
          ((G.neighborFinset x ∪ G.neighborFinset y).card : ℝ) + 1 := by
      exact_mod_cast hLowerNat
    have hThreeR : (3 : ℝ) ≤ (triangleMax160 G : ℝ) := by
      exact_mod_cast hThree
    norm_num [Nat.cast_add] at hUnion ⊢
    linarith

#print axioms c4free_large_triangleMax_bound

end WrittenOnTheWallII.GraphConjecture160Audit
