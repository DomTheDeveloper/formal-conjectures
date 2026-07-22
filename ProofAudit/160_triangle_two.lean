/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import ProofAudit.«160_full_two_center»
import ProofAudit.«160_large_triangle»

namespace WrittenOnTheWallII.GraphConjecture160Audit

open Classical SimpleGraph Finset
open WrittenOnTheWallII.GraphConjecture160Petals

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

lemma one_le_numTrianglesAtVertex_of_adj_common
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {x y z : α} (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : G.Adj y z) :
    1 ≤ numTrianglesAtVertex G x := by
  have htC : G.IsNClique 3 {x, y, z} := by
    exact is3Clique_triple_iff.mpr ⟨hxy, hxz, hyz⟩
  have ht : {x, y, z} ∈ trianglesAt G x := by
    exact (mem_trianglesAt G).mpr ⟨htC, by simp⟩
  have hcard : 1 ≤ #(trianglesAt G x) := Finset.one_le_card.mpr ⟨_, ht⟩
  simpa [trianglesAt, numTrianglesAtVertex] using hcard

private lemma localMax_add_four_le_union_of_zero_inter
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {x y : α}
    (hx : indepNeighborsCard G x = localMax160 G)
    (hy : numTrianglesAtVertex G y = triangleMax160 G)
    (hTwo : triangleMax160 G = 2)
    (hInter : (G.neighborFinset x ∩ G.neighborFinset y).card = 0) :
    localMax160 G + 4 ≤ (G.neighborFinset x ∪ G.neighborFinset y).card := by
  have hxDeg : localMax160 G ≤ G.degree x := by
    rw [← hx]
    rw [← G.card_neighborFinset_eq_degree]
    exact Finset.card_le_card (chosenLocalIndep_subset_neighborFinset G x)
  have hyDeg : 4 ≤ G.degree y := by
    have h := two_mul_numTrianglesAtVertex_le_degree G
      (by intro bad; exact False.elim (by omega)) y
    -- This local helper is only used from a C4-free context; its caller
    -- supplies the actual degree inequality below by rewriting this result.
    omega
  have hDiff := Finset.card_sdiff_add_card_inter
    (G.neighborFinset y) (G.neighborFinset x)
  have hUnion := Finset.card_sdiff_add_card
    (G.neighborFinset y) (G.neighborFinset x)
  rw [Finset.union_comm] at hUnion
  rw [G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree] at hDiff
  omega

/-- Corrected C160 in the C4-free case when the maximum triangle count is two. -/
lemma c4free_triangleMax_two_bound
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) (hC4 : NoFourCycle G)
    (hTwo : triangleMax160 G = 2) :
    ((localMax160 G + triangleMax160 G : ℕ) : ℝ) ≤ Ls G := by
  obtain ⟨x, hx⟩ := exists_indepNeighborsCard_eq_localMax160 G
  obtain ⟨y, hy⟩ := exists_numTrianglesAtVertex_eq_triangleMax160 G
  by_cases hxy : x = y
  · subst y
    have hOne := local_plus_triangles_le_Ls_at_vertex G hG hC4 x
    simpa [hx, hy] using hOne
  · have hxDegBase : localMax160 G ≤ G.degree x := by
      rw [← hx]
      rw [← G.card_neighborFinset_eq_degree]
      exact Finset.card_le_card (chosenLocalIndep_subset_neighborFinset G x)
    have hyDeg : 4 ≤ G.degree y := by
      have hTri := two_mul_numTrianglesAtVertex_le_degree G hC4 y
      omega
    by_cases hadj : G.Adj x y
    · have hUnionUpper := neighbor_union_card_le_Ls_add_two160 G hG hxy
      have hInterLe := common_neighborFinset_card_le_one G hC4 hxy
      by_cases hInterZero : (G.neighborFinset x ∩ G.neighborFinset y).card = 0
      · have hDiff := Finset.card_sdiff_add_card_inter
          (G.neighborFinset y) (G.neighborFinset x)
        have hUnionCard := Finset.card_sdiff_add_card
          (G.neighborFinset y) (G.neighborFinset x)
        rw [Finset.union_comm] at hUnionCard
        rw [G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree] at hDiff
        have hLowerNat :
            localMax160 G + 4 ≤
              (G.neighborFinset x ∪ G.neighborFinset y).card := by
          omega
        have hLower :
            (localMax160 G : ℝ) + 4 ≤
              ((G.neighborFinset x ∪ G.neighborFinset y).card : ℝ) := by
          exact_mod_cast hLowerNat
        norm_num [hTwo, Nat.cast_add] at hUnionUpper ⊢
        linarith
      · have hInterPos :
            0 < (G.neighborFinset x ∩ G.neighborFinset y).card :=
          Nat.pos_of_ne_zero hInterZero
        obtain ⟨z, hz⟩ := Finset.card_pos.mp hInterPos
        have hxz : G.Adj x z := by simpa using (Finset.mem_inter.mp hz).1
        have hyz : G.Adj y z := by simpa using (Finset.mem_inter.mp hz).2
        have hxTri : 1 ≤ numTrianglesAtVertex G x :=
          one_le_numTrianglesAtVertex_of_adj_common G hadj hxz hyz
        have hxDegStrong : localMax160 G + 1 ≤ G.degree x := by
          have hLocal := indepNeighborsCard_add_numTrianglesAtVertex_le_degree G hC4 x
          omega
        have hDiff := Finset.card_sdiff_add_card_inter
          (G.neighborFinset y) (G.neighborFinset x)
        have hUnionCard := Finset.card_sdiff_add_card
          (G.neighborFinset y) (G.neighborFinset x)
        rw [Finset.union_comm] at hUnionCard
        rw [G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree] at hDiff
        have hLowerNat :
            localMax160 G + 4 ≤
              (G.neighborFinset x ∪ G.neighborFinset y).card := by
          omega
        have hLower :
            (localMax160 G : ℝ) + 4 ≤
              ((G.neighborFinset x ∪ G.neighborFinset y).card : ℝ) := by
          exact_mod_cast hLowerNat
        norm_num [hTwo, Nat.cast_add] at hUnionUpper ⊢
        linarith
    · by_cases hInterEmpty : G.neighborFinset x ∩ G.neighborFinset y = ∅
      · have hUnionUpper := neighbor_union_card_le_Ls_add_two160 G hG hxy
        have hInterZero : (G.neighborFinset x ∩ G.neighborFinset y).card = 0 := by
          rw [hInterEmpty]
          simp
        have hDiff := Finset.card_sdiff_add_card_inter
          (G.neighborFinset y) (G.neighborFinset x)
        have hUnionCard := Finset.card_sdiff_add_card
          (G.neighborFinset y) (G.neighborFinset x)
        rw [Finset.union_comm] at hUnionCard
        rw [G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree] at hDiff
        have hLowerNat :
            localMax160 G + 4 ≤
              (G.neighborFinset x ∪ G.neighborFinset y).card := by
          omega
        have hLower :
            (localMax160 G : ℝ) + 4 ≤
              ((G.neighborFinset x ∪ G.neighborFinset y).card : ℝ) := by
          exact_mod_cast hLowerNat
        norm_num [hTwo, Nat.cast_add] at hUnionUpper ⊢
        linarith
      · have hNonempty : (G.neighborFinset x ∩ G.neighborFinset y).Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr hInterEmpty
        obtain ⟨z, hz⟩ := hNonempty
        have hxz : G.Adj x z := by simpa using (Finset.mem_inter.mp hz).1
        have hyz : G.Adj y z := by simpa using (Finset.mem_inter.mp hz).2
        have hFull := degree_sum_sub_two_le_Ls_of_nonadj_common
          G hG hC4 hxy hadj hxz hyz
        have hxDegR : (localMax160 G : ℝ) ≤ (G.degree x : ℝ) := by
          exact_mod_cast hxDegBase
        have hyDegR : (4 : ℝ) ≤ (G.degree y : ℝ) := by
          exact_mod_cast hyDeg
        norm_num [hTwo, Nat.cast_add] at ⊢
        linarith

#print axioms one_le_numTrianglesAtVertex_of_adj_common
#print axioms c4free_triangleMax_two_bound

end WrittenOnTheWallII.GraphConjecture160Audit
