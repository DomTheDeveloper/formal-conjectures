/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import ProofAudit.«160_triangle_boundary»
import ProofAudit.«160_except_one»

namespace WrittenOnTheWallII.GraphConjecture160Audit

open Classical SimpleGraph Finset
open WrittenOnTheWallII.GraphConjecture160Petals

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- Corrected C160 in the final C4-free case, when the maximum triangle count
is exactly one. -/
lemma c4free_triangleMax_one_bound
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) (hC4 : NoFourCycle G)
    (hOne : triangleMax160 G = 1) :
    ((localMax160 G + triangleMax160 G : ℕ) : ℝ) ≤ Ls G := by
  obtain ⟨x, hx⟩ := exists_indepNeighborsCard_eq_localMax160 G
  have hxMax := numTrianglesAtVertex_le_triangleMax160 G x
  by_cases hxZero : numTrianglesAtVertex G x = 0
  · obtain ⟨y₀, hy₀⟩ := exists_numTrianglesAtVertex_eq_triangleMax160 G
    have hyOne : numTrianglesAtVertex G y₀ = 1 := by omega
    have hTriNon : (trianglesAt G y₀).Nonempty := by
      rw [← Finset.card_pos]
      simpa [trianglesAt, numTrianglesAtVertex, hyOne]
    obtain ⟨t, htMem⟩ := hTriNon
    obtain ⟨htC, hy₀t⟩ := (mem_trianglesAt G).mp htMem
    have hxt : x ∉ t := by
      intro hxin
      have htX : t ∈ trianglesAt G x :=
        (mem_trianglesAt G).mpr ⟨htC, hxin⟩
      have hPos : 0 < #(trianglesAt G x) :=
        Finset.card_pos.mpr ⟨t, htX⟩
      have : 0 < numTrianglesAtVertex G x := by
        simpa [trianglesAt, numTrianglesAtVertex] using hPos
      omega
    obtain ⟨a, hat, haDeg⟩ :=
      exists_triangle_vertex_degree_ge_three G hG htC hxt
    have hxa : x ≠ a := by
      intro h
      subst a
      exact hxt hat
    have hxDeg : localMax160 G ≤ G.degree x := by
      rw [← hx]
      rw [← G.card_neighborFinset_eq_degree]
      exact Finset.card_le_card (chosenLocalIndep_subset_neighborFinset G x)
    have finish_empty :
        G.neighborFinset x ∩ G.neighborFinset a = ∅ →
          ((localMax160 G + triangleMax160 G : ℕ) : ℝ) ≤ Ls G := by
      intro hEmpty
      have hUnionUpper := neighbor_union_card_le_Ls_add_two160 G hG hxa
      have hDiff := Finset.card_sdiff_add_card_inter
        (G.neighborFinset a) (G.neighborFinset x)
      have hUnionCard := Finset.card_sdiff_add_card
        (G.neighborFinset a) (G.neighborFinset x)
      rw [Finset.union_comm] at hUnionCard
      have hInterZero : (G.neighborFinset a ∩ G.neighborFinset x).card = 0 := by
        rw [Finset.inter_comm, hEmpty]
        simp
      rw [G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree] at hDiff
      have hLowerNat :
          localMax160 G + 3 ≤
            (G.neighborFinset x ∪ G.neighborFinset a).card := by
        omega
      have hLower :
          (localMax160 G : ℝ) + 3 ≤
            ((G.neighborFinset x ∪ G.neighborFinset a).card : ℝ) := by
        exact_mod_cast hLowerNat
      norm_num [hOne, Nat.cast_add] at hUnionUpper ⊢
      linarith
    by_cases hxaAdj : G.Adj x a
    · have hInterEmpty : G.neighborFinset x ∩ G.neighborFinset a = ∅ := by
        apply Finset.eq_empty_iff_forall_not_mem.mpr
        intro z hz
        have hxz : G.Adj x z := by simpa using (Finset.mem_inter.mp hz).1
        have haz : G.Adj a z := by simpa using (Finset.mem_inter.mp hz).2
        have hTriX := one_le_numTrianglesAtVertex_of_adj_common G hxaAdj hxz haz
        omega
      exact finish_empty hInterEmpty
    · by_cases hInterEmpty : G.neighborFinset x ∩ G.neighborFinset a = ∅
      · exact finish_empty hInterEmpty
      · have hNonempty : (G.neighborFinset x ∩ G.neighborFinset a).Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr hInterEmpty
        obtain ⟨z, hz⟩ := hNonempty
        have hxz : G.Adj x z := by simpa using (Finset.mem_inter.mp hz).1
        have haz : G.Adj a z := by simpa using (Finset.mem_inter.mp hz).2
        have hFull := degree_sum_sub_two_le_Ls_of_nonadj_common
          G hG hC4 hxa hxaAdj hxz haz
        have hxDegR : (localMax160 G : ℝ) ≤ (G.degree x : ℝ) := by
          exact_mod_cast hxDeg
        have haDegR : (3 : ℝ) ≤ (G.degree a : ℝ) := by
          exact_mod_cast haDeg
        norm_num [hOne, Nat.cast_add] at ⊢
        linarith
  · have hxOne : numTrianglesAtVertex G x = 1 := by
      omega
    have hAtX := local_plus_triangles_le_Ls_at_vertex G hG hC4 x
    simpa [hx, hxOne, hOne] using hAtX

#print axioms c4free_triangleMax_one_bound

end WrittenOnTheWallII.GraphConjecture160Audit
