/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import ProofAudit.«160_star_bound»

namespace WrittenOnTheWallII.GraphConjecture160Audit

open Classical SimpleGraph Finset

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

lemma degree_le_Ls_of_connected
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (x : α) :
    (G.degree x : ℝ) ≤ Ls G := by
  obtain ⟨T, hseedT, hTG, hT⟩ :=
    hG.exists_isTree_le_of_le_of_isAcyclic
      (starSeed160_le G x) (starSeed160_isAcyclic G x)
  letI : DecidableRel T.Adj := Classical.decRel T.Adj
  have hDegree : G.degree x ≤ T.degree x := by
    rw [← G.card_neighborFinset_eq_degree, ← T.card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro v hv
    have hTadj : T.Adj x v := hseedT (starSeed160_adj G x hv)
    simpa using hTadj
  have hDegreeR : (G.degree x : ℝ) ≤ (T.degree x : ℝ) := by
    exact_mod_cast hDegree
  have hTreeInt := degree_le_treeLeaves160 T hT x
  have hTree : (T.degree x : ℝ) ≤ ((treeLeaves160 T).card : ℝ) := by
    exact_mod_cast hTreeInt
  exact hDegreeR.trans (hTree.trans (treeLeaves160_card_le_Ls G T hTG hT))

lemma local_plus_triangles_le_Ls_at_vertex
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) (hC4 : NoFourCycle G) (x : α) :
    ((indepNeighborsCard G x + numTrianglesAtVertex G x : ℕ) : ℝ) ≤ Ls G := by
  have hdeg := indepNeighborsCard_add_numTrianglesAtVertex_le_degree G hC4 x
  have hdegR :
      ((indepNeighborsCard G x + numTrianglesAtVertex G x : ℕ) : ℝ) ≤
        (G.degree x : ℝ) := by
    exact_mod_cast hdeg
  exact hdegR.trans (degree_le_Ls_of_connected G hG x)

noncomputable def triangleMax160
    (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  maxTrianglesAtVertex G

lemma exists_numTrianglesAtVertex_eq_triangleMax160
    (G : SimpleGraph α) [DecidableRel G.Adj] :
    ∃ y, numTrianglesAtVertex G y = triangleMax160 G := by
  unfold triangleMax160 maxTrianglesAtVertex
  have hm := (Finset.univ.image (numTrianglesAtVertex G)).max'_mem
    (Finset.image_nonempty.mpr Finset.univ_nonempty)
  rw [Finset.mem_image] at hm
  obtain ⟨y, _hy, hym⟩ := hm
  exact ⟨y, hym⟩

#print axioms degree_le_Ls_of_connected
#print axioms local_plus_triangles_le_Ls_at_vertex
#print axioms exists_numTrianglesAtVertex_eq_triangleMax160

end WrittenOnTheWallII.GraphConjecture160Audit
