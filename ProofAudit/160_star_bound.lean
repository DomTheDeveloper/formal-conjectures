/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import ProofAudit.«160_attempt»
import ProofAudit.«160_local_count»
import ProofAudit.«160_tree_bridge»

namespace WrittenOnTheWallII.GraphConjecture160Audit

open Classical SimpleGraph Finset

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

noncomputable def starLeaves160
    (G : SimpleGraph α) [DecidableRel G.Adj] (x : α) : List α :=
  (G.neighborFinset x).toList

noncomputable def starSeed160
    (G : SimpleGraph α) [DecidableRel G.Adj] (x : α) : SimpleGraph α :=
  attachLeaves (⊥ : SimpleGraph α) x (starLeaves160 G x)

lemma starSeed160_isAcyclic
    (G : SimpleGraph α) [DecidableRel G.Adj] (x : α) :
    (starSeed160 G x).IsAcyclic := by
  apply attachLeaves_isAcyclic (⊥ : SimpleGraph α) x (starLeaves160 G x)
  · exact isAcyclic_bot
  · simp [starLeaves160]
  · simp [starLeaves160]
  · simp

lemma starSeed160_le
    (G : SimpleGraph α) [DecidableRel G.Adj] (x : α) :
    starSeed160 G x ≤ G := by
  apply attachLeaves_le (⊥ : SimpleGraph α) G x (starLeaves160 G x) bot_le
  intro v hv
  have hv' : v ∈ G.neighborFinset x := by
    simpa [starLeaves160] using hv
  simpa using hv'

lemma starSeed160_adj
    (G : SimpleGraph α) [DecidableRel G.Adj] (x : α) {v : α}
    (hv : v ∈ G.neighborFinset x) :
    (starSeed160 G x).Adj x v := by
  apply attachLeaves_adj_of_mem
  simpa [starLeaves160] using hv

lemma indepNeighborsCard_le_Ls
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (x : α) :
    (indepNeighborsCard G x : ℝ) ≤ Ls G := by
  obtain ⟨T, hseedT, hTG, hT⟩ :=
    hG.exists_isTree_le_of_le_of_isAcyclic
      (starSeed160_le G x) (starSeed160_isAcyclic G x)
  letI : DecidableRel T.Adj := Classical.decRel T.Adj
  have hLocalDegree : indepNeighborsCard G x ≤ G.degree x := by
    rw [← chosenLocalIndep_card G x]
    rw [← G.card_neighborFinset_eq_degree]
    exact Finset.card_le_card (chosenLocalIndep_subset_neighborFinset G x)
  have hDegree : G.degree x ≤ T.degree x := by
    rw [← G.card_neighborFinset_eq_degree, ← T.card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro v hv
    have hTadj : T.Adj x v := hseedT (starSeed160_adj G x hv)
    simpa using hTadj
  have hTreeInt := degree_le_treeLeaves160 T hT x
  have hTree : (T.degree x : ℝ) ≤ ((treeLeaves160 T).card : ℝ) := by
    exact_mod_cast hTreeInt
  have hLs := treeLeaves160_card_le_Ls G T hTG hT
  exact_mod_cast hLocalDegree.trans hDegree |>.trans (hTree.trans hLs)

noncomputable def localMax160
    (G : SimpleGraph α) : ℕ :=
  (Finset.univ.image (indepNeighborsCard G)).max'
    (Finset.image_nonempty.mpr Finset.univ_nonempty)

lemma exists_indepNeighborsCard_eq_localMax160
    (G : SimpleGraph α) :
    ∃ x, indepNeighborsCard G x = localMax160 G := by
  have hm := (Finset.univ.image (indepNeighborsCard G)).max'_mem
    (Finset.image_nonempty.mpr Finset.univ_nonempty)
  rw [Finset.mem_image] at hm
  obtain ⟨x, _hx, hxm⟩ := hm
  exact ⟨x, hxm⟩

lemma localMax160_le_Ls
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    (localMax160 G : ℝ) ≤ Ls G := by
  obtain ⟨x, hx⟩ := exists_indepNeighborsCard_eq_localMax160 G
  rw [← hx]
  exact indepNeighborsCard_le_Ls G hG x

#print axioms indepNeighborsCard_le_Ls
#print axioms localMax160_le_Ls

end WrittenOnTheWallII.GraphConjecture160Audit
