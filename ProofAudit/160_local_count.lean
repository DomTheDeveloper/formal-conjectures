/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import ProofAudit.«160_local_structure»
import ProofAudit.«160_petals»

namespace WrittenOnTheWallII.GraphConjecture160Audit

open Classical SimpleGraph Finset
open WrittenOnTheWallII.GraphConjecture160Petals

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

noncomputable def chosenLocalIndepSubtype
    (G : SimpleGraph α) (v : α) : Finset (G.neighborSet v) :=
  (G.induce (G.neighborSet v)).exists_isNIndepSet_indepNum.choose

lemma chosenLocalIndepSubtype_spec
    (G : SimpleGraph α) (v : α) :
    (G.induce (G.neighborSet v)).IsNIndepSet
      (G.induce (G.neighborSet v)).indepNum
      (chosenLocalIndepSubtype G v) :=
  (G.induce (G.neighborSet v)).exists_isNIndepSet_indepNum.choose_spec

noncomputable def chosenLocalIndep
    (G : SimpleGraph α) (v : α) : Finset α :=
  (chosenLocalIndepSubtype G v).map
    ⟨Subtype.val, Subtype.val_injective⟩

lemma chosenLocalIndep_card
    (G : SimpleGraph α) (v : α) :
    (chosenLocalIndep G v).card = indepNeighborsCard G v := by
  rw [chosenLocalIndep, Finset.card_map]
  simpa [indepNeighborsCard] using
    (chosenLocalIndepSubtype_spec G v).card_eq

lemma chosenLocalIndep_subset_neighborFinset
    (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) :
    chosenLocalIndep G v ⊆ G.neighborFinset v := by
  intro u hu
  rw [chosenLocalIndep, Finset.mem_map] at hu
  obtain ⟨w, _hw, rfl⟩ := hu
  simpa using w.property

lemma chosenLocalIndep_isIndepSet
    (G : SimpleGraph α) (v : α) :
    G.IsIndepSet (chosenLocalIndep G v : Set α) := by
  intro a ha b hb hab
  have ha' : a ∈ chosenLocalIndep G v := by simpa using ha
  have hb' : b ∈ chosenLocalIndep G v := by simpa using hb
  rw [chosenLocalIndep, Finset.mem_map] at ha' hb'
  obtain ⟨a', ha', rfl⟩ := ha'
  obtain ⟨b', hb', rfl⟩ := hb'
  have hab' : a' ≠ b' := by
    intro h
    apply hab
    exact congrArg Subtype.val h
  have hnot := (chosenLocalIndepSubtype_spec G v).isIndepSet
    (by simpa using ha') (by simpa using hb') hab'
  simpa using hnot

lemma trianglePetals_subset_neighborFinset
    (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) :
    trianglePetals G v ⊆ G.neighborFinset v := by
  intro z hz
  simp only [trianglePetals, Finset.mem_biUnion] at hz
  obtain ⟨t, ht, hzt⟩ := hz
  obtain ⟨htC, hvt⟩ := (mem_trianglesAt G).mp ht
  have hzT : z ∈ t := (Finset.mem_erase.mp hzt).2
  have hzv : z ≠ v := (Finset.mem_erase.mp hzt).1
  have hvz : G.Adj v z := htC.isClique hvt hzT hzv.symm
  simpa using hvz

lemma two_mul_numTrianglesAtVertex_le_degree
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hC4 : NoFourCycle G) (v : α) :
    2 * numTrianglesAtVertex G v ≤ G.degree v := by
  have hED := edgeDisjointTriangles_of_no_four_cycle G hC4
  have hPcard := card_trianglePetals G (v := v) hED
  have hPsub := trianglePetals_subset_neighborFinset G v
  have hcard := Finset.card_le_card hPsub
  rw [G.card_neighborFinset_eq_degree] at hcard
  simpa [trianglesAt, numTrianglesAtVertex] using hPcard ▸ hcard

lemma indepNeighborsCard_add_numTrianglesAtVertex_le_degree
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hC4 : NoFourCycle G) (v : α) :
    indepNeighborsCard G v + numTrianglesAtVertex G v ≤ G.degree v := by
  let S := chosenLocalIndep G v
  let P := trianglePetals G v
  let N := G.neighborFinset v
  have hED := edgeDisjointTriangles_of_no_four_cycle G hC4
  have hInt : #(S ∩ P) ≤ #(trianglesAt G v) := by
    exact card_inter_trianglePetals_le G hED
      (chosenLocalIndep_isIndepSet G v)
  have hSsub : S ⊆ N := by
    simpa [S, N] using chosenLocalIndep_subset_neighborFinset G v
  have hPsub : P ⊆ N := by
    simpa [P, N] using trianglePetals_subset_neighborFinset G v
  have hOutSub : S \ P ⊆ N \ P := Finset.sdiff_subset_sdiff hSsub (Subset.rfl)
  have hOut : #(S \ P) ≤ #(N \ P) := Finset.card_le_card hOutSub
  have hSdecomp := Finset.card_inter_add_card_sdiff S P
  have hNdecomp := Finset.card_sdiff_add_card_eq_card hPsub
  have hPcard : #P = 2 * #(trianglesAt G v) := by
    simpa [P] using card_trianglePetals G (v := v) hED
  have hScard : #S = indepNeighborsCard G v := by
    simpa [S] using chosenLocalIndep_card G v
  have hNcard : #N = G.degree v := by
    simpa [N] using G.card_neighborFinset_eq_degree (v := v)
  have hTcard : #(trianglesAt G v) = numTrianglesAtVertex G v := by
    simp [trianglesAt, numTrianglesAtVertex]
  omega

#print axioms two_mul_numTrianglesAtVertex_le_degree
#print axioms indepNeighborsCard_add_numTrianglesAtVertex_le_degree

end WrittenOnTheWallII.GraphConjecture160Audit
