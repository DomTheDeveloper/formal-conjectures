/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import FormalConjecturesUtil

namespace WrittenOnTheWallII.GraphConjecture160Local

open Classical SimpleGraph Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def localIndepSubtype (G : SimpleGraph α) (v : α) :
    Finset (G.neighborSet v) :=
  Classical.choose ((G.induce (G.neighborSet v)).exists_isNIndepSet_indepNum)

noncomputable def localIndepSet (G : SimpleGraph α) (v : α) : Finset α :=
  (localIndepSubtype G v).map ⟨Subtype.val, Subtype.val_injective⟩

lemma localIndepSet_subset_neighborSet (G : SimpleGraph α) (v : α) :
    (localIndepSet G v : Set α) ⊆ G.neighborSet v := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
  exact y.property

lemma localIndepSet_isIndep (G : SimpleGraph α) (v : α) :
    G.IsIndepSet (localIndepSet G v : Set α) := by
  intro a ha b hb hab hAdj
  obtain ⟨a', ha', rfl⟩ := Finset.mem_map.mp ha
  obtain ⟨b', hb', rfl⟩ := Finset.mem_map.mp hb
  have hs := Classical.choose_spec
    ((G.induce (G.neighborSet v)).exists_isNIndepSet_indepNum)
  exact hs.isIndepSet ha' hb' (Subtype.coe_injective.ne hab) hAdj

lemma card_localIndepSet (G : SimpleGraph α) (v : α) :
    #(localIndepSet G v) = indepNeighborsCard G v := by
  rw [localIndepSet, Finset.card_map]
  exact (Classical.choose_spec
    ((G.induce (G.neighborSet v)).exists_isNIndepSet_indepNum)).card_eq

lemma exists_maxLocalIndependence_vertex (G : SimpleGraph α) :
    ∃ v : α,
      indepNeighborsCard G v =
        (Finset.univ.image (indepNeighborsCard G)).max'
          (Finset.image_nonempty.mpr Finset.univ_nonempty) := by
  let S := Finset.univ.image (indepNeighborsCard G)
  have hS : S.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
  have hm : S.max' hS ∈ S := S.max'_mem hS
  obtain ⟨v, -, hv⟩ := Finset.mem_image.mp hm
  exact ⟨v, hv.symm⟩

lemma exists_maxTriangles_vertex (G : SimpleGraph α) [DecidableRel G.Adj] :
    ∃ v : α,
      numTrianglesAtVertex G v =
        (Finset.univ.image (numTrianglesAtVertex G)).max'
          (Finset.image_nonempty.mpr Finset.univ_nonempty) := by
  let S := Finset.univ.image (numTrianglesAtVertex G)
  have hS : S.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
  have hm : S.max' hS ∈ S := S.max'_mem hS
  obtain ⟨v, -, hv⟩ := Finset.mem_image.mp hm
  exact ⟨v, hv.symm⟩

#print axioms localIndepSet_isIndep
#print axioms card_localIndepSet
#print axioms exists_maxLocalIndependence_vertex
#print axioms exists_maxTriangles_vertex

end WrittenOnTheWallII.GraphConjecture160Local
