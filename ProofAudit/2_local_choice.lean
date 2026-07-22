/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import FormalConjecturesUtil

namespace WrittenOnTheWallII.GraphConjecture2Audit

open Classical Finset SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A chosen maximum independent set in the graph induced by `N(v)`, still
viewed on the subtype `N(v)`. -/
noncomputable def chosenLocalIndepSubtype
    (G : SimpleGraph α) (v : α) : Finset (G.neighborSet v) :=
  (G.induce (G.neighborSet v)).exists_isNIndepSet_indepNum.choose

lemma chosenLocalIndepSubtype_spec
    (G : SimpleGraph α) (v : α) :
    (G.induce (G.neighborSet v)).IsNIndepSet
      (G.induce (G.neighborSet v)).indepNum
      (chosenLocalIndepSubtype G v) :=
  (G.induce (G.neighborSet v)).exists_isNIndepSet_indepNum.choose_spec

/-- The same chosen set, embedded back into the original vertex type. -/
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

lemma chosenLocalIndep_mem_adj
    (G : SimpleGraph α) [DecidableRel G.Adj] {v u : α}
    (hu : u ∈ chosenLocalIndep G v) :
    G.Adj v u := by
  simpa using chosenLocalIndep_subset_neighborFinset G v hu

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

#print axioms chosenLocalIndepSubtype_spec
#print axioms chosenLocalIndep_card
#print axioms chosenLocalIndep_subset_neighborFinset
#print axioms chosenLocalIndep_mem_adj
#print axioms chosenLocalIndep_isIndepSet

end WrittenOnTheWallII.GraphConjecture2Audit
