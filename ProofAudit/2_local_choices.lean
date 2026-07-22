/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import FormalConjecturesUtil

namespace WrittenOnTheWallII.GraphConjecture2Audit

open Classical Finset SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A chosen maximum independent set in the graph induced by `N(v)`. -/
noncomputable def localIndepSubtype
    (G : SimpleGraph α) (v : α) : Finset (G.neighborSet v) :=
  ((G.induce (G.neighborSet v)).exists_isNIndepSet_indepNum).choose

lemma localIndepSubtype_spec
    (G : SimpleGraph α) (v : α) :
    (G.induce (G.neighborSet v)).IsNIndepSet
      (G.induce (G.neighborSet v)).indepNum (localIndepSubtype G v) :=
  ((G.induce (G.neighborSet v)).exists_isNIndepSet_indepNum).choose_spec

/-- The same chosen set, embedded back into the original vertex type. -/
noncomputable def localIndep
    (G : SimpleGraph α) (v : α) : Finset α :=
  (localIndepSubtype G v).map ⟨Subtype.val, Subtype.val_injective⟩

/-- Every chosen local-independent vertex really is a neighbor of the center. -/
lemma localIndep_subset_neighborFinset
    (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) :
    localIndep G v ⊆ G.neighborFinset v := by
  intro u hu
  simp only [localIndep, Finset.mem_map] at hu
  obtain ⟨u', _hu', rfl⟩ := hu
  simpa using u'.property

/-- The chosen local independent set has the required maximum cardinality. -/
lemma card_localIndep
    (G : SimpleGraph α) (v : α) :
    (localIndep G v).card = indepNeighborsCard G v := by
  rw [localIndep, Finset.card_map]
  simpa [indepNeighborsCard] using (localIndepSubtype_spec G v).card_eq

#print axioms localIndepSubtype_spec
#print axioms localIndep_subset_neighborFinset
#print axioms card_localIndep

end WrittenOnTheWallII.GraphConjecture2Audit
