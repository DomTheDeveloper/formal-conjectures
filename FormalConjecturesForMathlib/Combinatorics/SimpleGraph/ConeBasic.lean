/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Data.Fintype.Option

/-!
# The one-vertex cone over a simple graph

The cone is used to reduce Hamiltonian paths to Hamiltonian cycles: a path in
`G` becomes a cycle after adjoining one universal apex.
-/

namespace SimpleGraph

open Classical

variable {V : Type*}

/-- Add one new universal vertex, represented by `none`. -/
def cone (G : SimpleGraph V) : SimpleGraph (Option V) where
  Adj x y :=
    match x, y with
    | none, none => False
    | none, some _ => True
    | some _, none => True
    | some u, some v => G.Adj u v
  symm := by
    intro x y h
    cases x <;> cases y <;> simp_all [G.adj_symm]
  loopless := by
    intro x
    cases x <;> simp

@[simp] lemma cone_adj_none_none (G : SimpleGraph V) : ¬(cone G).Adj none none := by simp [cone]
@[simp] lemma cone_adj_none_some (G : SimpleGraph V) (v : V) :
    (cone G).Adj none (some v) := by simp [cone]
@[simp] lemma cone_adj_some_none (G : SimpleGraph V) (v : V) :
    (cone G).Adj (some v) none := by simp [cone]
@[simp] lemma cone_adj_some_some (G : SimpleGraph V) (u v : V) :
    (cone G).Adj (some u) (some v) ↔ G.Adj u v := by simp [cone]

/-- The canonical graph homomorphism into the cone. -/
def coneSomeHom (G : SimpleGraph V) : G →g cone G where
  toFun := some
  map_rel' := by
    intro u v h
    simpa [cone] using h

@[simp] lemma coneSomeHom_apply (G : SimpleGraph V) (v : V) : coneSomeHom G v = some v := rfl

variable [Fintype V]

lemma cone_neighborFinset_some (G : SimpleGraph V) (v : V) :
    (cone G).neighborFinset (some v) =
      insert none ((G.neighborFinset v).image some) := by
  classical
  ext x
  cases x with
  | none => simp [cone]
  | some x => simp [cone]

@[simp] theorem cone_degree_some (G : SimpleGraph V) (v : V) :
    (cone G).degree (some v) = G.degree v + 1 := by
  classical
  rw [← card_neighborFinset_eq_degree, cone_neighborFinset_some]
  rw [Finset.card_insert_of_not_mem]
  · rw [Finset.card_image_of_injective]
    · omega
    · exact Option.some_injective
  · simp

@[simp] theorem card_option_vertices : Fintype.card (Option V) = Fintype.card V + 1 := by
  simp

/-- The cone commutes with adding an edge between old vertices. -/
theorem cone_sup_edge (G : SimpleGraph V) (u v : V) :
    cone (G ⊔ edge u v) = cone G ⊔ edge (some u) (some v) := by
  ext x y
  cases x <;> cases y <;> simp [cone, edge_adj, sup_adj]

#print axioms SimpleGraph.cone_degree_some
#print axioms SimpleGraph.cone_sup_edge

end SimpleGraph
