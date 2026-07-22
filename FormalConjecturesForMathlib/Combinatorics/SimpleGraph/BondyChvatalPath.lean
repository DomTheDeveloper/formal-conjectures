/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.BondyChvatalEdge
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.ConeHamiltonian

/-!
# One-edge Bondy--Chvátal theorem for Hamiltonian paths

Adding a nonedge `uv` with `deg u + deg v ≥ n - 1` preserves traceability in
the reverse direction.
-/

namespace SimpleGraph

open Classical

variable {V : Type*} [Fintype V] [Nontrivial V] {G : SimpleGraph V}

/-- The one-edge closure lemma for Hamiltonian paths. -/
theorem isTraceable_of_sup_edge
    {u v : V} (hne : u ≠ v) (hnadj : ¬G.Adj u v)
    (hdeg : G.degree u + G.degree v ≥ Fintype.card V - 1)
    (hadd : IsTraceable (G ⊔ edge u v)) : IsTraceable G := by
  have hconeAdded : IsHamiltonian (cone (G ⊔ edge u v)) :=
    cone_isHamiltonian_of_traceable hadd
  rw [cone_sup_edge] at hconeAdded
  have hne' : some u ≠ some v := by simpa using hne
  have hnadj' : ¬(cone G).Adj (some u) (some v) := by simpa using hnadj
  have hdeg' :
      (cone G).degree (some u) + (cone G).degree (some v) ≥
        Fintype.card (Option V) := by
    simp only [cone_degree_some, card_option_vertices]
    have hcard : 2 ≤ Fintype.card V := Fintype.one_lt_card
    omega
  have hcone : IsHamiltonian (cone G) :=
    isHamiltonian_of_sup_edge hne' hnadj' hdeg' hconeAdded
  exact traceable_of_cone_isHamiltonian hcone

#print axioms SimpleGraph.isTraceable_of_sup_edge

end SimpleGraph
