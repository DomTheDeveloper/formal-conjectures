/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.BondyChvatalPath
import Mathlib.Dynamics.FixedPoints.Increasing

/-!
# Bondy--Chvátal closure for Hamiltonian paths

The threshold is `n - 1`, as opposed to the Hamiltonian-cycle threshold `n`.
-/

namespace SimpleGraph

open Classical Function

variable {V : Type*} [Fintype V] [Nontrivial V]

/-- Nonedges eligible for one path-closure step. -/
def pathClosureNewEdges (G : SimpleGraph V) :=
  {uv : V × V |
    G.degree uv.1 + G.degree uv.2 ≥ Fintype.card V - 1 ∧
      uv.1 ≠ uv.2 ∧ ¬G.Adj uv.1 uv.2}

/-- Add one eligible path-closure edge, if one exists. -/
noncomputable def pathClosureStep (G : SimpleGraph V) : SimpleGraph V :=
  if h : (pathClosureNewEdges G).Nonempty then
    G ⊔ edge h.some.1 h.some.2
  else G

lemma self_le_pathClosureStep (G : SimpleGraph V) : G ≤ pathClosureStep G := by
  unfold pathClosureStep
  split_ifs <;> simp

lemma pathClosureStep_eq_iff (G : SimpleGraph V) : pathClosureStep G = G ↔
    ∀ {u v}, u ≠ v → G.degree u + G.degree v ≥ Fintype.card V - 1 → G.Adj u v := by
  unfold pathClosureStep pathClosureNewEdges
  split_ifs with h
  · have hne := h.some_mem.2.1
    have hnadj := h.some_mem.2.2
    constructor
    · intro heq
      have : (edge h.some.1 h.some.2) ≤ G := by
        simpa [sup_eq_left] using heq
      exact False.elim (hnadj (this ((edge_adj _ _).2 ⟨Or.inl ⟨rfl, rfl⟩, hne⟩)))
    · intro hall
      exact False.elim (hnadj (hall hne h.some_mem.1))
  · constructor
    · intro _ u v huv hdeg
      by_contra hnadj
      exact h ⟨(u, v), hdeg, huv, hnadj⟩
    · intro _
      rfl

/-- One path-closure step does not create traceability from nothing. -/
theorem isTraceable_of_pathClosureStep (G : SimpleGraph V)
    (h : IsTraceable (pathClosureStep G)) : IsTraceable G := by
  unfold pathClosureStep at h
  split_ifs at h with hn
  · exact isTraceable_of_sup_edge hn.some_mem.2.1 hn.some_mem.2.2 hn.some_mem.1 h
  · exact h

/-- Iterated Bondy--Chvátal path closure. -/
noncomputable def pathClosure (G : SimpleGraph V) : SimpleGraph V :=
  Function.eventualValue self_le_pathClosureStep G

lemma self_le_pathClosure (G : SimpleGraph V) : G ≤ pathClosure G := by
  rw [pathClosure]
  exact Function.self_le_eventualValue self_le_pathClosureStep G

lemma pathClosure_spec (G : SimpleGraph V) :
    ∀ {u v}, u ≠ v →
      (pathClosure G).degree u + (pathClosure G).degree v ≥ Fintype.card V - 1 →
      (pathClosure G).Adj u v := by
  have hfix : pathClosureStep (pathClosure G) = pathClosure G :=
    isFixedPt_eventualValue self_le_pathClosureStep G
  rwa [pathClosureStep_eq_iff] at hfix

private theorem not_traceable_iterate {G : SimpleGraph V} {n : ℕ}
    (hG : ¬IsTraceable G) : ¬IsTraceable (pathClosureStep^[n] G) := by
  induction n with
  | zero => simpa
  | succ m ih =>
    rw [add_comm]
    contrapose ih
    simp only [iterate_add_apply, iterate_one, Decidable.not_not] at ih ⊢
    exact isTraceable_of_pathClosureStep _ ih

/-- A graph is traceable iff its path closure is traceable. -/
theorem pathClosure_traceable_iff (G : SimpleGraph V) :
    IsTraceable (pathClosure G) ↔ IsTraceable G := by
  constructor
  · intro hG
    unfold pathClosure Function.eventualValue at hG
    by_contra h
    exact not_traceable_iterate h hG
  · exact fun hG => by
      obtain ⟨a, b, p, hp⟩ := hG
      exact ⟨a, b, p.mapLe (self_le_pathClosure G), by
        simpa [Walk.IsHamiltonian] using hp⟩

#print axioms SimpleGraph.pathClosure_spec
#print axioms SimpleGraph.pathClosure_traceable_iff

end SimpleGraph
