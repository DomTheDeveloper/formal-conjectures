/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.ConeBasic
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.HamiltonianConstruct

/-!
# Hamilton paths and the graph cone

For a nontrivial finite graph, `G` has a Hamiltonian path iff its one-vertex
cone has a Hamiltonian cycle.
-/

namespace SimpleGraph

open Classical Walk Function

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- The predicate used by the WOWII statement. -/
def IsTraceable (G : SimpleGraph V) : Prop :=
  ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian

/-- Old vertices of the cone. -/
def coneOldSet : Set (Option V) := {x | x ≠ none}

/-- The old-vertex subtype of `Option V` is equivalent to `V`. -/
def coneOldEquiv : coneOldSet (V := V) ≃ V where
  toFun x :=
    match h : x.1 with
    | none => False.elim (x.2 h)
    | some v => v
  invFun v := ⟨some v, by simp [coneOldSet]⟩
  left_inv x := by
    rcases x with ⟨x, hx⟩
    cases x with
    | none => exact False.elim (hx rfl)
    | some v => rfl
  right_inv v := rfl

/-- Forget the subtype after inducing the cone on its old vertices. -/
def coneOldHom (G : SimpleGraph V) :
    (cone G).induce (coneOldSet (V := V)) →g G where
  toFun := coneOldEquiv
  map_rel' := by
    intro x y h
    rcases x with ⟨x, hx⟩
    rcases y with ⟨y, hy⟩
    cases x with
    | none => exact False.elim (hx rfl)
    | some u =>
      cases y with
      | none => exact False.elim (hy rfl)
      | some v => simpa [coneOldEquiv, cone, induce_adj] using h

lemma coneOldHom_bijective (G : SimpleGraph V) : Function.Bijective (coneOldHom G) :=
  (coneOldEquiv (V := V)).bijective

/-- A Hamiltonian path closes through the apex to a Hamiltonian cycle. -/
theorem cone_isHamiltonian_of_traceable [Nontrivial V]
    (hG : IsTraceable G) : IsHamiltonian (cone G) := by
  intro _
  obtain ⟨a, b, p, hp⟩ := hG
  let pm := p.map (coneSomeHom G)
  let q := (cone_adj_none_some G a).toWalk
    |>.append pm
    |>.concat (cone_adj_some_none G b)
  refine ⟨none, q, ?_⟩
  apply Walk.IsHamiltonianCycle.of_tail_toFinset
  · have hcard : 2 ≤ Fintype.card V := Fintype.one_lt_card
    simp [q, pm, hp.length_eq]
    omega
  · have hcard : 2 ≤ Fintype.card V := Fintype.one_lt_card
    simp
    omega
  · ext x
    cases x with
    | none => simp [q, pm]
    | some v => simp [q, pm, hp.mem_support v]

/-- Removing the apex from a Hamiltonian cycle of the cone gives a Hamiltonian
path in the original graph. -/
theorem traceable_of_cone_isHamiltonian [Nonempty V]
    (hG : IsHamiltonian (cone G)) : IsTraceable G := by
  have hcard : Fintype.card (Option V) ≠ 1 := by
    have hpos : 0 < Fintype.card V := Fintype.card_pos
    simp
    omega
  obtain ⟨a, q, hq⟩ := hG hcard
  have hnone : none ∈ q.support := hq.mem_support none
  let q0 := q.rotate none hnone
  have hq0 : q0.IsHamiltonianCycle := hq.rotate hnone
  have htail : q0.tail.IsHamiltonian := hq0.isHamiltonian_tail
  have htail_not_nil : ¬q0.tail.Nil := by
    rw [← not_nil_iff_lt_length]
    have hlen := length_tail_add_one hq0.not_nil
    have hthree := hq0.isCycle.three_le_length
    omega
  let r0 := q0.tail.dropLast
  have hsupport : r0.support ++ [none] = q0.tail.support := by
    simpa [r0] using support_dropLast_concat htail_not_nil
  have r0_path : r0.IsPath := htail.isPath.dropLast
  have r0_old : ∀ x ∈ r0.support, x ∈ coneOldSet (V := V) := by
    intro x hx
    change x ≠ none
    intro hxn
    subst x
    have hc := htail none
    rw [← hsupport, List.count_append] at hc
    simp at hc
    have : r0.support.count none = 0 := by omega
    exact (List.count_eq_zero.mp this) hx
  let r1 := r0.induce (coneOldSet (V := V)) r0_old
  have r1_path : r1.IsPath := by
    rw [Walk.isPath_def]
    simpa [r1, Walk.support_induce] using r0_path.support_nodup
  have r1_ham : r1.IsHamiltonian := r1_path.isHamiltonian_of_mem (fun z => by
    have hmem : z.1 ∈ q0.tail.support := htail.mem_support z.1
    rw [← hsupport, List.mem_append] at hmem
    have hmem0 : z.1 ∈ r0.support := hmem.resolve_right (by
      simp only [List.mem_singleton]
      exact z.2)
    simpa [r1, Walk.support_induce] using hmem0)
  let r2 := r1.map (coneOldHom G)
  exact ⟨_, _, r2, r1_ham.map (coneOldHom_bijective G)⟩

/-- Traceability is equivalent to Hamiltonicity of the cone. -/
theorem traceable_iff_cone_isHamiltonian [Nontrivial V] :
    IsTraceable G ↔ IsHamiltonian (cone G) :=
  ⟨cone_isHamiltonian_of_traceable, traceable_of_cone_isHamiltonian⟩

#print axioms SimpleGraph.cone_isHamiltonian_of_traceable
#print axioms SimpleGraph.traceable_of_cone_isHamiltonian
#print axioms SimpleGraph.traceable_iff_cone_isHamiltonian

end SimpleGraph
