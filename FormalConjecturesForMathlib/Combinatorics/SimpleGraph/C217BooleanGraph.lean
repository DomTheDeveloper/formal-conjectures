/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217HamiltonDP
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Residue

/-!
# Boolean graph model for the finite C217 certificates

A list of Boolean edge variables is interpreted canonically as an undirected
loopless graph.  The same model supplies Boolean tests for connectivity and an
exact degree-count profile.  The soundness lemmas below connect those tests to
Mathlib graph notions; generated LRAT certificates can therefore remain purely
Boolean.
-/

namespace SimpleGraph.C217BooleanGraph

open Classical

/-- Canonical row-major index for an unordered pair. -/
def pairIndex (n : ℕ) (i j : Fin n) : ℕ :=
  min i.val j.val * n + max i.val j.val

/-- Symmetric irreflexive Boolean adjacency extracted from a list. -/
def adjBool {n : ℕ} (bits : List Bool) (i j : Fin n) : Bool :=
  decide (i ≠ j) && bits.getD (pairIndex n i j) false

lemma adjBool_symm {n : ℕ} (bits : List Bool) (i j : Fin n) :
    adjBool bits i j = adjBool bits j i := by
  simp [adjBool, pairIndex, eq_comm, Nat.min_comm, Nat.max_comm]

lemma adjBool_loopless {n : ℕ} (bits : List Bool) (i : Fin n) :
    ¬adjBool bits i i := by
  simp [adjBool]

/-- The simple graph represented by a Boolean edge list. -/
def graphOfBits {n : ℕ} (bits : List Bool) : SimpleGraph (Fin n) :=
  SimpleGraph.mk' ⟨adjBool bits, ⟨adjBool_symm bits, adjBool_loopless bits⟩⟩

@[simp] theorem graphOfBits_adj {n : ℕ} (bits : List Bool) (i j : Fin n) :
    (graphOfBits bits).Adj i j ↔ adjBool bits i j = true := by
  rfl

/-- A cut has a crossing edge. -/
def cutCrossesBool {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Bool :=
  S.any fun u => (Finset.univ \ S).any fun v => decide (G.Adj u v)

/-- Boolean connectedness via the nonempty proper cut characterization. -/
def connectedCutBool {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Bool :=
  Finset.univ.powerset.all fun S =>
    if decide S.Nonempty && decide (S ≠ Finset.univ) then cutCrossesBool G S else true

/-- A connected graph passes the Boolean cut test. -/
theorem connectedCutBool_of_connected {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hG : G.Connected) :
    connectedCutBool G = true := by
  apply Finset.all_eq_true.mpr
  intro S hS
  by_cases hne : S.Nonempty
  · by_cases hproper : S ≠ Finset.univ
    · have hvout : ∃ v : V, v ∉ S := by
        by_contra h
        push_neg at h
        apply hproper
        exact Finset.eq_univ_iff_forall.mpr h
      obtain ⟨u, hu⟩ := hne
      obtain ⟨v, hv⟩ := hvout
      obtain ⟨p⟩ := hG.preconnected u v
      obtain ⟨d, hd, hdu, hdv⟩ := p.exists_boundary_dart (S : Set V) hu hv
      simp only [connectedCutBool, hne, hproper, decide_true, Bool.true_and, if_true]
      apply Finset.any_eq_true.mpr
      refine ⟨d.fst, hdu, ?_⟩
      apply Finset.any_eq_true.mpr
      refine ⟨d.snd, ?_, ?_⟩
      · simp [hdv]
      · simpa using d.adj
    · simp [connectedCutBool, hne, hproper]
  · simp [connectedCutBool, hne]

/-- Number of vertices of degree exactly `d`. -/
def degreeMultiplicity {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : ℕ :=
  (Finset.univ.filter fun v => G.degree v = d).card

/-- Exact degree-multiplicity profile for a proposed descending degree list. -/
def degreeProfileBool {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (row : List ℕ) : Bool :=
  decide (row.length = Fintype.card V) &&
    (List.range (Fintype.card V)).all fun d =>
      decide (degreeMultiplicity G d = row.count d)

/-- Sorting the graph degrees to `row` implies the Boolean multiplicity profile. -/
theorem degreeProfileBool_of_degreeSequence_eq {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (row : List ℕ) (hrow : degreeSequence G = row) :
    degreeProfileBool G row = true := by
  have hlen : row.length = Fintype.card V := by
    rw [← hrow, degreeSequence_length]
  have hperm : degreeSequence G ~
      (Finset.univ.toList.map fun v => G.degree v) := by
    rw [← Multiset.coe_eq_coe]
    simp [degreeSequence]
  apply Bool.and_eq_true.mpr
  refine ⟨by simpa using hlen, ?_⟩
  apply List.all_eq_true.mpr
  intro d hd
  have hcount : row.count d =
      (Finset.univ.toList.map fun v => G.degree v).count d := by
    rw [← hrow]
    exact hperm.count_eq d
  have hmult :
      (Finset.univ.toList.map fun v => G.degree v).count d =
        degreeMultiplicity G d := by
    rw [List.count_eq_countP, List.countP_map]
    rw [List.countP_eq_length_filter]
    rw [← List.toFinset_card_of_nodup ((Finset.nodup_toList _).filter _)]
    simp [degreeMultiplicity]
  simp [hcount, hmult]

#print axioms SimpleGraph.C217BooleanGraph.connectedCutBool_of_connected
#print axioms SimpleGraph.C217BooleanGraph.degreeProfileBool_of_degreeSequence_eq

end SimpleGraph.C217BooleanGraph
