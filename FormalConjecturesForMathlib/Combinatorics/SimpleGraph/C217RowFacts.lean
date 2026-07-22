/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217OrderBound

/-!
# Degree-row facts for WOWII Conjecture 217

This module provides a small stable interface between an exact descending
degree-sequence equality and graph-level facts used by the exceptional-row
handlers.
-/

namespace SimpleGraph.C217RowFacts

open Classical
open SimpleGraph.C217OrderBound

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Vertices having degree exactly `d`. -/
def degreeClass (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : Finset V :=
  Finset.univ.filter fun v => G.degree v = d

@[simp] lemma mem_degreeClass (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (v : V) :
    v ∈ degreeClass G d ↔ G.degree v = d := by
  simp [degreeClass]

/-- Every vertex degree occurs in the sorted degree sequence. -/
lemma degree_mem_degreeSequence
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    G.degree v ∈ degreeSequence G := by
  have hv : G.degree v ∈ Finset.univ.val.map (fun x => G.degree x) := by
    exact Multiset.mem_map.mpr ⟨v, by simp, rfl⟩
  simpa [degreeSequence] using hv

/-- The multiplicity of `d` in the sorted sequence is the number of vertices
of degree `d`. -/
lemma card_degreeClass_eq_count_degreeSequence
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) :
    (degreeClass G d).card = (degreeSequence G).count d := by
  unfold degreeClass degreeSequence
  rw [← Multiset.count_coe, Multiset.sort_eq]
  simp

/-- An exact row equality determines the graph order. -/
lemma card_eq_length_of_degreeSequence_eq
    (G : SimpleGraph V) [DecidableRel G.Adj] {row : List ℕ}
    (hrow : degreeSequence G = row) :
    Fintype.card V = row.length := by
  rw [← degreeSequence_length G, hrow]

/-- An exact row equality determines every degree-class cardinality. -/
lemma card_degreeClass_of_degreeSequence_eq
    (G : SimpleGraph V) [DecidableRel G.Adj] {row : List ℕ}
    (hrow : degreeSequence G = row) (d : ℕ) :
    (degreeClass G d).card = row.count d := by
  rw [card_degreeClass_eq_count_degreeSequence, hrow]

/-- A bound holding for all entries of an exact row holds for every graph
vertex. -/
lemma degree_le_of_degreeSequence_eq
    (G : SimpleGraph V) [DecidableRel G.Adj] {row : List ℕ} {k : ℕ}
    (hrow : degreeSequence G = row)
    (hbound : ∀ d ∈ row, d ≤ k) :
    ∀ v, G.degree v ≤ k := by
  intro v
  apply hbound (G.degree v)
  rw [← hrow]
  exact degree_mem_degreeSequence G v

/-- A lower bound holding for all entries of an exact row holds for every
vertex. -/
lemma degree_ge_of_degreeSequence_eq
    (G : SimpleGraph V) [DecidableRel G.Adj] {row : List ℕ} {k : ℕ}
    (hrow : degreeSequence G = row)
    (hbound : ∀ d ∈ row, k ≤ d) :
    ∀ v, k ≤ G.degree v := by
  intro v
  apply hbound (G.degree v)
  rw [← hrow]
  exact degree_mem_degreeSequence G v

/-- If a row contains only the values in a finite list, every graph degree is
one of those values. -/
lemma degree_mem_values_of_degreeSequence_eq
    (G : SimpleGraph V) [DecidableRel G.Adj] {row values : List ℕ}
    (hrow : degreeSequence G = row)
    (hvalues : ∀ d ∈ row, d ∈ values) :
    ∀ v, G.degree v ∈ values := by
  intro v
  apply hvalues (G.degree v)
  rw [← hrow]
  exact degree_mem_degreeSequence G v

#print axioms SimpleGraph.C217RowFacts.degree_mem_degreeSequence
#print axioms SimpleGraph.C217RowFacts.card_degreeClass_eq_count_degreeSequence
#print axioms SimpleGraph.C217RowFacts.card_eq_length_of_degreeSequence_eq
#print axioms SimpleGraph.C217RowFacts.card_degreeClass_of_degreeSequence_eq
#print axioms SimpleGraph.C217RowFacts.degree_le_of_degreeSequence_eq
#print axioms SimpleGraph.C217RowFacts.degree_ge_of_degreeSequence_eq

end SimpleGraph.C217RowFacts
