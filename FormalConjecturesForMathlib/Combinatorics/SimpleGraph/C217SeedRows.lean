/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217CrossDegree
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217RowFacts

/-!
# Seed-completion exceptional rows for WOWII Conjecture 217

This file begins the row-level instantiation of the generic cross-degree and
path-closure completion lemmas.
-/

namespace SimpleGraph.C217SeedRows

open Classical
open SimpleGraph
open SimpleGraph.C217OrderBound
open SimpleGraph.C217RowFacts
open SimpleGraph.C217ClosureHelpers
open SimpleGraph.C217CrossDegree

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]

/-- The exceptional row `[3,3,2,2,2,2]` is traceable.

The two degree-three vertices form a universal set in the path closure. Their
original degree capacity is six, whereas the four outside degree-two vertices
demand eight cross incidences if no outside seed appears. The cross-degree
criterion therefore supplies a seed and completes the closure. -/
theorem row_332222
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (hrow : degreeSequence G = [3, 3, 2, 2, 2, 2]) :
    IsTraceable G := by
  let A : Finset V := degreeClass G 3
  have hn : Fintype.card V = 6 := by
    have h := card_eq_length_of_degreeSequence_eq G hrow
    norm_num at h
    exact h
  have hAcard : A.card = 2 := by
    have h := card_degreeClass_of_degreeSequence_eq G hrow 3
    norm_num at h
    simpa [A] using h
  have hdegCases : ∀ v, G.degree v = 3 ∨ G.degree v = 2 := by
    intro v
    have hmem := degree_mem_degreeSequence G v
    rw [hrow] at hmem
    simpa using hmem
  have hAdeg : ∀ a ∈ A, G.degree a = 3 := by
    intro a ha
    simpa [A] using ha
  have hBdeg : ∀ v ∉ A, G.degree v = 2 := by
    intro v hvA
    rcases hdegCases v with h3 | h2
    · exact (hvA (by simpa [A, h3])).elim
    · exact h2
  have huniv : ∀ a ∈ A, ∀ v, v ≠ a → (pathClosure G).Adj a v := by
    intro a ha v hav
    have hadeg := hAdeg a ha
    by_cases hvA : v ∈ A
    · have hvdeg := hAdeg v hvA
      apply pathClosure_adj_of_degree_sum G hav
      rw [hn, hadeg, hvdeg]
      norm_num
    · have hvdeg := hBdeg v hvA
      apply pathClosure_adj_of_degree_sum G hav
      rw [hn, hadeg, hvdeg]
      norm_num
  have hout : ∀ v ∉ A, 2 ≤ (pathClosure G).degree v := by
    intro v hvA
    have hvdeg := hBdeg v hvA
    have hmono : G.degree v ≤ (pathClosure G).degree v :=
      degree_le_of_le (v := v) (self_le_pathClosure G)
    omega
  have hBcard : (Finset.univ \ A).card = 4 := by
    rw [Finset.card_sdiff (Finset.subset_univ A), Finset.card_univ, hn, hAcard]
  have hsumA : (∑ a ∈ A, G.degree a) = 6 := by
    calc
      (∑ a ∈ A, G.degree a) = ∑ a ∈ A, 3 := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hAdeg a ha]
      _ = 6 := by simp [hAcard]
  have hsumB : (∑ v ∈ Finset.univ \ A, G.degree v) = 8 := by
    calc
      (∑ v ∈ Finset.univ \ A, G.degree v) = ∑ v ∈ Finset.univ \ A, 2 := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [hBdeg v (by simpa using hv)]
      _ = 8 := by simp [hBcard]
  apply isTraceable_of_universal_degree_sum_lt G A 2
  · omega
  · exact hAcard
  · exact huniv
  · exact hout
  · omega

#print axioms SimpleGraph.C217SeedRows.row_332222

end SimpleGraph.C217SeedRows
