/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217CrossDegree
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217RowFacts

/-!
# Seed-completion exceptional rows for WOWII Conjecture 217

This file instantiates the generic cross-degree and path-closure completion
lemmas on the low-degree exceptional rows.
-/

namespace SimpleGraph.C217SeedRows

open Classical
open SimpleGraph
open SimpleGraph.C217OrderBound
open SimpleGraph.C217RowFacts
open SimpleGraph.C217ClosureHelpers
open SimpleGraph.C217CrossDegree

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]

/-- The exceptional row `[3,3,2,2,2,2]` is traceable. -/
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

/-- The exceptional row `[5,4,4,3,3,3,3,3]` is traceable.

The degree-five vertex and the two degree-four vertices form a three-vertex
set `A`. Every pair touching `A` meets the order-seven path-closure threshold,
so `A` is universal immediately. The degree sum on `A` is thirteen, while the
five outside degree-three vertices have total degree fifteen. -/
theorem row_54433333
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (hrow : degreeSequence G = [5, 4, 4, 3, 3, 3, 3, 3]) :
    IsTraceable G := by
  let A5 : Finset V := degreeClass G 5
  let A4 : Finset V := degreeClass G 4
  let A : Finset V := A5 ∪ A4
  have hn : Fintype.card V = 8 := by
    have h := card_eq_length_of_degreeSequence_eq G hrow
    norm_num at h
    exact h
  have h5card : A5.card = 1 := by
    have h := card_degreeClass_of_degreeSequence_eq G hrow 5
    norm_num at h
    simpa [A5] using h
  have h4card : A4.card = 2 := by
    have h := card_degreeClass_of_degreeSequence_eq G hrow 4
    norm_num at h
    simpa [A4] using h
  have hdisj : Disjoint A5 A4 := by
    rw [Finset.disjoint_left]
    intro x hx5 hx4
    have h5 : G.degree x = 5 := by simpa [A5] using hx5
    have h4 : G.degree x = 4 := by simpa [A4] using hx4
    omega
  have hAcard : A.card = 3 := by
    rw [A, Finset.card_union_of_disjoint hdisj, h5card, h4card]
  have hdegCases : ∀ v, G.degree v = 5 ∨ G.degree v = 4 ∨ G.degree v = 3 := by
    intro v
    have hmem := degree_mem_degreeSequence G v
    rw [hrow] at hmem
    simpa using hmem
  have hAdeg : ∀ a ∈ A, 4 ≤ G.degree a := by
    intro a ha
    rw [A, Finset.mem_union] at ha
    rcases ha with ha5 | ha4
    · have : G.degree a = 5 := by simpa [A5] using ha5
      omega
    · have : G.degree a = 4 := by simpa [A4] using ha4
      omega
  have hBdeg : ∀ v ∉ A, G.degree v = 3 := by
    intro v hvA
    rcases hdegCases v with h5 | h4 | h3
    · exact (hvA (by simp [A, A5, h5])).elim
    · exact (hvA (by simp [A, A4, h4])).elim
    · exact h3
  have hsum5 : (∑ a ∈ A5, G.degree a) = 5 := by
    calc
      (∑ a ∈ A5, G.degree a) = ∑ a ∈ A5, 5 := by
        apply Finset.sum_congr rfl
        intro a ha
        have : G.degree a = 5 := by simpa [A5] using ha
        rw [this]
      _ = 5 := by simp [h5card]
  have hsum4 : (∑ a ∈ A4, G.degree a) = 8 := by
    calc
      (∑ a ∈ A4, G.degree a) = ∑ a ∈ A4, 4 := by
        apply Finset.sum_congr rfl
        intro a ha
        have : G.degree a = 4 := by simpa [A4] using ha
        rw [this]
      _ = 8 := by simp [h4card]
  have hsumA : (∑ a ∈ A, G.degree a) = 13 := by
    rw [A, Finset.sum_union hdisj, hsum5, hsum4]
  have hBcard : (Finset.univ \ A).card = 5 := by
    rw [Finset.card_sdiff (Finset.subset_univ A), Finset.card_univ, hn, hAcard]
  have hsumB : (∑ v ∈ Finset.univ \ A, G.degree v) = 15 := by
    calc
      (∑ v ∈ Finset.univ \ A, G.degree v) = ∑ v ∈ Finset.univ \ A, 3 := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [hBdeg v (by simpa using hv)]
      _ = 15 := by simp [hBcard]
  apply isTraceable_of_direct_universal_degree_sum_lt G A 3 4 3
  · omega
  · exact hAcard
  · exact hAdeg
  · intro v hvA
    rw [hBdeg v hvA]
  · omega
  · omega
  · omega

#print axioms SimpleGraph.C217SeedRows.row_332222
#print axioms SimpleGraph.C217SeedRows.row_54433333

end SimpleGraph.C217SeedRows
