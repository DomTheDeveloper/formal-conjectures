/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217TwoBlockClosure
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217RowFacts

/-!
# Exact degree-sequence interface for the C217 two-block family
-/

namespace SimpleGraph.C217TwoBlockRows

open Classical
open SimpleGraph
open SimpleGraph.C217OrderBound
open SimpleGraph.C217RowFacts
open SimpleGraph.C217TwoBlockClosure

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]

/-- Every exact row `(h-1)^h,q^(q+1)` with `h ≥ q+2` is traceable. -/
theorem isTraceable_twoBlock_of_degreeSequence
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (h q : ℕ) (hhq : q + 2 ≤ h)
    (hrow : degreeSequence G =
      List.replicate h (h - 1) ++ List.replicate (q + 1) q) :
    IsTraceable G := by
  let A : Finset V := degreeClass G (h - 1)
  let B : Finset V := degreeClass G q
  have hne : h - 1 ≠ q := by omega
  have hn : Fintype.card V = h + q + 1 := by
    have hc := card_eq_length_of_degreeSequence_eq G hrow
    simp at hc
    omega
  have hAcard : A.card = h := by
    have hc := card_degreeClass_of_degreeSequence_eq G hrow (h - 1)
    simp [A, hne] at hc
    exact hc
  have hBcard : B.card = q + 1 := by
    have hc := card_degreeClass_of_degreeSequence_eq G hrow q
    simp [B, hne.symm] at hc
    exact hc
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    have hxa : G.degree x = h - 1 := by simpa [A] using hxA
    have hxb : G.degree x = q := by simpa [B] using hxB
    exact hne (hxa.symm.trans hxb)
  have hpart : A ∪ B = Finset.univ := by
    ext v
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    have hmem := degree_mem_degreeSequence G v
    rw [hrow, List.mem_append] at hmem
    simpa [A, B] using hmem
  have hAdeg : ∀ a ∈ A, G.degree a = h - 1 := by
    intro a ha
    simpa [A] using ha
  have hBdeg : ∀ b ∈ B, G.degree b = q := by
    intro b hb
    simpa [B] using hb
  exact isTraceable_twoBlock G hG A B h q hn hpart hdisj
    hAcard hBcard hAdeg hBdeg hhq

/-- The fifteen explicit certificate rows in the parametric two-block family. -/
def twoBlockRows : List (List ℕ) :=
  [ [2, 2, 2, 1, 1],
    [3, 3, 3, 3, 1, 1],
    [4, 4, 4, 4, 4, 1, 1],
    [5, 5, 5, 5, 5, 5, 1, 1],
    [6, 6, 6, 6, 6, 6, 6, 1, 1],
    [3, 3, 3, 3, 2, 2, 2],
    [4, 4, 4, 4, 4, 2, 2, 2],
    [5, 5, 5, 5, 5, 5, 2, 2, 2],
    [6, 6, 6, 6, 6, 6, 6, 2, 2, 2],
    [4, 4, 4, 4, 4, 3, 3, 3, 3],
    [5, 5, 5, 5, 5, 5, 3, 3, 3, 3],
    [6, 6, 6, 6, 6, 6, 6, 3, 3, 3, 3],
    [5, 5, 5, 5, 5, 5, 4, 4, 4, 4, 4],
    [6, 6, 6, 6, 6, 6, 6, 4, 4, 4, 4, 4],
    [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] ]

/-- Membership in the explicit family dispatches to the parametric theorem. -/
theorem isTraceable_of_mem_twoBlockRows
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (hrow : degreeSequence G ∈ twoBlockRows) :
    IsTraceable G := by
  simp only [twoBlockRows, List.mem_cons, List.mem_singleton] at hrow
  rcases hrow with hrow | hrow | hrow | hrow | hrow |
      hrow | hrow | hrow | hrow | hrow | hrow | hrow | hrow | hrow | hrow
  · apply isTraceable_twoBlock_of_degreeSequence G hG 3 1 (by norm_num)
    simpa using hrow
  · apply isTraceable_twoBlock_of_degreeSequence G hG 4 1 (by norm_num)
    simpa using hrow
  · apply isTraceable_twoBlock_of_degreeSequence G hG 5 1 (by norm_num)
    simpa using hrow
  · apply isTraceable_twoBlock_of_degreeSequence G hG 6 1 (by norm_num)
    simpa using hrow
  · apply isTraceable_twoBlock_of_degreeSequence G hG 7 1 (by norm_num)
    simpa using hrow
  · apply isTraceable_twoBlock_of_degreeSequence G hG 4 2 (by norm_num)
    simpa using hrow
  · apply isTraceable_twoBlock_of_degreeSequence G hG 5 2 (by norm_num)
    simpa using hrow
  · apply isTraceable_twoBlock_of_degreeSequence G hG 6 2 (by norm_num)
    simpa using hrow
  · apply isTraceable_twoBlock_of_degreeSequence G hG 7 2 (by norm_num)
    simpa using hrow
  · apply isTraceable_twoBlock_of_degreeSequence G hG 5 3 (by norm_num)
    simpa using hrow
  · apply isTraceable_twoBlock_of_degreeSequence G hG 6 3 (by norm_num)
    simpa using hrow
  · apply isTraceable_twoBlock_of_degreeSequence G hG 7 3 (by norm_num)
    simpa using hrow
  · apply isTraceable_twoBlock_of_degreeSequence G hG 6 4 (by norm_num)
    simpa using hrow
  · apply isTraceable_twoBlock_of_degreeSequence G hG 7 4 (by norm_num)
    simpa using hrow
  · apply isTraceable_twoBlock_of_degreeSequence G hG 7 5 (by norm_num)
    simpa using hrow

#print axioms SimpleGraph.C217TwoBlockRows.isTraceable_twoBlock_of_degreeSequence
#print axioms SimpleGraph.C217TwoBlockRows.isTraceable_of_mem_twoBlockRows

end SimpleGraph.C217TwoBlockRows
