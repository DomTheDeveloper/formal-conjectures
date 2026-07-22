/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217MixedChvatal
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217RowFacts

/-!
# The four mixed order-twelve rows for WOWII Conjecture 217
-/

namespace SimpleGraph.C217MixedRows

open Classical
open SimpleGraph
open SimpleGraph.C217OrderBound
open SimpleGraph.C217RowFacts
open SimpleGraph.C217ClosureHelpers
open SimpleGraph.C217UniversalStages
open SimpleGraph.C217MixedChvatal

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]

/-- Generic replicated-row theorem for degree classes six, five, and four. -/
theorem isTraceable_mixed_replicates
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a c d m : ℕ)
    (ha : 0 < a) (hc : 0 < c) (hd : 0 < d)
    (hcount : a + c + d = 12)
    (hstage : 11 ≤ (a - 1 + c) + 4)
    (hDsmall : d < 5)
    (houtside : c + d - m ≤ 6)
    (hforce : ∀ nC nD sC sD : ℕ,
      nC + sC = c → nD + sD = d → sC + sD < m →
      6 * a < a * nC + (a - 1) * nD)
    (hrow : degreeSequence G =
      List.replicate a 6 ++ List.replicate c 5 ++ List.replicate d 4) :
    IsTraceable G := by
  let A : Finset V := degreeClass G 6
  let C : Finset V := degreeClass G 5
  let D : Finset V := degreeClass G 4
  have hn : Fintype.card V = 12 := by
    have hlen := card_eq_length_of_degreeSequence_eq G hrow
    simp at hlen
    omega
  have hAcard : A.card = a := by
    have h := card_degreeClass_of_degreeSequence_eq G hrow 6
    simp [A, ha.ne', hc.ne', hd.ne'] at h
    exact h
  have hCcard : C.card = c := by
    have h := card_degreeClass_of_degreeSequence_eq G hrow 5
    simp [C, ha.ne', hc.ne', hd.ne'] at h
    exact h
  have hDcard : D.card = d := by
    have h := card_degreeClass_of_degreeSequence_eq G hrow 4
    simp [D, ha.ne', hc.ne', hd.ne'] at h
    exact h
  have hdegCases : ∀ v,
      G.degree v = 6 ∨ G.degree v = 5 ∨ G.degree v = 4 := by
    intro v
    have hmem := degree_mem_degreeSequence G v
    rw [hrow, List.mem_append, List.mem_append] at hmem
    simpa [ha.ne', hc.ne', hd.ne'] using hmem
  have hAC : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro x hxA hxC
    have h6 : G.degree x = 6 := by simpa [A] using hxA
    have h5 : G.degree x = 5 := by simpa [C] using hxC
    omega
  have hAD : Disjoint A D := by
    rw [Finset.disjoint_left]
    intro x hxA hxD
    have h6 : G.degree x = 6 := by simpa [A] using hxA
    have h4 : G.degree x = 4 := by simpa [D] using hxD
    omega
  have hCDdisj : Disjoint C D := by
    rw [Finset.disjoint_left]
    intro x hxC hxD
    have h5 : G.degree x = 5 := by simpa [C] using hxC
    have h4 : G.degree x = 4 := by simpa [D] using hxD
    omega
  have hAdeg : ∀ x ∈ A, G.degree x = 6 := by
    intro x hx
    simpa [A] using hx
  have hCdeg : ∀ x ∈ C, G.degree x = 5 := by
    intro x hx
    simpa [C] using hx
  have hDdeg : ∀ x ∈ D, G.degree x = 4 := by
    intro x hx
    simpa [D] using hx
  have hpart : A ∪ (C ∪ D) = Finset.univ := by
    ext v
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    rcases hdegCases v with h6 | h5 | h4
    · exact Or.inl (by simpa [A, h6])
    · exact Or.inr (Or.inl (by simpa [C, h5]))
    · exact Or.inr (Or.inr (by simpa [D, h4]))
  have hCD : C ∪ D = Finset.univ \ A := by
    ext v
    constructor
    · intro hv
      have hvnotA : v ∉ A := by
        rw [Finset.mem_union] at hv
        rcases hv with hvC | hvD
        · exact fun hvA => Finset.disjoint_left.mp hAC v hvA hvC
        · exact fun hvA => Finset.disjoint_left.mp hAD v hvA hvD
      simp [hv, hvnotA]
    · intro hv
      have hvA : v ∉ A := (Finset.mem_sdiff.mp hv).2
      have hvpart : v ∈ A ∪ (C ∪ D) := by
        rw [hpart]
        simp
      rw [Finset.mem_union] at hvpart
      exact hvpart.resolve_left hvA
  have hAA : ∀ x ∈ A, ∀ y ∈ A, y ≠ x →
      (pathClosure G).Adj x y := by
    intro x hx y hy hne
    apply pathClosure_adj_of_degree_sum G hne.symm
    rw [hAdeg x hx, hAdeg y hy, hn]
    norm_num
  have hAtoC : ∀ x ∈ A, ∀ y ∈ C, (pathClosure G).Adj x y := by
    intro x hx y hy
    have hne : x ≠ y := by
      intro h
      subst y
      exact Finset.disjoint_left.mp hAC x hx hy
    apply pathClosure_adj_of_degree_sum G hne
    rw [hAdeg x hx, hCdeg y hy, hn]
    norm_num
  have hDbase : ∀ x ∈ D, 4 ≤ (pathClosure G).degree x := by
    intro x hx
    have hmono : G.degree x ≤ (pathClosure G).degree x :=
      degree_le_of_le (v := x) (self_le_pathClosure G)
    rw [hDdeg x hx] at hmono
    exact hmono
  have huniv : ∀ x ∈ A, ∀ y, y ≠ x → (pathClosure G).Adj x y := by
    apply universal_of_high_middle G A C 4 hAC hAA hAtoC
    · intro v hv
      have hvA : v ∉ A := by
        intro hvA
        exact hv (Finset.mem_union.mpr (Or.inl hvA))
      have hvC : v ∉ C := by
        intro hvC
        exact hv (Finset.mem_union.mpr (Or.inr hvC))
      have hvCD : v ∈ C ∪ D := by
        rw [hCD]
        simp [hvA]
      exact hDbase v (hvCD.resolve_left hvC)
    · rw [hn, hAcard, hCcard]
      exact hstage
  have hAbase : ∀ x ∈ A, 6 ≤ (pathClosure G).degree x := by
    intro x hx
    have hmono : G.degree x ≤ (pathClosure G).degree x :=
      degree_le_of_le (v := x) (self_le_pathClosure G)
    rw [hAdeg x hx] at hmono
    exact hmono
  have hCbase : ∀ x ∈ C, 5 ≤ (pathClosure G).degree x := by
    intro x hx
    have hmono : G.degree x ≤ (pathClosure G).degree x :=
      degree_le_of_le (v := x) (self_le_pathClosure G)
    rw [hCdeg x hx] at hmono
    exact hmono
  have hsumA : (∑ x ∈ A, G.degree x) = 6 * a := by
    calc
      (∑ x ∈ A, G.degree x) = ∑ _x ∈ A, 6 := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hAdeg x hx]
      _ = 6 * a := by simp [hAcard, mul_comm]
  have hSeeds : m ≤ (sixSeedSet G A).card := by
    apply sixSeedSet_card_ge G A C D m hCD hCDdisj hCdeg hDdeg huniv
    intro nC nD sC sD hnC hnD hs
    rw [hsumA, hAcard, hCcard, hDcard]
    exact hforce nC nD sC sD hnC hnD hs
  have hCompCard : (Finset.univ \ A).card = c + d := by
    rw [← hCD, Finset.card_union_of_disjoint hCDdisj, hCcard, hDcard]
  apply isTraceable_of_mixed_sixSeeds G A C D m hn hCD hCDdisj
  · exact hAbase
  · exact huniv
  · exact hCbase
  · exact hDbase
  · simpa [hDcard] using hDsmall
  · exact hSeeds
  · rw [hCompCard]
    exact houtside

/-- Row 32: `[6^5,5^4,4^3]`. -/
theorem row_666665555444
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hrow : degreeSequence G = [6,6,6,6,6,5,5,5,5,4,4,4]) :
    IsTraceable G := by
  apply isTraceable_mixed_replicates G 5 4 3 1
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · intro nC nD sC sD hnC hnD hs
    omega
  · simpa using hrow

/-- Row 33: `[6^4,5^6,4^2]`. -/
theorem row_666655555544
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hrow : degreeSequence G = [6,6,6,6,5,5,5,5,5,5,4,4]) :
    IsTraceable G := by
  apply isTraceable_mixed_replicates G 4 6 2 2
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · intro nC nD sC sD hnC hnD hs
    omega
  · simpa using hrow

/-- Row 34: `[6^3,5^8,4]`. -/
theorem row_666555555554
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hrow : degreeSequence G = [6,6,6,5,5,5,5,5,5,5,5,4]) :
    IsTraceable G := by
  apply isTraceable_mixed_replicates G 3 8 1 3
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · intro nC nD sC sD hnC hnD hs
    omega
  · simpa using hrow

/-- Row 35: `[6^5,5^6,4]`. -/
theorem row_666665555554
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hrow : degreeSequence G = [6,6,6,6,6,5,5,5,5,5,5,4]) :
    IsTraceable G := by
  apply isTraceable_mixed_replicates G 5 6 1 1
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · intro nC nD sC sD hnC hnD hs
    omega
  · simpa using hrow

#print axioms SimpleGraph.C217MixedRows.isTraceable_mixed_replicates
#print axioms SimpleGraph.C217MixedRows.row_666665555444
#print axioms SimpleGraph.C217MixedRows.row_666655555544
#print axioms SimpleGraph.C217MixedRows.row_666555555554
#print axioms SimpleGraph.C217MixedRows.row_666665555554

end SimpleGraph.C217MixedRows
