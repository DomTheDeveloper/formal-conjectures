/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217UniversalStages
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217RowFacts

/-!
# Three-class seed rows for WOWII Conjecture 217
-/

namespace SimpleGraph.C217StagedSeedRows

open Classical
open SimpleGraph
open SimpleGraph.C217OrderBound
open SimpleGraph.C217RowFacts
open SimpleGraph.C217ClosureHelpers
open SimpleGraph.C217UniversalStages

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]

private lemma sum_compl_add_sum_eq_total
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) :
    (∑ v ∈ Finset.univ \ A, G.degree v) +
      (∑ a ∈ A, G.degree a) = ∑ v, G.degree v := by
  rw [← Finset.sum_union Finset.sdiff_disjoint,
    Finset.sdiff_union_of_subset (Finset.subset_univ A)]

/-- The row `[4,4,4,3,3,3,3,2]` is traceable. -/
theorem row_44433332
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (hrow : degreeSequence G = [4, 4, 4, 3, 3, 3, 3, 2]) :
    IsTraceable G := by
  let A : Finset V := degreeClass G 4
  let C : Finset V := degreeClass G 3
  have hn : Fintype.card V = 8 := by
    have h := card_eq_length_of_degreeSequence_eq G hrow
    norm_num at h
    exact h
  have hAcard : A.card = 3 := by
    have h := card_degreeClass_of_degreeSequence_eq G hrow 4
    norm_num at h
    simpa [A] using h
  have hCcard : C.card = 4 := by
    have h := card_degreeClass_of_degreeSequence_eq G hrow 3
    norm_num at h
    simpa [C] using h
  have hdisj : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro x hxA hxC
    have h4 : G.degree x = 4 := by simpa [A] using hxA
    have h3 : G.degree x = 3 := by simpa [C] using hxC
    omega
  have hdegCases : ∀ v, G.degree v = 4 ∨ G.degree v = 3 ∨ G.degree v = 2 := by
    intro v
    have hmem := degree_mem_degreeSequence G v
    rw [hrow] at hmem
    simpa using hmem
  have hAdeg : ∀ a ∈ A, G.degree a = 4 := by
    intro a ha
    simpa [A] using ha
  have hCdeg : ∀ c ∈ C, G.degree c = 3 := by
    intro c hc
    simpa [C] using hc
  have hDdegG : ∀ v ∉ A ∪ C, G.degree v = 2 := by
    intro v hv
    rcases hdegCases v with h4 | h3 | h2
    · exact (hv (by simp [A, h4])).elim
    · exact (hv (by simp [C, h3])).elim
    · exact h2
  have hAA : ∀ a ∈ A, ∀ b ∈ A, b ≠ a → (pathClosure G).Adj a b := by
    intro a ha b hb hba
    apply pathClosure_adj_of_degree_sum G hba.symm
    rw [hn, hAdeg a ha, hAdeg b hb]
    norm_num
  have hAC : ∀ a ∈ A, ∀ c ∈ C, (pathClosure G).Adj a c := by
    intro a ha c hc
    have hac : a ≠ c := by
      intro h
      subst c
      exact (Finset.disjoint_left.mp hdisj a ha hc)
    apply pathClosure_adj_of_degree_sum G hac
    rw [hn, hAdeg a ha, hCdeg c hc]
    norm_num
  have hDdeg : ∀ v ∉ A ∪ C, 2 ≤ (pathClosure G).degree v := by
    intro v hv
    have hmono : G.degree v ≤ (pathClosure G).degree v :=
      degree_le_of_le (v := v) (self_le_pathClosure G)
    have hvdeg := hDdegG v hv
    omega
  have hsumA : (∑ a ∈ A, G.degree a) = 12 := by
    calc
      (∑ a ∈ A, G.degree a) = ∑ a ∈ A, 4 := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hAdeg a ha]
      _ = 12 := by simp [hAcard]
  have htotal : (∑ v, G.degree v) = 26 := by
    rw [← degreeSequence_sum G, hrow]
    norm_num
  have hpartition := sum_compl_add_sum_eq_total G A
  have hsumB : (∑ v ∈ Finset.univ \ A, G.degree v) = 14 := by omega
  apply isTraceable_of_high_middle_degree_sum_lt G A C 3 2
  · omega
  · exact hAcard
  · exact hdisj
  · exact hAA
  · exact hAC
  · exact hDdeg
  · rw [hn, hAcard, hCcard]
    norm_num
  · omega

/-- The row `[5,5,5,5,4,4,4,4,3,3]` is traceable. -/
theorem row_5555444433
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (hrow : degreeSequence G = [5, 5, 5, 5, 4, 4, 4, 4, 3, 3]) :
    IsTraceable G := by
  let A : Finset V := degreeClass G 5
  let C : Finset V := degreeClass G 4
  have hn : Fintype.card V = 10 := by
    have h := card_eq_length_of_degreeSequence_eq G hrow
    norm_num at h
    exact h
  have hAcard : A.card = 4 := by
    have h := card_degreeClass_of_degreeSequence_eq G hrow 5
    norm_num at h
    simpa [A] using h
  have hCcard : C.card = 4 := by
    have h := card_degreeClass_of_degreeSequence_eq G hrow 4
    norm_num at h
    simpa [C] using h
  have hdisj : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro x hxA hxC
    have h5 : G.degree x = 5 := by simpa [A] using hxA
    have h4 : G.degree x = 4 := by simpa [C] using hxC
    omega
  have hdegCases : ∀ v, G.degree v = 5 ∨ G.degree v = 4 ∨ G.degree v = 3 := by
    intro v
    have hmem := degree_mem_degreeSequence G v
    rw [hrow] at hmem
    simpa using hmem
  have hAdeg : ∀ a ∈ A, G.degree a = 5 := by
    intro a ha
    simpa [A] using ha
  have hCdeg : ∀ c ∈ C, G.degree c = 4 := by
    intro c hc
    simpa [C] using hc
  have hDdegG : ∀ v ∉ A ∪ C, G.degree v = 3 := by
    intro v hv
    rcases hdegCases v with h5 | h4 | h3
    · exact (hv (by simp [A, h5])).elim
    · exact (hv (by simp [C, h4])).elim
    · exact h3
  have hAA : ∀ a ∈ A, ∀ b ∈ A, b ≠ a → (pathClosure G).Adj a b := by
    intro a ha b hb hba
    apply pathClosure_adj_of_degree_sum G hba.symm
    rw [hn, hAdeg a ha, hAdeg b hb]
    norm_num
  have hAC : ∀ a ∈ A, ∀ c ∈ C, (pathClosure G).Adj a c := by
    intro a ha c hc
    have hac : a ≠ c := by
      intro h
      subst c
      exact (Finset.disjoint_left.mp hdisj a ha hc)
    apply pathClosure_adj_of_degree_sum G hac
    rw [hn, hAdeg a ha, hCdeg c hc]
    norm_num
  have hDdeg : ∀ v ∉ A ∪ C, 3 ≤ (pathClosure G).degree v := by
    intro v hv
    have hmono : G.degree v ≤ (pathClosure G).degree v :=
      degree_le_of_le (v := v) (self_le_pathClosure G)
    have hvdeg := hDdegG v hv
    omega
  have hsumA : (∑ a ∈ A, G.degree a) = 20 := by
    calc
      (∑ a ∈ A, G.degree a) = ∑ a ∈ A, 5 := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hAdeg a ha]
      _ = 20 := by simp [hAcard]
  have htotal : (∑ v, G.degree v) = 42 := by
    rw [← degreeSequence_sum G, hrow]
    norm_num
  have hpartition := sum_compl_add_sum_eq_total G A
  have hsumB : (∑ v ∈ Finset.univ \ A, G.degree v) = 22 := by omega
  apply isTraceable_of_high_middle_degree_sum_lt G A C 4 3
  · omega
  · exact hAcard
  · exact hdisj
  · exact hAA
  · exact hAC
  · exact hDdeg
  · rw [hn, hAcard, hCcard]
    norm_num
  · omega

/-- The row `[6,5,5,5,4,4,4,4,4,3]` is traceable. -/
theorem row_6555444443
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (hrow : degreeSequence G = [6, 5, 5, 5, 4, 4, 4, 4, 4, 3]) :
    IsTraceable G := by
  let A6 : Finset V := degreeClass G 6
  let A5 : Finset V := degreeClass G 5
  let A : Finset V := A6 ∪ A5
  let C : Finset V := degreeClass G 4
  have hn : Fintype.card V = 10 := by
    have h := card_eq_length_of_degreeSequence_eq G hrow
    norm_num at h
    exact h
  have h6card : A6.card = 1 := by
    have h := card_degreeClass_of_degreeSequence_eq G hrow 6
    norm_num at h
    simpa [A6] using h
  have h5card : A5.card = 3 := by
    have h := card_degreeClass_of_degreeSequence_eq G hrow 5
    norm_num at h
    simpa [A5] using h
  have hCcard : C.card = 5 := by
    have h := card_degreeClass_of_degreeSequence_eq G hrow 4
    norm_num at h
    simpa [C] using h
  have h65disj : Disjoint A6 A5 := by
    rw [Finset.disjoint_left]
    intro x hx6 hx5
    have h6 : G.degree x = 6 := by simpa [A6] using hx6
    have h5 : G.degree x = 5 := by simpa [A5] using hx5
    omega
  have hAcard : A.card = 4 := by
    rw [A, Finset.card_union_of_disjoint h65disj, h6card, h5card]
  have hdisj : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro x hxA hxC
    rw [A, Finset.mem_union] at hxA
    have h4 : G.degree x = 4 := by simpa [C] using hxC
    rcases hxA with hx6 | hx5
    · have h6 : G.degree x = 6 := by simpa [A6] using hx6
      omega
    · have h5 : G.degree x = 5 := by simpa [A5] using hx5
      omega
  have hdegCases : ∀ v,
      G.degree v = 6 ∨ G.degree v = 5 ∨ G.degree v = 4 ∨ G.degree v = 3 := by
    intro v
    have hmem := degree_mem_degreeSequence G v
    rw [hrow] at hmem
    simpa using hmem
  have hAdeg : ∀ a ∈ A, 5 ≤ G.degree a := by
    intro a ha
    rw [A, Finset.mem_union] at ha
    rcases ha with ha6 | ha5
    · have : G.degree a = 6 := by simpa [A6] using ha6
      omega
    · have : G.degree a = 5 := by simpa [A5] using ha5
      omega
  have hCdeg : ∀ c ∈ C, G.degree c = 4 := by
    intro c hc
    simpa [C] using hc
  have hDdegG : ∀ v ∉ A ∪ C, G.degree v = 3 := by
    intro v hv
    rcases hdegCases v with h6 | h5 | h4 | h3
    · exact (hv (by simp [A, A6, h6])).elim
    · exact (hv (by simp [A, A5, h5])).elim
    · exact (hv (by simp [C, h4])).elim
    · exact h3
  have hAA : ∀ a ∈ A, ∀ b ∈ A, b ≠ a → (pathClosure G).Adj a b := by
    intro a ha b hb hba
    apply pathClosure_adj_of_degree_sum G hba.symm
    have ha5 := hAdeg a ha
    have hb5 := hAdeg b hb
    rw [hn]
    omega
  have hAC : ∀ a ∈ A, ∀ c ∈ C, (pathClosure G).Adj a c := by
    intro a ha c hc
    have hac : a ≠ c := by
      intro h
      subst c
      exact (Finset.disjoint_left.mp hdisj a ha hc)
    apply pathClosure_adj_of_degree_sum G hac
    have ha5 := hAdeg a ha
    have hc4 := hCdeg c hc
    rw [hn]
    omega
  have hDdeg : ∀ v ∉ A ∪ C, 3 ≤ (pathClosure G).degree v := by
    intro v hv
    have hmono : G.degree v ≤ (pathClosure G).degree v :=
      degree_le_of_le (v := v) (self_le_pathClosure G)
    have hvdeg := hDdegG v hv
    omega
  have hsum6 : (∑ a ∈ A6, G.degree a) = 6 := by
    calc
      (∑ a ∈ A6, G.degree a) = ∑ a ∈ A6, 6 := by
        apply Finset.sum_congr rfl
        intro a ha
        have : G.degree a = 6 := by simpa [A6] using ha
        rw [this]
      _ = 6 := by simp [h6card]
  have hsum5 : (∑ a ∈ A5, G.degree a) = 15 := by
    calc
      (∑ a ∈ A5, G.degree a) = ∑ a ∈ A5, 5 := by
        apply Finset.sum_congr rfl
        intro a ha
        have : G.degree a = 5 := by simpa [A5] using ha
        rw [this]
      _ = 15 := by simp [h5card]
  have hsumA : (∑ a ∈ A, G.degree a) = 21 := by
    rw [A, Finset.sum_union h65disj, hsum6, hsum5]
  have htotal : (∑ v, G.degree v) = 44 := by
    rw [← degreeSequence_sum G, hrow]
    norm_num
  have hpartition := sum_compl_add_sum_eq_total G A
  have hsumB : (∑ v ∈ Finset.univ \ A, G.degree v) = 23 := by omega
  apply isTraceable_of_high_middle_degree_sum_lt G A C 4 3
  · omega
  · exact hAcard
  · exact hdisj
  · exact hAA
  · exact hAC
  · exact hDdeg
  · rw [hn, hAcard, hCcard]
    norm_num
  · omega

#print axioms SimpleGraph.C217StagedSeedRows.row_44433332
#print axioms SimpleGraph.C217StagedSeedRows.row_5555444433
#print axioms SimpleGraph.C217StagedSeedRows.row_6555444443

end SimpleGraph.C217StagedSeedRows
