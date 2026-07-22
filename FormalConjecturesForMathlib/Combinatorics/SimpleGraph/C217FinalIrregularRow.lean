/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217UniversalStages
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217RowFacts

/-!
# Final irregular low-degree row for WOWII Conjecture 217
-/

namespace SimpleGraph.C217FinalIrregularRow

open Classical
open SimpleGraph
open SimpleGraph.C217OrderBound
open SimpleGraph.C217RowFacts
open SimpleGraph.C217ClosureHelpers
open SimpleGraph.C217CrossDegree
open SimpleGraph.C217UniversalStages

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]

/-- The exceptional row `[5,5,5,4,4,4,4,4,4,3]` is traceable. -/
theorem row_5554444443
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (hrow : degreeSequence G = [5, 5, 5, 4, 4, 4, 4, 4, 4, 3]) :
    IsTraceable G := by
  let A : Finset V := degreeClass G 5
  let C : Finset V := degreeClass G 4
  let H : SimpleGraph V := pathClosure G
  have hn : Fintype.card V = 10 := by
    have h := card_eq_length_of_degreeSequence_eq G hrow
    norm_num at h
    exact h
  have hAcard : A.card = 3 := by
    have h := card_degreeClass_of_degreeSequence_eq G hrow 5
    norm_num at h
    simpa [A] using h
  have hCcard : C.card = 6 := by
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
  have hAA : ∀ a ∈ A, ∀ b ∈ A, b ≠ a → H.Adj a b := by
    intro a ha b hb hba
    apply pathClosure_adj_of_degree_sum G hba.symm
    rw [hn, hAdeg a ha, hAdeg b hb]
    norm_num
  have hAC : ∀ a ∈ A, ∀ c ∈ C, H.Adj a c := by
    intro a ha c hc
    have hac : a ≠ c := by
      intro h
      subst c
      exact (Finset.disjoint_left.mp hdisj a ha hc)
    apply pathClosure_adj_of_degree_sum G hac
    rw [hn, hAdeg a ha, hCdeg c hc]
    norm_num
  have hDdeg : ∀ v ∉ A ∪ C, 3 ≤ H.degree v := by
    intro v hv
    have hmono : G.degree v ≤ H.degree v :=
      degree_le_of_le (v := v) (self_le_pathClosure G)
    have hvdeg := hDdegG v hv
    omega
  have huniv : ∀ a ∈ A, ∀ v, v ≠ a → H.Adj a v := by
    apply universal_of_high_middle G A C 3 hdisj
    · exact hAA
    · exact hAC
    · exact hDdeg
    · rw [hn, hAcard, hCcard]
      norm_num
  have hsumA : (∑ a ∈ A, G.degree a) = 15 := by
    calc
      (∑ a ∈ A, G.degree a) = ∑ a ∈ A, 5 := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hAdeg a ha]
      _ = 15 := by simp [hAcard]
  have hseed : ∃ s ∈ C, 5 ≤ H.degree s := by
    by_contra hnone
    push_neg at hnone
    have hcrossC : ∀ c ∈ C, crossDegree G A c = 3 := by
      intro c hc
      have hcHle : H.degree c ≤ 4 := by
        have hnot := hnone c hc
        omega
      have hcG := hCdeg c hc
      have hmono : G.degree c ≤ H.degree c :=
        degree_le_of_le (v := c) (self_le_pathClosure G)
      have hcHeq : H.degree c = 4 := by omega
      have hall : ∀ a ∈ A, G.Adj c a := by
        intro a ha
        have hac : a ≠ c := by
          intro h
          subst c
          exact (Finset.disjoint_left.mp hdisj a ha hc)
        have hHadj : H.Adj c a := (huniv a ha c hac).symm
        by_contra hGadj
        have hlt := degree_lt_of_le_of_adj_of_not_adj
          (self_le_pathClosure G) hHadj hGadj
        omega
      unfold crossDegree
      calc
        (∑ a ∈ A, if G.Adj c a then 1 else 0) = ∑ a ∈ A, 1 := by
          apply Finset.sum_congr rfl
          intro a ha
          simp [hall a ha]
        _ = 3 := by simp [hAcard]
    have hsumC : (∑ c ∈ C, crossDegree G A c) = 18 := by
      calc
        (∑ c ∈ C, crossDegree G A c) = ∑ c ∈ C, 3 := by
          apply Finset.sum_congr rfl
          intro c hc
          rw [hcrossC c hc]
        _ = 18 := by simp [hCcard]
    have hCsub : C ⊆ Finset.univ \ A := by
      intro c hc
      have hcA : c ∉ A := by
        intro hcA
        exact Finset.disjoint_left.mp hdisj c hcA hc
      simp [hc, hcA]
    have hsumCB : (∑ c ∈ C, crossDegree G A c) ≤
        ∑ v ∈ Finset.univ \ A, crossDegree G A v := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hCsub
        (fun v hvB hvC => Nat.zero_le _)
    have hinLe :
        (∑ a ∈ A, crossDegree G (Finset.univ \ A) a) ≤
          ∑ a ∈ A, G.degree a := by
      exact Finset.sum_le_sum fun a ha =>
        crossDegree_le_degree G (Finset.univ \ A) a
    have hcross := sum_crossDegree_compl G A
    have hsumB : (∑ v ∈ Finset.univ \ A, crossDegree G A v) ≤ 15 := by
      rw [hcross]
      calc
        (∑ a ∈ A, crossDegree G (Finset.univ \ A) a) ≤
            ∑ a ∈ A, G.degree a := hinLe
        _ = 15 := hsumA
    omega
  obtain ⟨s, hsC, hsdeg⟩ := hseed
  have hsA : s ∉ A := by
    intro hs
    exact Finset.disjoint_left.mp hdisj s hs hsC
  have hsCAdj : ∀ c ∈ C, c ≠ s → H.Adj s c := by
    intro c hc hcs
    apply pathClosure_spec G hcs.symm
    have hcmono : G.degree c ≤ H.degree c :=
      degree_le_of_le (v := c) (self_le_pathClosure G)
    have hc4 := hCdeg c hc
    rw [hn]
    omega
  have hsEight : 8 ≤ H.degree s := by
    have hdisj' : Disjoint A (C.erase s) :=
      hdisj.mono (by rfl) (Finset.erase_subset s C)
    have hsub : A ∪ (C.erase s) ⊆ H.neighborFinset s := by
      intro x hx
      rw [Finset.mem_union] at hx
      rcases hx with hxA | hxC
      · have hxs : x ≠ s := by
          intro h
          subst x
          exact hsA hxA
        simpa using (huniv x hxA s hxs).symm
      · have hxe := Finset.mem_erase.mp hxC
        simpa using hsCAdj x hxe.2 hxe.1
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj', hAcard,
      Finset.card_erase_of_mem hsC, hCcard, card_neighborFinset_eq_degree] at hcard
    omega
  have hout : ∀ v ∉ A, 4 ≤ H.degree v := by
    intro v hvA
    by_cases hvC : v ∈ C
    · have hmono : G.degree v ≤ H.degree v :=
        degree_le_of_le (v := v) (self_le_pathClosure G)
      have hv4 := hCdeg v hvC
      omega
    · have hvD : v ∉ A ∪ C := by simp [hvA, hvC]
      have hv3 := hDdegG v hvD
      have hsv : H.Adj s v := by
        have hsvne : s ≠ v := by
          intro h
          subst v
          exact hvC hsC
        apply pathClosure_spec G hsvne
        have hvmono : G.degree v ≤ H.degree v :=
          degree_le_of_le (v := v) (self_le_pathClosure G)
        rw [hn]
        omega
      have hsub : insert s A ⊆ H.neighborFinset v := by
        intro x hx
        rw [Finset.mem_insert] at hx
        rcases hx with rfl | hxA
        · simpa using hsv.symm
        · have hxv : x ≠ v := by
            intro h
            subst x
            exact hvA hxA
          simpa using (huniv x hxA v hxv).symm
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hsA, hAcard,
        card_neighborFinset_eq_degree] at hcard
      omega
  have hsecond : ∃ t ∈ C, t ≠ s ∧ 5 ≤ H.degree t := by
    by_contra hnone
    push_neg at hnone
    have hsub : C.erase s ⊆ G.neighborFinset s := by
      intro t ht
      have hte := Finset.mem_erase.mp ht
      have htC := hte.2
      have hHadj := hsCAdj t htC hte.1
      by_contra hGadj
      have hlt : G.degree t < H.degree t :=
        degree_lt_of_le_of_adj_of_not_adj (self_le_pathClosure G) hHadj.symm hGadj
      have hnot5 := hnone t htC hte.1
      have ht4 := hCdeg t htC
      omega
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hsC, hCcard,
      card_neighborFinset_eq_degree, hCdeg s hsC] at hcard
    omega
  obtain ⟨t, htC, hts, htdeg⟩ := hsecond
  have htA : t ∉ A := by
    intro ht
    exact Finset.disjoint_left.mp hdisj t ht htC
  apply isTraceable_of_universal_two_seeds G A 4
  · omega
  · omega
  · simpa [H] using huniv
  · simpa [H] using hout
  · exact ⟨s, t, hsA, htA, hts.symm, by simpa [H] using hsdeg,
      by simpa [H] using htdeg⟩

#print axioms SimpleGraph.C217FinalIrregularRow.row_5554444443

end SimpleGraph.C217FinalIrregularRow
