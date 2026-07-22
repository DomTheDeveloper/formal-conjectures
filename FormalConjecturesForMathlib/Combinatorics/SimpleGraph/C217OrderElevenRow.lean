/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217CrossDegree
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217RowFacts

/-!
# The order-eleven exceptional row for WOWII Conjecture 217
-/

namespace SimpleGraph.C217OrderElevenRow

open Classical
open SimpleGraph
open SimpleGraph.C217OrderBound
open SimpleGraph.C217RowFacts
open SimpleGraph.C217ClosureHelpers
open SimpleGraph.C217CrossDegree

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]

/-- The exceptional row `[6,6,6,6,5,5,4,4,4,4,4]` is traceable. -/
theorem row_66665544444
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hrow : degreeSequence G = [6,6,6,6,5,5,4,4,4,4,4]) :
    IsTraceable G := by
  let A : Finset V := degreeClass G 6
  let C : Finset V := degreeClass G 5
  let D : Finset V := degreeClass G 4
  let H : SimpleGraph V := pathClosure G
  have hn : Fintype.card V = 11 := by
    have h := card_eq_length_of_degreeSequence_eq G hrow
    norm_num at h
    exact h
  have hAcard : A.card = 4 := by
    have h := card_degreeClass_of_degreeSequence_eq G hrow 6
    norm_num at h
    simpa [A] using h
  have hCcard : C.card = 2 := by
    have h := card_degreeClass_of_degreeSequence_eq G hrow 5
    norm_num at h
    simpa [C] using h
  have hDcard : D.card = 5 := by
    have h := card_degreeClass_of_degreeSequence_eq G hrow 4
    norm_num at h
    simpa [D] using h
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
  have hdegCases : ∀ v,
      G.degree v = 6 ∨ G.degree v = 5 ∨ G.degree v = 4 := by
    intro v
    have h := degree_mem_degreeSequence G v
    rw [hrow] at h
    simpa using h
  have hAdeg : ∀ a ∈ A, G.degree a = 6 := by
    intro a ha
    simpa [A] using ha
  have hCdeg : ∀ c ∈ C, G.degree c = 5 := by
    intro c hc
    simpa [C] using hc
  have hDdeg : ∀ d ∈ D, G.degree d = 4 := by
    intro d hd
    simpa [D] using hd
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
      have hvA : v ∉ A := by
        rw [Finset.mem_union] at hv
        rcases hv with hvC | hvD
        · exact fun hvA => Finset.disjoint_left.mp hAC v hvA hvC
        · exact fun hvA => Finset.disjoint_left.mp hAD v hvA hvD
      simp [hv, hvA]
    · intro hv
      have hvA : v ∉ A := (Finset.mem_sdiff.mp hv).2
      have hvpart : v ∈ A ∪ (C ∪ D) := by
        rw [hpart]
        simp
      rw [Finset.mem_union] at hvpart
      exact hvpart.resolve_left hvA
  have huniv : ∀ a ∈ A, ∀ v, v ≠ a → H.Adj a v := by
    intro a ha v hav
    apply pathClosure_adj_of_degree_sum G hav
    rcases hdegCases v with h6 | h5 | h4
    · rw [hAdeg a ha, h6, hn]
      norm_num
    · rw [hAdeg a ha, h5, hn]
      norm_num
    · rw [hAdeg a ha, h4, hn]
      norm_num
  have hAbase : ∀ a ∈ A, 6 ≤ H.degree a := by
    intro a ha
    have hmono : G.degree a ≤ H.degree a :=
      degree_le_of_le (v := a) (self_le_pathClosure G)
    rw [hAdeg a ha] at hmono
    exact hmono
  have hCbase : ∀ c ∈ C, 5 ≤ H.degree c := by
    intro c hc
    have hmono : G.degree c ≤ H.degree c :=
      degree_le_of_le (v := c) (self_le_pathClosure G)
    rw [hCdeg c hc] at hmono
    exact hmono
  have hDbase : ∀ d ∈ D, 4 ≤ H.degree d := by
    intro d hd
    have hmono : G.degree d ≤ H.degree d :=
      degree_le_of_le (v := d) (self_le_pathClosure G)
    rw [hDdeg d hd] at hmono
    exact hmono
  have hsumA : (∑ a ∈ A, G.degree a) = 24 := by
    calc
      (∑ a ∈ A, G.degree a) = ∑ _a ∈ A, 6 := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hAdeg a ha]
      _ = 24 := by simp [hAcard]
  have hseed : ∃ d ∈ D, 5 ≤ H.degree d := by
    by_contra hnone
    push_neg at hnone
    have hDOriginal : ∀ d ∈ D, ∀ a ∈ A, G.Adj d a := by
      intro d hd a ha
      have had : a ≠ d := by
        intro h
        subst a
        exact Finset.disjoint_left.mp hAD d ha hd
      have hHadj : H.Adj d a := (huniv a ha d had).symm
      by_contra hGadj
      have hlt := degree_lt_of_le_of_adj_of_not_adj
        (self_le_pathClosure G) hHadj hGadj
      have hnot5 := hnone d hd
      have hd4 := hDdeg d hd
      omega
    have hMissingC : ∃ c ∈ C, ∃ a ∈ A, ¬G.Adj c a := by
      by_contra hmiss
      push_neg at hmiss
      have hcrossD : (∑ d ∈ D, crossDegree G A d) = 20 := by
        calc
          (∑ d ∈ D, crossDegree G A d) = ∑ _d ∈ D, 4 := by
            apply Finset.sum_congr rfl
            intro d hd
            unfold crossDegree
            calc
              (∑ a ∈ A, if G.Adj d a then 1 else 0) = ∑ _a ∈ A, 1 := by
                apply Finset.sum_congr rfl
                intro a ha
                simp [hDOriginal d hd a ha]
              _ = 4 := by simp [hAcard]
          _ = 20 := by simp [hDcard]
      have hcrossC : (∑ c ∈ C, crossDegree G A c) = 8 := by
        calc
          (∑ c ∈ C, crossDegree G A c) = ∑ _c ∈ C, 4 := by
            apply Finset.sum_congr rfl
            intro c hc
            unfold crossDegree
            calc
              (∑ a ∈ A, if G.Adj c a then 1 else 0) = ∑ _a ∈ A, 1 := by
                apply Finset.sum_congr rfl
                intro a ha
                simp [hmiss c hc a ha]
              _ = 4 := by simp [hAcard]
          _ = 8 := by simp [hCcard]
      have houtSum :
          (∑ v ∈ Finset.univ \ A, crossDegree G A v) = 28 := by
        rw [← hCD, Finset.sum_union hCDdisj, hcrossC, hcrossD]
      have hcrossLe : (∑ v ∈ Finset.univ \ A, crossDegree G A v) ≤
          ∑ a ∈ A, G.degree a := by
        rw [sum_crossDegree_compl G A]
        exact Finset.sum_le_sum fun a ha =>
          crossDegree_le_degree G (Finset.univ \ A) a
      rw [houtSum, hsumA] at hcrossLe
      omega
    obtain ⟨c, hc, a, ha, hca⟩ := hMissingC
    have hcaH : H.Adj c a := (huniv a ha c (by
      intro h
      subst a
      exact Finset.disjoint_left.mp hAC c ha hc)).symm
    have hcSix : 6 ≤ H.degree c := by
      have hlt := degree_lt_of_le_of_adj_of_not_adj
        (self_le_pathClosure G) hcaH hca
      rw [hCdeg c hc] at hlt
      omega
    obtain ⟨d, hd⟩ : D.Nonempty := by
      rw [← Finset.card_pos, hDcard]
      norm_num
    have hcd : H.Adj c d := by
      have hne : c ≠ d := by
        intro h
        subst d
        exact Finset.disjoint_left.mp hCDdisj c hc hd
      apply pathClosure_spec G hne
      have hd4 := hDbase d hd
      rw [hn]
      omega
    have hsub : insert c A ⊆ H.neighborFinset d := by
      intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hxA
      · simpa using hcd.symm
      · have hxd : x ≠ d := by
          intro h
          subst x
          exact Finset.disjoint_left.mp hAD d hxA hd
        simpa using (huniv x hxA d hxd).symm
    have hcA : c ∉ A := by
      intro hcA
      exact Finset.disjoint_left.mp hAC c hcA hc
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hcA, hAcard,
      card_neighborFinset_eq_degree] at hcard
    have hnot5 := hnone d hd
    omega
  obtain ⟨d, hdD, hd5⟩ := hseed
  have hcond : ChvatalPathCondition H := by
    intro i hi hmid
    rw [hn] at hmid
    have hicases : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
      omega
    rcases hicases with rfl | rfl | rfl | rfl | rfl
    · left
      have hempty : lowDegreeFinset H 1 = ∅ := by
        ext v
        simp [lowDegreeFinset]
      simp [hempty]
    · left
      have hempty : lowDegreeFinset H 2 = ∅ := by
        ext v
        simp [lowDegreeFinset]
        rcases hdegCases v with h6 | h5 | h4
        all_goals
          have hmono : G.degree v ≤ H.degree v :=
            degree_le_of_le (v := v) (self_le_pathClosure G)
          omega
      simp [hempty]
    · left
      have hempty : lowDegreeFinset H 3 = ∅ := by
        ext v
        simp [lowDegreeFinset]
        rcases hdegCases v with h6 | h5 | h4
        all_goals
          have hmono : G.degree v ≤ H.degree v :=
            degree_le_of_le (v := v) (self_le_pathClosure G)
          omega
      simp [hempty]
    · left
      have hempty : lowDegreeFinset H 4 = ∅ := by
        ext v
        simp [lowDegreeFinset]
        rcases hdegCases v with h6 | h5 | h4
        all_goals
          have hmono : G.degree v ≤ H.degree v :=
            degree_le_of_le (v := v) (self_le_pathClosure G)
          omega
      simp [hempty]
    · left
      have hsub : lowDegreeFinset H 5 ⊆ D.erase d := by
        intro v hv
        have hvlt : H.degree v < 5 := by simpa [lowDegreeFinset] using hv
        have hvD : v ∈ D := by
          rcases hdegCases v with h6 | h5 | h4
          · have hmono : G.degree v ≤ H.degree v :=
              degree_le_of_le (v := v) (self_le_pathClosure G)
            omega
          · have hmono : G.degree v ≤ H.degree v :=
              degree_le_of_le (v := v) (self_le_pathClosure G)
            omega
          · simpa [D, h4]
        exact Finset.mem_erase.mpr ⟨by
          intro h
          subst v
          omega, hvD⟩
      have hc := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hdD, hDcard] at hc
      omega
  have hTraceH := isTraceable_of_chvatalPathCondition H hcond
  exact (pathClosure_traceable_iff G).mp hTraceH

#print axioms SimpleGraph.C217OrderElevenRow.row_66665544444

end SimpleGraph.C217OrderElevenRow
