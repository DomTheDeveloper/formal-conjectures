/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217SeedRows

/-!
# The two-stage exceptional row for WOWII Conjecture 217
-/

namespace SimpleGraph.C217TwoStageRow

open Classical
open SimpleGraph
open SimpleGraph.C217OrderBound
open SimpleGraph.C217RowFacts
open SimpleGraph.C217ClosureHelpers
open SimpleGraph.C217CrossDegree

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]

/-- The exceptional row `[4,4,3,3,3,3,3,3]` is traceable.

The two degree-four vertices are universal in the path closure. If fewer than
two outside vertices gained degree, at least five outside vertices would retain
closure degree three. Every such vertex must already be adjacent in the
original graph to both high vertices, creating at least ten cross incidences,
while the two high vertices have total degree only eight. Hence two distinct
outside seeds exist, and the two-seed completion lemma closes the graph. -/
theorem row_44333333
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (hrow : degreeSequence G = [4, 4, 3, 3, 3, 3, 3, 3]) :
    IsTraceable G := by
  let A : Finset V := degreeClass G 4
  let H : SimpleGraph V := pathClosure G
  let B : Finset V := Finset.univ \ A
  have hn : Fintype.card V = 8 := by
    have h := card_eq_length_of_degreeSequence_eq G hrow
    norm_num at h
    exact h
  have hAcard : A.card = 2 := by
    have h := card_degreeClass_of_degreeSequence_eq G hrow 4
    norm_num at h
    simpa [A] using h
  have hBcard : B.card = 6 := by
    rw [B, Finset.card_sdiff (Finset.subset_univ A), Finset.card_univ, hn, hAcard]
  have hdegCases : ∀ v, G.degree v = 4 ∨ G.degree v = 3 := by
    intro v
    have hmem := degree_mem_degreeSequence G v
    rw [hrow] at hmem
    simpa using hmem
  have hAdeg : ∀ a ∈ A, G.degree a = 4 := by
    intro a ha
    simpa [A] using ha
  have hBdeg : ∀ v ∉ A, G.degree v = 3 := by
    intro v hvA
    rcases hdegCases v with h4 | h3
    · exact (hvA (by simpa [A, h4])).elim
    · exact h3
  have huniv : ∀ a ∈ A, ∀ v, v ≠ a → H.Adj a v := by
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
  have hout : ∀ v ∉ A, 3 ≤ H.degree v := by
    intro v hvA
    have hmono : G.degree v ≤ H.degree v :=
      degree_le_of_le (v := v) (self_le_pathClosure G)
    have hvdeg := hBdeg v hvA
    omega
  have hsumA : (∑ a ∈ A, G.degree a) = 8 := by
    calc
      (∑ a ∈ A, G.degree a) = ∑ a ∈ A, 4 := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hAdeg a ha]
      _ = 8 := by simp [hAcard]
  let S : Finset V := B.filter fun v => 4 ≤ H.degree v
  have hScard : 2 ≤ S.card := by
    by_contra hnot
    have hSle : S.card ≤ 1 := by omega
    let N : Finset V := B \ S
    have hSsubB : S ⊆ B := by
      intro v hv
      exact (Finset.mem_filter.mp (by simpa [S] using hv)).1
    have hNcard : 5 ≤ N.card := by
      rw [N, Finset.card_sdiff hSsubB, hBcard]
      omega
    have hNcross : ∀ v ∈ N, crossDegree G A v = 2 := by
      intro v hvN
      have hvB : v ∈ B := (Finset.mem_sdiff.mp (by simpa [N] using hvN)).1
      have hvS : v ∉ S := (Finset.mem_sdiff.mp (by simpa [N] using hvN)).2
      have hvA : v ∉ A := by simpa [B] using hvB
      have hHle : H.degree v ≤ 3 := by
        have hnot4 : ¬4 ≤ H.degree v := by
          intro h4
          exact hvS (by simp [S, hvB, h4])
        omega
      have hGv := hBdeg v hvA
      have hmono : G.degree v ≤ H.degree v :=
        degree_le_of_le (v := v) (self_le_pathClosure G)
      have hHv : H.degree v = 3 := by omega
      have hall : ∀ a ∈ A, G.Adj v a := by
        intro a ha
        have hav : a ≠ v := by
          intro h
          subst a
          exact hvA ha
        have hHadj : H.Adj v a := (huniv a ha v hav).symm
        by_contra hGadj
        have hlt : G.degree v < H.degree v :=
          degree_lt_of_le_of_adj_of_not_adj (self_le_pathClosure G) hHadj hGadj
        omega
      unfold crossDegree
      calc
        (∑ a ∈ A, if G.Adj v a then 1 else 0) = ∑ a ∈ A, 1 := by
          apply Finset.sum_congr rfl
          intro a ha
          simp [hall a ha]
        _ = 2 := by simp [hAcard]
    have hsumN : (∑ v ∈ N, crossDegree G A v) = 2 * N.card := by
      calc
        (∑ v ∈ N, crossDegree G A v) = ∑ v ∈ N, 2 := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [hNcross v hv]
        _ = 2 * N.card := by simp [mul_comm]
    have hNB : N ⊆ B := Finset.sdiff_subset
    have hsumNB : (∑ v ∈ N, crossDegree G A v) ≤
        ∑ v ∈ B, crossDegree G A v := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hNB
        (fun v hvB hvN => Nat.zero_le _)
    have hinLe : (∑ a ∈ A, crossDegree G B a) ≤
        ∑ a ∈ A, G.degree a := by
      exact Finset.sum_le_sum fun a ha => crossDegree_le_degree G B a
    have hcross : (∑ v ∈ B, crossDegree G A v) =
        ∑ a ∈ A, crossDegree G B a := by
      simpa [B] using sum_crossDegree_compl G A
    have hsumBcross : (∑ v ∈ B, crossDegree G A v) ≤ 8 := by
      rw [hcross]
      calc
        (∑ a ∈ A, crossDegree G B a) ≤ ∑ a ∈ A, G.degree a := hinLe
        _ = 8 := hsumA
    omega
  have hSnon : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨s, hsS⟩ := hSnon
  have hErasePos : 0 < (S.erase s).card := by
    rw [Finset.card_erase_of_mem hsS]
    omega
  obtain ⟨t, htErase⟩ := Finset.card_pos.mp hErasePos
  have htInfo := Finset.mem_erase.mp htErase
  have htS : t ∈ S := htInfo.2
  have hst : s ≠ t := htInfo.1.symm
  have hsData : s ∈ B ∧ 4 ≤ H.degree s := by simpa [S] using hsS
  have htData : t ∈ B ∧ 4 ≤ H.degree t := by simpa [S] using htS
  apply isTraceable_of_universal_two_seeds G A 3
  · omega
  · omega
  · simpa [H] using huniv
  · simpa [H] using hout
  · refine ⟨s, t, ?_, ?_, hst, ?_, ?_⟩
    · simpa [B] using hsData.1
    · simpa [B] using htData.1
    · simpa [H] using hsData.2
    · simpa [H] using htData.2

#print axioms SimpleGraph.C217TwoStageRow.row_44333333

end SimpleGraph.C217TwoStageRow
