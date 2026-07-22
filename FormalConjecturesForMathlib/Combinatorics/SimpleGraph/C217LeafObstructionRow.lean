/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217DoubleStar
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217RowFacts
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217ClosureHelpers

/-!
# The `[6^4,4^6]` leaf-obstruction row for WOWII Conjecture 217
-/

namespace SimpleGraph.C217LeafObstructionRow

open Classical
open SimpleGraph
open SimpleGraph.C217OrderBound
open SimpleGraph.C217RowFacts
open SimpleGraph.C217ClosureHelpers
open SimpleGraph.C217LeafWitness
open SimpleGraph.C217DoubleStar

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]

/-- The exceptional row `[6,6,6,6,4,4,4,4,4,4]` is traceable under the retained
leaf hypothesis `Ls G ≤ 6`. If an outside vertex gains a closure edge, one-seed
completion applies. Otherwise every high–low edge was already original, and a
double-star spanning tree has eight leaves. -/
theorem row_6666444444
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hL : Ls G ≤ 6)
    (hrow : degreeSequence G = [6,6,6,6,4,4,4,4,4,4]) :
    IsTraceable G := by
  let A : Finset V := degreeClass G 6
  let B : Finset V := degreeClass G 4
  let H : SimpleGraph V := pathClosure G
  have hn : Fintype.card V = 10 := by
    have h := card_eq_length_of_degreeSequence_eq G hrow
    norm_num at h
    exact h
  have hAcard : A.card = 4 := by
    have h := card_degreeClass_of_degreeSequence_eq G hrow 6
    norm_num at h
    simpa [A] using h
  have hBcard : B.card = 6 := by
    have h := card_degreeClass_of_degreeSequence_eq G hrow 4
    norm_num at h
    simpa [B] using h
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    have h6 : G.degree x = 6 := by simpa [A] using hxA
    have h4 : G.degree x = 4 := by simpa [B] using hxB
    omega
  have hcases : ∀ v, G.degree v = 6 ∨ G.degree v = 4 := by
    intro v
    have h := degree_mem_degreeSequence G v
    rw [hrow] at h
    simpa using h
  have hAdeg : ∀ a ∈ A, G.degree a = 6 := by
    intro a ha
    simpa [A] using ha
  have hBdeg : ∀ b ∈ B, G.degree b = 4 := by
    intro b hb
    simpa [B] using hb
  have hpart : A ∪ B = Finset.univ := by
    ext v
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    rcases hcases v with h6 | h4
    · exact Or.inl (by simpa [A, h6])
    · exact Or.inr (by simpa [B, h4])
  have huniv : ∀ a ∈ A, ∀ v, v ≠ a → H.Adj a v := by
    intro a ha v hav
    apply pathClosure_adj_of_degree_sum G hav
    rcases hcases v with h6 | h4
    · rw [hAdeg a ha, h6, hn]
      norm_num
    · rw [hAdeg a ha, h4, hn]
      norm_num
  have hout : ∀ v ∉ A, 4 ≤ H.degree v := by
    intro v hvA
    have hvB : v ∈ B := by
      have hvpart : v ∈ A ∪ B := by rw [hpart]; simp
      rw [Finset.mem_union] at hvpart
      exact hvpart.resolve_left hvA
    have hmono : G.degree v ≤ H.degree v :=
      degree_le_of_le (v := v) (self_le_pathClosure G)
    rw [hBdeg v hvB] at hmono
    exact hmono
  by_cases hseed : ∃ s ∉ A, 5 ≤ H.degree s
  · exact isTraceable_of_universal_seed G A 4 (by omega)
      (by omega) (by simpa [H] using huniv) (by simpa [H] using hout)
      (by simpa [H] using hseed)
  · push_neg at hseed
    have hOriginal : ∀ b ∈ B, ∀ a ∈ A, G.Adj b a := by
      intro b hb a ha
      have hab : a ≠ b := by
        intro h
        subst a
        exact Finset.disjoint_left.mp hdisj b ha hb
      have hHadj : H.Adj b a := (huniv a ha b hab).symm
      by_contra hGadj
      have hlt := degree_lt_of_le_of_adj_of_not_adj
        (self_le_pathClosure G) hHadj hGadj
      have hnot5 := hseed b (by
        intro hbA
        exact Finset.disjoint_left.mp hdisj b hbA hb)
      have hb4 := hBdeg b hb
      omega
    obtain ⟨a, ha⟩ : A.Nonempty := by
      rw [← Finset.card_pos, hAcard]
      norm_num
    obtain ⟨b, hb⟩ : B.Nonempty := by
      rw [← Finset.card_pos, hBcard]
      norm_num
    let T : SimpleGraph V := doubleStar A B a b
    have hTG : T ≤ G := by
      intro x y hxy
      rw [doubleStar_adj] at hxy
      rcases hxy.2 with h | h | h | h
      · subst x
        exact (hOriginal y h.2 a ha).symm
      · subst x
        exact hOriginal b hb y h.2
      · subst y
        exact hOriginal x h.2 a ha
      · subst y
        exact (hOriginal b hb x h.2).symm
    let S : G.Subgraph where
      verts := Set.univ
      Adj := T.Adj
      adj_sub := hTG
      edge_vert := by aesop
      symm := T.symm
    have hspan : S.IsSpanning := by
      intro v
      simp [S]
    have hspanningCoe : S.spanningCoe = T := by
      ext x y
      rfl
    have htreeT : T.IsTree := by
      exact isTree_doubleStar hpart hdisj ha hb
    have htreeS : S.IsTree := by
      apply (S.spanningCoe_isTree hspan).mpr
      simpa [hspanningCoe] using htreeT
    have hle : S ≤ G.toSubgraph := by
      constructor
      · intro v hv
        simp
      · intro x y hxy
        exact hTG hxy
    have hleafT : 8 ≤ T.toSubgraph.leafCount := by
      have h := noncenter_leaf_count_le hpart hdisj ha hb
      rw [hAcard, hBcard] at h
      norm_num at h ⊢
      exact h
    have hleafS : 8 ≤ S.leafCount := by
      simpa [S, T, Subgraph.leafCount] using hleafT
    have hleafReal : (8 : ℝ) ≤ (S.leafCount : ℝ) := by
      exact_mod_cast hleafS
    have hLsLower : (8 : ℝ) ≤ Ls G :=
      hleafReal.trans
        (leafCount_cast_le_Ls_of_spanningTree G S hspan htreeS hle)
    linarith

#print axioms SimpleGraph.C217LeafObstructionRow.row_6666444444

end SimpleGraph.C217LeafObstructionRow
