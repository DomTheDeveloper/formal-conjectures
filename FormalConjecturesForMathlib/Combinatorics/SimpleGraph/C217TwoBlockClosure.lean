/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217ClosureHelpers
import Lean.Elab.Tactic.Omega

/-!
# Parametric two-block closure for WOWII Conjecture 217

This is the uniform argument for degree rows

`(h - 1 repeated h times, q repeated q + 1 times)`

with `h ≥ q + 2`. It covers fifteen of the forty exceptional rows.
-/

namespace SimpleGraph.C217TwoBlockClosure

open Classical
open SimpleGraph
open SimpleGraph.C217ClosureHelpers

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]

/-- The parametric two-block degree pattern has complete path closure and is
therefore traceable. -/
theorem isTraceable_twoBlock
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (A B : Finset V) (h q : ℕ)
    (hn : Fintype.card V = h + q + 1)
    (hpart : A ∪ B = Finset.univ)
    (hdisj : Disjoint A B)
    (hAcard : A.card = h)
    (hBcard : B.card = q + 1)
    (hAdeg : ∀ a ∈ A, G.degree a = h - 1)
    (hBdeg : ∀ b ∈ B, G.degree b = q)
    (hhq : q + 2 ≤ h) :
    IsTraceable G := by
  let H : SimpleGraph V := pathClosure G
  have hAne : A.Nonempty := by
    rw [← Finset.card_pos, hAcard]
    omega
  have hBne : B.Nonempty := by
    rw [← Finset.card_pos, hBcard]
    omega
  have hAclique : ∀ a ∈ A, ∀ a' ∈ A, a' ≠ a → H.Adj a a' := by
    intro a ha a' ha' hne
    apply pathClosure_adj_of_degree_sum G hne.symm
    rw [hn, hAdeg a ha, hAdeg a' ha']
    omega
  let Ap : Finset V := A.filter fun a => ∃ b ∈ B, G.Adj a b
  have hApSub : Ap ⊆ A := by
    intro a ha
    exact (Finset.mem_filter.mp (by simpa [Ap] using ha)).1
  have hApNe : Ap.Nonempty := by
    obtain ⟨a₀, ha₀⟩ := hAne
    obtain ⟨b₀, hb₀⟩ := hBne
    have hb₀A : b₀ ∉ A := by
      intro hbA
      exact Finset.disjoint_left.mp hdisj b₀ hbA hb₀
    obtain ⟨p⟩ := hG.preconnected a₀ b₀
    obtain ⟨d, _, hdA, hdnotA⟩ :=
      p.exists_boundary_dart (A : Set V) ha₀ hb₀A
    have hdB : d.snd ∈ B := by
      have hmem : d.snd ∈ A ∪ B := by
        rw [hpart]
        simp
      rw [Finset.mem_union] at hmem
      exact hmem.resolve_left hdnotA
    refine ⟨d.fst, ?_⟩
    simp only [Ap, Finset.mem_filter]
    exact ⟨hdA, d.snd, hdB, d.adj⟩
  have hApDegree : ∀ a ∈ Ap, h ≤ H.degree a := by
    intro a haAp
    have haA : a ∈ A := hApSub haAp
    obtain ⟨b, hbB, hab⟩ := (Finset.mem_filter.mp (by simpa [Ap] using haAp)).2
    have hbA : b ∉ A := by
      intro hbA
      exact Finset.disjoint_left.mp hdisj b hbA hbB
    have hsub : insert b (A.erase a) ⊆ H.neighborFinset a := by
      intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hxA
      · have : H.Adj a b := (self_le_pathClosure G) hab
        simpa using this
      · have hxe := Finset.mem_erase.mp hxA
        simpa using hAclique a haA x hxe.2 hxe.1
    have hcard := Finset.card_le_card hsub
    have hbErase : b ∉ A.erase a := by simp [hbA]
    rw [Finset.card_insert_of_notMem hbErase,
      Finset.card_erase_of_mem haA, hAcard,
      card_neighborFinset_eq_degree] at hcard
    omega
  have hApB : ∀ a ∈ Ap, ∀ b ∈ B, H.Adj a b := by
    intro a ha b hb
    have hab : a ≠ b := by
      intro h
      subst b
      exact Finset.disjoint_left.mp hdisj a (hApSub ha) hb
    apply pathClosure_spec G hab
    have hbmono : G.degree b ≤ H.degree b :=
      degree_le_of_le (v := b) (self_le_pathClosure G)
    have haH := hApDegree a ha
    have hbG := hBdeg b hb
    rw [hn]
    omega
  by_cases hnew : ∃ a ∈ Ap, ∃ b ∈ B, ¬G.Adj a b
  · obtain ⟨a₁, ha₁, b₁, hb₁, hnewEdge⟩ := hnew
    have hbSeed : q + 1 ≤ H.degree b₁ := by
      have hlt : G.degree b₁ < H.degree b₁ :=
        degree_lt_of_le_of_adj_of_not_adj
          (self_le_pathClosure G) (hApB a₁ ha₁ b₁ hb₁).symm hnewEdge.symm
      rw [hBdeg b₁ hb₁] at hlt
      omega
    have hAB : ∀ a ∈ A, ∀ b ∈ B, H.Adj a b := by
      intro a ha b hb
      by_cases haAp : a ∈ Ap
      · exact hApB a haAp b hb
      · have haBase : h - 1 ≤ H.degree a := by
          have hsub : A.erase a ⊆ H.neighborFinset a := by
            intro x hx
            have hxe := Finset.mem_erase.mp hx
            simpa using hAclique a ha x hxe.2 hxe.1
          have hcard := Finset.card_le_card hsub
          rw [Finset.card_erase_of_mem ha, hAcard,
            card_neighborFinset_eq_degree] at hcard
          exact hcard
        have hab₁ : H.Adj a b₁ := by
          have habne : a ≠ b₁ := by
            intro h
            subst b₁
            exact Finset.disjoint_left.mp hdisj a ha hb₁
          apply pathClosure_spec G habne
          rw [hn]
          omega
        have haHigh : h ≤ H.degree a := by
          have hb₁A : b₁ ∉ A := by
            intro hbA
            exact Finset.disjoint_left.mp hdisj b₁ hbA hb₁
          have hsub : insert b₁ (A.erase a) ⊆ H.neighborFinset a := by
            intro x hx
            rw [Finset.mem_insert] at hx
            rcases hx with rfl | hxA
            · simpa using hab₁
            · have hxe := Finset.mem_erase.mp hxA
              simpa using hAclique a ha x hxe.2 hxe.1
          have hcard := Finset.card_le_card hsub
          have hbErase : b₁ ∉ A.erase a := by simp [hb₁A]
          rw [Finset.card_insert_of_notMem hbErase,
            Finset.card_erase_of_mem ha, hAcard,
            card_neighborFinset_eq_degree] at hcard
          omega
        have habne : a ≠ b := by
          intro h
          subst b
          exact Finset.disjoint_left.mp hdisj a ha hb
        apply pathClosure_spec G habne
        have hbmono : G.degree b ≤ H.degree b :=
          degree_le_of_le (v := b) (self_le_pathClosure G)
        have hbG := hBdeg b hb
        rw [hn]
        omega
    have hBHigh : ∀ b ∈ B, h ≤ H.degree b := by
      intro b hb
      have hsub : A ⊆ H.neighborFinset b := by
        intro a ha
        simpa using (hAB a ha b hb).symm
      have hcard := Finset.card_le_card hsub
      rw [card_neighborFinset_eq_degree, hAcard] at hcard
      exact hcard
    have hHtop : H = (⊤ : SimpleGraph V) := by
      ext u v
      constructor
      · intro huv
        simpa using huv.ne
      · intro huv
        have hu : u ∈ A ∪ B := by rw [hpart]; simp
        have hv : v ∈ A ∪ B := by rw [hpart]; simp
        rw [Finset.mem_union] at hu hv
        rcases hu with huA | huB
        · rcases hv with hvA | hvB
          · exact hAclique u huA v hvA huv
          · exact hAB u huA v hvB
        · rcases hv with hvA | hvB
          · exact (hAB v hvA u huB).symm
          · apply pathClosure_spec G huv
            have huH := hBHigh u huB
            have hvH := hBHigh v hvB
            rw [hn]
            omega
    exact isTraceable_of_pathClosure_eq_top G hHtop
  · push_neg at hnew
    have hApBOriginal : ∀ a ∈ Ap, ∀ b ∈ B, G.Adj a b := by
      intro a ha b hb
      exact hnew a ha b hb
    have hApCardLe : Ap.card ≤ q := by
      obtain ⟨b, hb⟩ := hBne
      have hsub : Ap ⊆ G.neighborFinset b := by
        intro a ha
        simpa using (hApBOriginal a ha b hb).symm
      have hcard := Finset.card_le_card hsub
      rw [card_neighborFinset_eq_degree, hBdeg b hb] at hcard
      exact hcard
    have hOutsideAllA : ∀ x ∈ A \ Ap, G.neighborFinset x = A.erase x := by
      intro x hx
      have hxA := (Finset.mem_sdiff.mp hx).1
      have hxNotAp := (Finset.mem_sdiff.mp hx).2
      have hsub : G.neighborFinset x ⊆ A.erase x := by
        intro y hy
        have hxy : G.Adj x y := by simpa using hy
        have hyPart : y ∈ A ∪ B := by rw [hpart]; simp
        rw [Finset.mem_union] at hyPart
        have hyA : y ∈ A := by
          rcases hyPart with hyA | hyB
          · exact hyA
          · exfalso
            apply hxNotAp
            simp only [Ap, Finset.mem_filter]
            exact ⟨hxA, y, hyB, hxy⟩
        exact Finset.mem_erase.mpr ⟨hxy.ne, hyA⟩
      apply Finset.eq_of_subset_of_card_le hsub
      rw [card_neighborFinset_eq_degree, hAdeg x hxA,
        Finset.card_erase_of_mem hxA, hAcard]
    obtain ⟨a, haAp⟩ := hApNe
    have haA := hApSub haAp
    have hsub : (A \ Ap) ∪ B ⊆ G.neighborFinset a := by
      intro x hx
      rw [Finset.mem_union] at hx
      rcases hx with hxOut | hxB
      · have hxData := Finset.mem_sdiff.mp hxOut
        have hxeq := hOutsideAllA x hxOut
        have hax : a ∈ A.erase x := by
          exact Finset.mem_erase.mpr ⟨by
            intro h
            subst x
            exact hxData.2 haAp, haA⟩
        have hxa : G.Adj x a := by
          have : a ∈ G.neighborFinset x := by simpa [hxeq] using hax
          simpa using this
        simpa using hxa.symm
      · simpa using hApBOriginal a haAp x hxB
    have hdisjOut : Disjoint (A \ Ap) B :=
      hdisj.mono Finset.sdiff_subset (by rfl)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisjOut,
      Finset.card_sdiff hApSub, hAcard, hBcard,
      card_neighborFinset_eq_degree, hAdeg a haA] at hcard
    omega

#print axioms SimpleGraph.C217TwoBlockClosure.isTraceable_twoBlock

end SimpleGraph.C217TwoBlockClosure
