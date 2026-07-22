/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217CrossDegree
import Lean.Elab.Tactic.Omega

/-!
# Quantitative seed completion for WOWII Conjecture 217

A universal high-degree set need not be large enough for one seed to finish the
path closure. The correct invariant is the total number of outside seeds. This
module proves both the multi-seed cascade and the cross-incidence estimate that
forces enough seeds.
-/

namespace SimpleGraph.C217MultiSeed

open Classical
open SimpleGraph
open SimpleGraph.C217ClosureHelpers
open SimpleGraph.C217CrossDegree

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]

/-- Outside vertices whose path-closure degree has risen above the base value
`r`. -/
def seedSet (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (r : ℕ) : Finset V :=
  (Finset.univ \ A).filter fun v => r + 1 ≤ (pathClosure G).degree v

lemma seedSet_subset_compl
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (r : ℕ) :
    seedSet G A r ⊆ Finset.univ \ A := by
  intro v hv
  exact (Finset.mem_filter.mp (by simpa [seedSet] using hv)).1

lemma mem_seedSet_iff
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (r : ℕ) (v : V) :
    v ∈ seedSet G A r ↔ v ∉ A ∧ r + 1 ≤ (pathClosure G).degree v := by
  simp [seedSet]

/-- A universal set together with enough outside seeds makes every outside
vertex have degree at least `r+1`, and hence makes the path closure complete. -/
theorem pathClosure_eq_top_of_many_seeds
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A S : Finset V) (r : ℕ)
    (hn : Fintype.card V = 2 * r + 2)
    (hSsub : S ⊆ Finset.univ \ A)
    (huniv : ∀ a ∈ A, ∀ v, v ≠ a → (pathClosure G).Adj a v)
    (hout : ∀ v ∉ A, r ≤ (pathClosure G).degree v)
    (hSdeg : ∀ s ∈ S, r + 1 ≤ (pathClosure G).degree s)
    (hcount : r + 1 ≤ A.card + S.card) :
    pathClosure G = (⊤ : SimpleGraph V) := by
  let H := pathClosure G
  have hASdisj : Disjoint A S := by
    rw [Finset.disjoint_left]
    intro x hxA hxS
    have hxComp := hSsub hxS
    exact (Finset.mem_sdiff.mp hxComp).2 hxA
  have houtStrong : ∀ v ∉ A, r + 1 ≤ H.degree v := by
    intro v hvA
    by_cases hvS : v ∈ S
    · simpa [H] using hSdeg v hvS
    · have hSadj : ∀ s ∈ S, H.Adj s v := by
        intro s hs
        have hsv : s ≠ v := by
          intro h
          subst s
          exact hvS hs
        apply pathClosure_spec G hsv
        have hsdeg := hSdeg s hs
        have hvdeg := hout v hvA
        simpa [H, hn] using (show 2 * r + 1 ≤ H.degree s + H.degree v by omega)
      have hsub : A ∪ S ⊆ H.neighborFinset v := by
        intro x hx
        rw [Finset.mem_union] at hx
        rcases hx with hxA | hxS
        · have hxv : x ≠ v := by
            intro h
            subst x
            exact hvA hxA
          simpa [H] using (huniv x hxA v hxv).symm
        · simpa [H] using (hSadj x hxS).symm
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hASdisj,
        card_neighborFinset_eq_degree] at hcard
      exact hcount.trans hcard
  ext u v
  constructor
  · intro huv
    simpa using huv.ne
  · intro huv
    by_cases huA : u ∈ A
    · exact huniv u huA v huv
    · by_cases hvA : v ∈ A
      · exact (huniv v hvA u huv.symm).symm
      · apply pathClosure_spec G huv
        have hu := houtStrong u huA
        have hv := houtStrong v hvA
        simpa [H, hn] using (show 2 * r + 1 ≤ H.degree u + H.degree v by omega)

/-- The cross-incidence capacity of `A` forces a lower bound on the number of
outside seeds. -/
theorem seedSet_card_ge
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (r m : ℕ)
    (huniv : ∀ a ∈ A, ∀ v, v ≠ a → (pathClosure G).Adj a v)
    (hBdeg : ∀ v ∉ A, G.degree v = r)
    (hm : m ≤ (Finset.univ \ A).card)
    (hcapacity : (∑ a ∈ A, G.degree a) <
      A.card * ((Finset.univ \ A).card - (m - 1))) :
    m ≤ (seedSet G A r).card := by
  let B : Finset V := Finset.univ \ A
  let S : Finset V := seedSet G A r
  by_contra hnot
  have hSlt : S.card < m := by
    exact Nat.lt_of_not_ge hnot
  have hSsub : S ⊆ B := by
    simpa [S, B] using seedSet_subset_compl G A r
  let N : Finset V := B \ S
  have hNcard : N.card = B.card - S.card := by
    simp [N, Finset.card_sdiff hSsub]
  have hNcross : ∀ v ∈ N, crossDegree G A v = A.card := by
    intro v hvN
    have hvData := Finset.mem_sdiff.mp (by simpa [N] using hvN)
    have hvB : v ∈ B := hvData.1
    have hvS : v ∉ S := hvData.2
    have hvA : v ∉ A := by simpa [B] using hvB
    have hall : ∀ a ∈ A, G.Adj v a := by
      intro a ha
      have hav : a ≠ v := by
        intro h
        subst a
        exact hvA ha
      have hHadj : (pathClosure G).Adj v a := (huniv a ha v hav).symm
      by_contra hGadj
      have hlt : G.degree v < (pathClosure G).degree v :=
        degree_lt_of_le_of_adj_of_not_adj (self_le_pathClosure G) hHadj hGadj
      have hvdeg := hBdeg v hvA
      have hvSeed : v ∈ S := by
        rw [S, mem_seedSet_iff]
        exact ⟨hvA, by omega⟩
      exact hvS hvSeed
    unfold crossDegree
    calc
      (∑ a ∈ A, if G.Adj v a then 1 else 0) = ∑ a ∈ A, 1 := by
        apply Finset.sum_congr rfl
        intro a ha
        simp [hall a ha]
      _ = A.card := by simp
  have hsumN : (∑ v ∈ N, crossDegree G A v) = A.card * N.card := by
    calc
      (∑ v ∈ N, crossDegree G A v) = ∑ v ∈ N, A.card := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [hNcross v hv]
      _ = A.card * N.card := by simp [mul_comm]
  have hNsubB : N ⊆ B := Finset.sdiff_subset
  have hsumNB : (∑ v ∈ N, crossDegree G A v) ≤
      ∑ v ∈ B, crossDegree G A v := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hNsubB
      (fun v hvB hvN => Nat.zero_le _)
  have hcross : (∑ v ∈ B, crossDegree G A v) =
      ∑ a ∈ A, crossDegree G B a := by
    simpa [B] using sum_crossDegree_compl G A
  have hcrossLe : (∑ v ∈ B, crossDegree G A v) ≤
      ∑ a ∈ A, G.degree a := by
    rw [hcross]
    exact Finset.sum_le_sum fun a ha => crossDegree_le_degree G B a
  have hSle : S.card ≤ m - 1 := by omega
  have hBminus : B.card - (m - 1) ≤ N.card := by
    rw [hNcard]
    omega
  have hmul : A.card * (B.card - (m - 1)) ≤ A.card * N.card :=
    Nat.mul_le_mul_left A.card hBminus
  have hcapLe : A.card * (B.card - (m - 1)) ≤
      ∑ a ∈ A, G.degree a := by
    calc
      A.card * (B.card - (m - 1)) ≤ A.card * N.card := hmul
      _ = ∑ v ∈ N, crossDegree G A v := hsumN.symm
      _ ≤ ∑ v ∈ B, crossDegree G A v := hsumNB
      _ ≤ ∑ a ∈ A, G.degree a := hcrossLe
  simpa [B] using (Nat.not_lt_of_ge hcapLe hcapacity)

/-- Quantitative end-to-end criterion: cross-incidence capacity forces enough
seeds, and enough seeds complete the path closure. -/
theorem isTraceable_of_seed_capacity
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (r m : ℕ)
    (hn : Fintype.card V = 2 * r + 2)
    (huniv : ∀ a ∈ A, ∀ v, v ≠ a → (pathClosure G).Adj a v)
    (hBdeg : ∀ v ∉ A, G.degree v = r)
    (hm : m ≤ (Finset.univ \ A).card)
    (hcount : r + 1 ≤ A.card + m)
    (hcapacity : (∑ a ∈ A, G.degree a) <
      A.card * ((Finset.univ \ A).card - (m - 1))) :
    IsTraceable G := by
  let S := seedSet G A r
  have hScard : m ≤ S.card := by
    exact seedSet_card_ge G A r m huniv hBdeg hm hcapacity
  have hSsub : S ⊆ Finset.univ \ A := by
    simpa [S] using seedSet_subset_compl G A r
  have hSdeg : ∀ s ∈ S, r + 1 ≤ (pathClosure G).degree s := by
    intro s hs
    exact (mem_seedSet_iff G A r s).mp (by simpa [S] using hs) |>.2
  have hout : ∀ v ∉ A, r ≤ (pathClosure G).degree v := by
    intro v hvA
    have hmono : G.degree v ≤ (pathClosure G).degree v :=
      degree_le_of_le (v := v) (self_le_pathClosure G)
    rw [hBdeg v hvA] at hmono
    exact hmono
  apply isTraceable_of_pathClosure_eq_top G
  apply pathClosure_eq_top_of_many_seeds G A S r hn hSsub huniv hout hSdeg
  exact hcount.trans (Nat.add_le_add_left hScard A.card)

#print axioms SimpleGraph.C217MultiSeed.pathClosure_eq_top_of_many_seeds
#print axioms SimpleGraph.C217MultiSeed.seedSet_card_ge
#print axioms SimpleGraph.C217MultiSeed.isTraceable_of_seed_capacity

end SimpleGraph.C217MultiSeed
