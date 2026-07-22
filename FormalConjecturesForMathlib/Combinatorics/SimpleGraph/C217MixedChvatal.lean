/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217CrossDegree
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217UniversalStages
import Mathlib.Tactic.IntervalCases

/-!
# Mixed high-degree rows via Chvátal after path closure

The four order-twelve rows with degree classes six, five, and four do not need
complete path closure. Cross-incidence capacity forces enough vertices of
closure degree at least six; the resulting closure satisfies Chvátal's path
condition directly.
-/

namespace SimpleGraph.C217MixedChvatal

open Classical
open SimpleGraph
open SimpleGraph.C217ClosureHelpers
open SimpleGraph.C217CrossDegree
open SimpleGraph.C217UniversalStages

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]

/-- Outside vertices whose closure degree is at least six. -/
def sixSeedSet (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) : Finset V :=
  (Finset.univ \ A).filter fun v => 6 ≤ (pathClosure G).degree v

lemma sixSeedSet_subset
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) :
    sixSeedSet G A ⊆ Finset.univ \ A := by
  intro v hv
  exact (Finset.mem_filter.mp (by simpa [sixSeedSet] using hv)).1

/-- A closure-nonseed of original degree five has all universal-set edges
already present in the original graph. -/
lemma crossDegree_eq_card_of_degree_five_nonseed
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) {v : V}
    (hvA : v ∉ A) (hvdeg : G.degree v = 5)
    (huniv : ∀ a ∈ A, ∀ w, w ≠ a → (pathClosure G).Adj a w)
    (hvnon : v ∉ sixSeedSet G A) :
    crossDegree G A v = A.card := by
  have hall : ∀ a ∈ A, G.Adj v a := by
    intro a ha
    have hav : a ≠ v := by
      intro h
      subst a
      exact hvA ha
    have hHadj := (huniv a ha v hav).symm
    by_contra hGadj
    have hlt := degree_lt_of_le_of_adj_of_not_adj
      (self_le_pathClosure G) hHadj hGadj
    have hvSeed : v ∈ sixSeedSet G A := by
      simp only [sixSeedSet, Finset.mem_filter, Finset.mem_sdiff,
        Finset.mem_univ, true_and]
      exact ⟨hvA, by omega⟩
    exact hvnon hvSeed
  unfold crossDegree
  calc
    (∑ a ∈ A, if G.Adj v a then 1 else 0) = ∑ _a ∈ A, 1 := by
      apply Finset.sum_congr rfl
      intro a ha
      simp [hall a ha]
    _ = A.card := by simp

/-- A closure-nonseed of original degree four is missing at most one edge to
the universal set, hence contributes at least `A.card - 1` cross incidences. -/
lemma card_sub_one_le_crossDegree_of_degree_four_nonseed
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) {v : V}
    (hvA : v ∉ A) (hvdeg : G.degree v = 4)
    (huniv : ∀ a ∈ A, ∀ w, w ≠ a → (pathClosure G).Adj a w)
    (hvnon : v ∉ sixSeedSet G A) :
    A.card - 1 ≤ crossDegree G A v := by
  let H := pathClosure G
  let M : Finset V := A.filter fun a => ¬G.Adj v a
  let P : Finset V := A.filter fun a => G.Adj v a
  have hHle : H.degree v ≤ 5 := by
    have hnot : ¬6 ≤ H.degree v := by
      intro h6
      apply hvnon
      simp [sixSeedSet, hvA, H, h6]
    omega
  have hdisj : Disjoint (G.neighborFinset v) M := by
    rw [Finset.disjoint_left]
    intro x hxG hxM
    have hAdj : G.Adj v x := by simpa using hxG
    exact (Finset.mem_filter.mp (by simpa [M] using hxM)).2 hAdj
  have hsub : G.neighborFinset v ∪ M ⊆ H.neighborFinset v := by
    intro x hx
    rw [Finset.mem_union] at hx
    rcases hx with hxG | hxM
    · have hAdjG : G.Adj v x := by simpa using hxG
      have hAdjH : H.Adj v x := (self_le_pathClosure G) hAdjG
      simpa [H] using hAdjH
    · have hxData := Finset.mem_filter.mp (by simpa [M] using hxM)
      have hxA := hxData.1
      have hxv : x ≠ v := by
        intro h
        subst x
        exact G.irrefl (show G.Adj v v from False.elim (hxData.2 (G.irrefl)))
      have hAdjH : H.Adj v x := (huniv x hxA v hxv).symm
      simpa [H] using hAdjH
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj,
    card_neighborFinset_eq_degree, hvdeg,
    card_neighborFinset_eq_degree] at hcard
  have hMle : M.card ≤ 1 := by omega
  have hpartition : P ∪ M = A := by
    ext x
    simp [P, M]
  have hPMdisj : Disjoint P M := by
    rw [Finset.disjoint_left]
    intro x hxP hxM
    have hp := (Finset.mem_filter.mp (by simpa [P] using hxP)).2
    have hm := (Finset.mem_filter.mp (by simpa [M] using hxM)).2
    exact hm hp
  have hcardA : A.card = P.card + M.card := by
    rw [← hpartition, Finset.card_union_of_disjoint hPMdisj]
  have hcross : crossDegree G A v = P.card := by
    rw [crossDegree_eq_card_filter]
    congr
  rw [hcross]
  omega

/-- Abstract seed-count theorem for the mixed classes. The concrete row only
needs to verify the final arithmetic lower bound `hforce`. -/
theorem sixSeedSet_card_ge
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C D : Finset V) (m : ℕ)
    (hCD : C ∪ D = Finset.univ \ A)
    (hCDisjD : Disjoint C D)
    (hCdeg : ∀ c ∈ C, G.degree c = 5)
    (hDdeg : ∀ d ∈ D, G.degree d = 4)
    (huniv : ∀ a ∈ A, ∀ v, v ≠ a → (pathClosure G).Adj a v)
    (hforce : ∀ sC sD : ℕ,
      sC ≤ C.card → sD ≤ D.card → sC + sD < m →
      (∑ a ∈ A, G.degree a) <
        A.card * (C.card - sC) + (A.card - 1) * (D.card - sD)) :
    m ≤ (sixSeedSet G A).card := by
  let S := sixSeedSet G A
  let SC := C ∩ S
  let SD := D ∩ S
  by_contra hnot
  have hSsub : S ⊆ C ∪ D := by
    intro v hv
    have hvComp := sixSeedSet_subset G A hv
    rw [← hCD] at hvComp
    exact hvComp
  have hSsplit : S = SC ∪ SD := by
    ext v
    constructor
    · intro hv
      have hvCD := hSsub hv
      rw [Finset.mem_union] at hvCD ⊢
      rcases hvCD with hvC | hvD
      · left; exact Finset.mem_inter.mpr ⟨hvC, hv⟩
      · right; exact Finset.mem_inter.mpr ⟨hvD, hv⟩
    · intro hv
      rw [Finset.mem_union] at hv
      rcases hv with hvSC | hvSD
      · exact (Finset.mem_inter.mp hvSC).2
      · exact (Finset.mem_inter.mp hvSD).2
  have hSCSD : Disjoint SC SD :=
    hCDisjD.mono Finset.inter_subset_left Finset.inter_subset_left
  have hScard : S.card = SC.card + SD.card := by
    rw [hSsplit, Finset.card_union_of_disjoint hSCSD]
  have hseedSmall : SC.card + SD.card < m := by
    rw [← hScard]
    exact Nat.lt_of_not_ge hnot
  let NC := C \ S
  let ND := D \ S
  have hNCcross : ∀ c ∈ NC, crossDegree G A c = A.card := by
    intro c hc
    have hcData := Finset.mem_sdiff.mp (by simpa [NC] using hc)
    have hcA : c ∉ A := by
      have hcComp : c ∈ Finset.univ \ A := by
        rw [← hCD]
        exact Finset.mem_union.mpr (Or.inl hcData.1)
      exact (Finset.mem_sdiff.mp hcComp).2
    exact crossDegree_eq_card_of_degree_five_nonseed G A hcA
      (hCdeg c hcData.1) huniv hcData.2
  have hNDcross : ∀ d ∈ ND, A.card - 1 ≤ crossDegree G A d := by
    intro d hd
    have hdData := Finset.mem_sdiff.mp (by simpa [ND] using hd)
    have hdA : d ∉ A := by
      have hdComp : d ∈ Finset.univ \ A := by
        rw [← hCD]
        exact Finset.mem_union.mpr (Or.inr hdData.1)
      exact (Finset.mem_sdiff.mp hdComp).2
    exact card_sub_one_le_crossDegree_of_degree_four_nonseed G A hdA
      (hDdeg d hdData.1) huniv hdData.2
  have hNCcard : NC.card = C.card - SC.card := by
    have hInter : C ∩ S = SC := rfl
    rw [NC, Finset.card_sdiff]
    · rw [← hInter]
      exact Finset.card_inter_of_subset (by rfl)
    · exact Finset.inter_subset_left
  have hNDcard : ND.card = D.card - SD.card := by
    have hInter : D ∩ S = SD := rfl
    rw [ND, Finset.card_sdiff]
    · rw [← hInter]
      exact Finset.card_inter_of_subset (by rfl)
    · exact Finset.inter_subset_left
  have hsumNC : (∑ c ∈ NC, crossDegree G A c) = A.card * NC.card := by
    calc
      (∑ c ∈ NC, crossDegree G A c) = ∑ _c ∈ NC, A.card := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [hNCcross c hc]
      _ = A.card * NC.card := by simp [mul_comm]
  have hsumND : (A.card - 1) * ND.card ≤
      ∑ d ∈ ND, crossDegree G A d := by
    calc
      (A.card - 1) * ND.card = ∑ _d ∈ ND, (A.card - 1) := by simp [mul_comm]
      _ ≤ ∑ d ∈ ND, crossDegree G A d :=
        Finset.sum_le_sum fun d hd => hNDcross d hd
  have hNCNDdisj : Disjoint NC ND :=
    hCDisjD.mono Finset.sdiff_subset Finset.sdiff_subset
  have hNCNDsub : NC ∪ ND ⊆ Finset.univ \ A := by
    intro v hv
    rw [Finset.mem_union] at hv
    rw [← hCD]
    rcases hv with hvNC | hvND
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mp (by simpa [NC] using hvNC)).1)
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mp (by simpa [ND] using hvND)).1)
  have hsumSub : (∑ v ∈ NC ∪ ND, crossDegree G A v) ≤
      ∑ v ∈ Finset.univ \ A, crossDegree G A v := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hNCNDsub
      (fun v hvB hvN => Nat.zero_le _)
  have hcrossLe : (∑ v ∈ Finset.univ \ A, crossDegree G A v) ≤
      ∑ a ∈ A, G.degree a := by
    rw [sum_crossDegree_compl G A]
    exact Finset.sum_le_sum fun a ha =>
      crossDegree_le_degree G (Finset.univ \ A) a
  have hlower : A.card * NC.card + (A.card - 1) * ND.card ≤
      ∑ v ∈ NC ∪ ND, crossDegree G A v := by
    rw [Finset.sum_union hNCNDdisj, hsumNC]
    exact Nat.add_le_add_left hsumND _
  have hforceNow := hforce SC.card SD.card
    (Finset.card_inter_le_left) (Finset.card_inter_le_left) hseedSmall
  rw [hNCcard, hNDcard] at hlower
  have hcap : A.card * (C.card - SC.card) +
      (A.card - 1) * (D.card - SD.card) ≤
      ∑ a ∈ A, G.degree a :=
    hlower.trans (hsumSub.trans hcrossLe)
  omega

/-- Enough six-seeds imply the closure satisfies Chvátal. -/
theorem isTraceable_of_mixed_sixSeeds
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C D : Finset V) (m : ℕ)
    (hn : Fintype.card V = 12)
    (hCD : C ∪ D = Finset.univ \ A)
    (hCDisjD : Disjoint C D)
    (hAuniv : ∀ a ∈ A, ∀ v, v ≠ a → (pathClosure G).Adj a v)
    (hCbase : ∀ c ∈ C, 5 ≤ (pathClosure G).degree c)
    (hDbase : ∀ d ∈ D, 4 ≤ (pathClosure G).degree d)
    (hDsmall : D.card < 5)
    (hSeeds : m ≤ (sixSeedSet G A).card)
    (hOutside : (Finset.univ \ A).card - m ≤ 6) :
    IsTraceable G := by
  let H := pathClosure G
  have hmin4 : ∀ v, 4 ≤ H.degree v := by
    intro v
    by_cases hvA : v ∈ A
    · have hsub : A.erase v ⊆ H.neighborFinset v := by
        intro x hx
        have hxe := Finset.mem_erase.mp hx
        simpa [H] using hAuniv v hvA x hxe.1.symm
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hvA, card_neighborFinset_eq_degree] at hcard
      omega
    · have hvCD : v ∈ C ∪ D := by
        rw [hCD]
        simp [hvA]
      rw [Finset.mem_union] at hvCD
      rcases hvCD with hvC | hvD
      · exact (hCbase v hvC).trans' (by omega)
      · exact hDbase v hvD
  have hcond : ChvatalPathCondition H := by
    intro i hi hmid
    rw [hn] at hmid
    interval_cases i
    all_goals try {omega}
    · left
      have hempty : lowDegreeFinset H 1 = ∅ := by
        ext v
        simp [lowDegreeFinset]
      simp [hempty]
    · left
      have hempty : lowDegreeFinset H 2 = ∅ := by
        ext v
        simp [lowDegreeFinset]
        have := hmin4 v
        omega
      simp [hempty]
    · left
      have hempty : lowDegreeFinset H 3 = ∅ := by
        ext v
        simp [lowDegreeFinset]
        have := hmin4 v
        omega
      simp [hempty]
    · left
      have hempty : lowDegreeFinset H 4 = ∅ := by
        ext v
        simp [lowDegreeFinset]
        have := hmin4 v
        omega
      simp [hempty]
    · left
      have hsub : lowDegreeFinset H 5 ⊆ D := by
        intro v hv
        have hvlt : H.degree v < 5 := by simpa [lowDegreeFinset] using hv
        have hvA : v ∉ A := by
          intro hvA
          have hdeg : A.card - 1 ≤ H.degree v := by
            have hsubA : A.erase v ⊆ H.neighborFinset v := by
              intro x hx
              have hxe := Finset.mem_erase.mp hx
              simpa [H] using hAuniv v hvA x hxe.1.symm
            have hc := Finset.card_le_card hsubA
            rw [Finset.card_erase_of_mem hvA, card_neighborFinset_eq_degree] at hc
            exact hc
          omega
        have hvCD : v ∈ C ∪ D := by
          rw [hCD]
          simp [hvA]
        rw [Finset.mem_union] at hvCD
        exact hvCD.resolve_left (fun hvC => by
          have := hCbase v hvC
          omega)
      exact (Finset.card_le_card hsub).trans_lt hDsmall
    · right
      have hsub : lowDegreeFinset H 6 ⊆
          (Finset.univ \ A) \ sixSeedSet G A := by
        intro v hv
        have hvlt : H.degree v < 6 := by simpa [lowDegreeFinset] using hv
        have hvA : v ∉ A := by
          intro hvA
          have hdeg : A.card - 1 ≤ H.degree v := by
            have hsubA : A.erase v ⊆ H.neighborFinset v := by
              intro x hx
              have hxe := Finset.mem_erase.mp hx
              simpa [H] using hAuniv v hvA x hxe.1.symm
            have hc := Finset.card_le_card hsubA
            rw [Finset.card_erase_of_mem hvA, card_neighborFinset_eq_degree] at hc
            exact hc
          omega
        refine Finset.mem_sdiff.mpr ⟨by simp [hvA], ?_⟩
        intro hvSeed
        have h6 := (Finset.mem_filter.mp (by simpa [sixSeedSet] using hvSeed)).2
        omega
      have hseedSub := sixSeedSet_subset G A
      have hcardComp : ((Finset.univ \ A) \ sixSeedSet G A).card =
          (Finset.univ \ A).card - (sixSeedSet G A).card := by
        rw [Finset.card_sdiff hseedSub]
      have hc := Finset.card_le_card hsub
      rw [hcardComp]
      rw [hn]
      omega
  have hTraceH := isTraceable_of_chvatalPathCondition H hcond
  exact (pathClosure_traceable_iff G).mp hTraceH

#print axioms SimpleGraph.C217MixedChvatal.sixSeedSet_card_ge
#print axioms SimpleGraph.C217MixedChvatal.isTraceable_of_mixed_sixSeeds

end SimpleGraph.C217MixedChvatal
