/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.PathClosure
import Mathlib.Data.Finset.Max
import Lean.Elab.Tactic.Omega

/-!
# Chvátal's degree condition for Hamiltonian paths

The condition is stated by counting vertices below each degree threshold. This
is equivalent to the usual sorted-degree formulation and interacts directly
with the finite C217 certificate.
-/

namespace SimpleGraph

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]

/-- Vertices of degree strictly below `k`. -/
def lowDegreeFinset (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : Finset V :=
  Finset.univ.filter fun v => G.degree v < k

/-- Vertices other than `v` that are not adjacent to `v`. -/
def nonneighborFinset (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  Finset.univ.filter fun w => w ≠ v ∧ ¬G.Adj v w

@[simp] lemma mem_nonneighborFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (v w : V) :
    w ∈ nonneighborFinset G v ↔ w ≠ v ∧ ¬G.Adj v w := by
  simp [nonneighborFinset]

lemma nonneighborFinset_eq_compl_neighborFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    nonneighborFinset G v = Gᶜ.neighborFinset v := by
  ext w
  simp [nonneighborFinset, and_comm]

lemma card_nonneighborFinset (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (nonneighborFinset G v).card = Fintype.card V - 1 - G.degree v := by
  rw [nonneighborFinset_eq_compl_neighborFinset, card_neighborFinset_eq_degree,
    degree_compl]

/-- Count-form Chvátal condition for a Hamiltonian path. -/
def ChvatalPathCondition (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ i : ℕ, 1 ≤ i → 2 * i < Fintype.card V + 1 →
    (lowDegreeFinset G i).card < i ∨
      (lowDegreeFinset G (Fintype.card V - i)).card ≤ Fintype.card V - i

lemma lowDegreeFinset_mono_graph {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj] (hGH : G ≤ H) (k : ℕ) :
    lowDegreeFinset H k ⊆ lowDegreeFinset G k := by
  intro v hv
  simp only [lowDegreeFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  exact (degree_le_of_le hGH).trans_lt hv

/-- Chvátal's count condition is preserved when edges are added. -/
theorem ChvatalPathCondition.mono {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hG : ChvatalPathCondition G) (hGH : G ≤ H) :
    ChvatalPathCondition H := by
  intro i hi hmid
  rcases hG i hi hmid with hlow | hhigh
  · left
    exact (Finset.card_le_card (lowDegreeFinset_mono_graph hGH i)).trans_lt hlow
  · right
    exact (Finset.card_le_card
      (lowDegreeFinset_mono_graph hGH (Fintype.card V - i))).trans hhigh

/-- The complete graph on a nontrivial finite vertex type has a Hamiltonian path. -/
theorem top_isTraceable : IsTraceable (⊤ : SimpleGraph V) := by
  let K : SimpleGraph V := ⊤
  obtain ⟨a, b, p, hp, hmax⟩ := Walk.exists_isPath_forall_isPath_length_le_length K
  refine ⟨a, b, p, hp.isHamiltonian_of_mem ?_⟩
  intro x
  by_contra hx
  have hxb : b ≠ x := by
    intro h
    subst x
    exact hx (by simp)
  have hbx : K.Adj b x := by simp [K, hxb]
  have hnew : (p.concat hbx).IsPath := hp.concat hx hbx
  have hle := hmax a x (p.concat hbx) hnew
  simp at hle

private lemma exists_nonneighbor_of_ne_top (G : SimpleGraph V) (hG : G ≠ ⊤) :
    ∃ u v : V, u ≠ v ∧ ¬G.Adj u v := by
  by_contra h
  push_neg at h
  apply hG
  ext u v
  constructor
  · intro huv
    exact h u v huv.ne
  · intro huv
    simpa using huv.ne

private lemma exists_max_degree_mem (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) (hs : s.Nonempty) :
    ∃ v ∈ s, ∀ x ∈ s, G.degree x ≤ G.degree v := by
  have hmem : s.sup G.degree ∈ G.degree '' (s : Set V) :=
    Finset.sup_mem_of_nonempty hs
  obtain ⟨v, hv, hvdeg⟩ := hmem
  refine ⟨v, hv, ?_⟩
  intro x hx
  rw [← hvdeg]
  exact Finset.le_sup hx

/-- Chvátal's degree condition implies traceability. -/
theorem isTraceable_of_chvatalPathCondition
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ChvatalPathCondition G) :
    IsTraceable G := by
  let H := pathClosure G
  have hHcond : ChvatalPathCondition H :=
    hG.mono (self_le_pathClosure G)
  have hHtop : H = ⊤ := by
    by_contra hne
    obtain ⟨u₀, v₀, huv₀, hnadj₀⟩ := exists_nonneighbor_of_ne_top H hne
    let active : Finset V :=
      Finset.univ.filter fun v => (nonneighborFinset H v).Nonempty
    have hactive : active.Nonempty := by
      refine ⟨u₀, ?_⟩
      simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨v₀, by simp [huv₀.symm, hnadj₀]⟩
    obtain ⟨v, hvactive, hvmax⟩ := exists_max_degree_mem H active hactive
    have hBv : (nonneighborFinset H v).Nonempty := by
      simpa [active] using hvactive
    obtain ⟨u, huBv, humax⟩ :=
      exists_max_degree_mem H (nonneighborFinset H v) hBv
    have huv : u ≠ v := (mem_nonneighborFinset H v u).mp huBv |>.1
    have hnadjVU : ¬H.Adj v u :=
      (mem_nonneighborFinset H v u).mp huBv |>.2
    have hnadj : ¬H.Adj u v := fun huvAdj => hnadjVU huvAdj.symm
    have huactive : u ∈ active := by
      simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨v, ?_⟩
      simp [huv, hnadj]
    have hduv : H.degree u ≤ H.degree v := hvmax u huactive
    have hsum : H.degree u + H.degree v < Fintype.card V - 1 := by
      by_contra hnot
      have hge : Fintype.card V - 1 ≤ H.degree u + H.degree v := by omega
      exact hnadj (by
        simpa [H] using pathClosure_spec G huv hge)
    let i := H.degree u + 1
    have hi : 1 ≤ i := by simp [i]
    have hmid : 2 * i < Fintype.card V + 1 := by
      have hdu := H.degree_lt_card_verts u
      have hdv := H.degree_lt_card_verts v
      dsimp [i]
      omega
    rcases hHcond i hi hmid with hfirst | hsecond
    · have hsub : nonneighborFinset H v ⊆ lowDegreeFinset H i := by
        intro x hx
        have hxle : H.degree x ≤ H.degree u := humax x hx
        simp only [lowDegreeFinset, Finset.mem_filter, Finset.mem_univ, true_and]
        dsimp [i]
        omega
      have hcard := Finset.card_le_card hsub
      have hBcard := card_nonneighborFinset H v
      have hdu := H.degree_lt_card_verts u
      have hdv := H.degree_lt_card_verts v
      omega
    · have hsub : insert u (nonneighborFinset H u) ⊆
          lowDegreeFinset H (Fintype.card V - i) := by
        intro x hx
        rw [Finset.mem_insert] at hx
        simp only [lowDegreeFinset, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hx with rfl | hx
        · dsimp [i]
          omega
        · have hxactive : x ∈ active := by
            simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨u, ?_⟩
            have hxu := (mem_nonneighborFinset H u x).mp hx
            simp [hxu.1.symm, hxu.2]
          have hxle : H.degree x ≤ H.degree v := hvmax x hxactive
          dsimp [i]
          omega
      have hcard := Finset.card_le_card hsub
      have hunot : u ∉ nonneighborFinset H u := by simp
      rw [Finset.card_insert_of_notMem hunot, card_nonneighborFinset] at hcard
      have hdu := H.degree_lt_card_verts u
      have hdv := H.degree_lt_card_verts v
      omega
  have htraceH : IsTraceable H := by
    rw [hHtop]
    exact top_isTraceable
  exact (pathClosure_traceable_iff G).mp htraceH

#print axioms SimpleGraph.isTraceable_of_chvatalPathCondition

end SimpleGraph
