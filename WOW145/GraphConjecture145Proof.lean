/-
Copyright 2026 Dominic Dabish.
Licensed under the Apache License, Version 2.0.
-/

import WOW146.ExceptionalTheorem
import FormalConjectures.WrittenOnTheWallII.GraphConjecture145

/-!
# WOWII Conjecture 145

This module proves the exact Formal Conjectures statement. The only exceptional
six-vertex induced-tree construction is reused, with attribution, from the
Apache-licensed and separately kernel-verified WOWII 146 formalization at
`akakabrian/WOW-146`. The reduction from the complement local-independence
invariant in Conjecture 145 is new here.
-/

open Classical
open SimpleGraph
open WrittenOnTheWallII.GraphConjecture145
open WrittenOnTheWallII.GraphConjecture146

namespace WOW145

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
variable {G : SimpleGraph α}

/-- If one complement-neighborhood has independence number one, its center is
at distance at most two from every vertex of the original graph. -/
lemma dist_le_two_of_comp_indepNeighborsCard_eq_one
    [DecidableRel G.Adj] (hG : G.Connected) {v : α}
    (hv : indepNeighborsCard Gᶜ v = 1) (w : α) :
    G.dist v w ≤ 2 := by
  by_cases hvw : v = w
  · subst w
    simp
  by_cases hadj : G.Adj v w
  · rw [dist_eq_one_iff_adj.mpr hadj]
    omega
  obtain ⟨p, -, hpLen⟩ := hG.exists_path_of_dist v w
  have hpPos : 0 < p.length := by
    rw [hpLen]
    exact hG.pos_dist_of_ne hvw
  have hpNotNil : ¬p.Nil := Walk.not_nil_iff_lt_length.mpr hpPos
  let z : α := p.penultimate
  have hzw : G.Adj z w := by
    simpa [z] using p.adj_penultimate hpNotNil
  by_cases hvz : G.Adj v z
  · exact WOW146.dist_le_two_of_adj_adj G hvz hzw
  have hvzNe : v ≠ z := by
    intro h
    exact hadj (h ▸ hzw)
  have hvwN : w ∈ Gᶜ.neighborSet v := by
    simp only [mem_neighborSet, compl_adj]
    exact ⟨hvw, hadj⟩
  have hvzN : z ∈ Gᶜ.neighborSet v := by
    simp only [mem_neighborSet, compl_adj]
    exact ⟨hvzNe, hvz⟩
  let z' : Gᶜ.neighborSet v := ⟨z, hvzN⟩
  let w' : Gᶜ.neighborSet v := ⟨w, hvwN⟩
  have hzwNe : z' ≠ w' := by
    intro h
    have hval : z = w := congrArg Subtype.val h
    exact hzw.ne hval
  have hpair :
      ((Gᶜ).induce (Gᶜ.neighborSet v)).IsIndepSet
        ({z', w'} : Finset (Gᶜ.neighborSet v)) := by
    rw [← isClique_compl]
    have hclique :
        (((Gᶜ).induce (Gᶜ.neighborSet v))ᶜ).IsClique
          ({z', w'} : Set (Gᶜ.neighborSet v)) := by
      rw [isClique_pair]
      intro _
      rw [compl_adj]
      refine ⟨hzwNe, ?_⟩
      change ¬Gᶜ.Adj z w
      intro hcomp
      exact (compl_adj.mp hcomp).2 hzw
    simpa using hclique
  have hcard : ({z', w'} : Finset (Gᶜ.neighborSet v)).card = 2 := by
    simp [hzwNe]
  have htwo := hpair.card_le_indepNum
  rw [hcard] at htwo
  unfold indepNeighborsCard at hv
  omega

/-- If the complement local-independence minimum is one, then the square graph
has radius one. -/
lemma graphSquareRadius_eq_one_of_localIndependenceMin_compl_eq_one
    [DecidableRel G.Adj] (hG : G.Connected)
    (hq : localIndependenceMin Gᶜ = 1) :
    graphSquareRadius G = 1 := by
  obtain ⟨v, -, hv⟩ := Finset.exists_mem_eq_inf'
    (Finset.univ_nonempty : (Finset.univ : Finset α).Nonempty)
    (indepNeighborsCard Gᶜ)
  have hvOne : indepNeighborsCard Gᶜ v = 1 := by
    rw [← hq]
    simpa [localIndependenceMin] using hv.symm
  have hdist : ∀ w : α, G.dist v w ≤ 2 :=
    dist_le_two_of_comp_indepNeighborsCard_eq_one hG hvOne
  obtain ⟨w, hw⟩ := G.exists_edist_eq_eccent_of_finite v
  have heccNat : (G.eccent v).toNat = G.dist v w := by
    unfold SimpleGraph.dist
    rw [hw]
  have heccLe : (G.eccent v).toNat ≤ 2 := by
    rw [heccNat]
    exact hdist w
  have hedFinite : G.ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hG
  have heccFinite : G.eccent v ≠ ⊤ := by
    intro heccTop
    apply hedFinite
    exact top_unique (heccTop ▸ (eccent_le_ediam (G := G) (u := v)))
  have hradLe : G.radius.toNat ≤ 2 := by
    exact (ENat.toNat_le_toNat (radius_le_eccent (G := G) (u := v)) heccFinite).trans heccLe
  have hradFinite : G.radius ≠ ⊤ := radius_ne_top_iff.mpr hG
  have hradPos : 0 < G.radius.toNat := by
    apply Nat.pos_of_ne_zero
    intro hz
    rcases ENat.toNat_eq_zero.mp hz with hzero | htop
    · exact radius_ne_zero_of_nontrivial (G := G) hzero
    · exact hradFinite htop
  rw [graphSquareRadius_eq hG]
  omega

/-- Exact proof of the Formal Conjectures statement for WOWII Conjecture 145. -/
theorem conjecture145_proof [DecidableRel G.Adj] (hG : G.Connected)
    (hlMin : 0 < localIndependenceMin Gᶜ) :
    2 * eccSet G (maxEccentricityVertices G : Set α) ≤
      largestInducedTreeSize G * localIndependenceMin Gᶜ := by
  let p := eccSet G (maxEccentricityVertices G : Set α)
  let d := G.diam
  let t := largestInducedTreeSize G
  let q := localIndependenceMin Gᶜ
  change 2 * p ≤ t * q
  have hqPos : 0 < q := by simpa [q] using hlMin
  have hpDiam : p + 1 ≤ d := by
    simpa [p, d] using eccSet_periphery_add_one_le_diam hG
  have hdiamTree : d + 1 ≤ t := by
    simpa [d, t] using diam_succ_le_largestInducedTreeSize hG
  have hpTree : p ≤ t := by omega
  by_cases hqTwo : 2 ≤ q
  · calc
      2 * p ≤ 2 * t := Nat.mul_le_mul_left 2 hpTree
      _ ≤ q * t := Nat.mul_le_mul_right t hqTwo
      _ = t * q := Nat.mul_comm _ _
  · have hqOne : q = 1 := by omega
    have hrho : graphSquareRadius G = 1 :=
      graphSquareRadius_eq_one_of_localIndependenceMin_compl_eq_one hG
        (by simpa [q] using hqOne)
    have hdLeFour : d ≤ 4 := by
      simpa [d] using WOW146.diam_le_four_of_graphSquareRadius_eq_one G hG hrho
    have hpLeThree : p ≤ 3 := by omega
    by_cases hpTwo : p ≤ 2
    · have hsmall : 2 * p ≤ t := by omega
      simpa [hqOne] using hsmall
    · have hpEq : p = 3 := by omega
      have hdEq : d = 4 := by omega
      have htSix : 6 ≤ t := by
        simpa [p, d, t] using
          WOW146.exceptional_six_vertex_induced_tree G hG hrho
            (by simpa [d] using hdEq) (by simpa [p] using hpEq)
      rw [hqOne, Nat.mul_one]
      omega

#check WrittenOnTheWallII.GraphConjecture145.conjecture145
#print axioms WOW145.dist_le_two_of_comp_indepNeighborsCard_eq_one
#print axioms WOW145.graphSquareRadius_eq_one_of_localIndependenceMin_compl_eq_one
#print axioms WOW145.conjecture145_proof

end WOW145
