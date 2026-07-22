/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import ProofAudit.«160_attempt»
import ProofAudit.«160_common_neighbors»

namespace WrittenOnTheWallII.GraphConjecture160Audit

open Classical SimpleGraph Finset

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

noncomputable def firstStarLeaves
    (G : SimpleGraph α) [DecidableRel G.Adj] (x : α) : List α :=
  (G.neighborFinset x).toList

noncomputable def secondStarNewLeaves
    (G : SimpleGraph α) [DecidableRel G.Adj] (x y : α) : List α :=
  ((G.neighborFinset y \ G.neighborFinset x).erase x).toList

noncomputable def twoCenterSeed
    (G : SimpleGraph α) [DecidableRel G.Adj] (x y : α) : SimpleGraph α :=
  attachLeaves (attachLeaves (⊥ : SimpleGraph α) x (firstStarLeaves G x))
    y (secondStarNewLeaves G x y)

lemma base_le_attachLeaves
    (H : SimpleGraph α) (c : α) (L : List α) :
    H ≤ attachLeaves H c L := by
  induction L with
  | nil => simp [attachLeaves]
  | cons v vs ih => exact ih.trans le_sup_left

lemma twoCenterSeed_isAcyclic
    (G : SimpleGraph α) [DecidableRel G.Adj] (x y : α) :
    (twoCenterSeed G x y).IsAcyclic := by
  let Lx := firstStarLeaves G x
  let Ly := secondStarNewLeaves G x y
  let Hx := attachLeaves (⊥ : SimpleGraph α) x Lx
  have hLx : Lx.Nodup := by simp [Lx, firstStarLeaves]
  have hxLx : x ∉ Lx := by simp [Lx, firstStarLeaves]
  have hHx : Hx.IsAcyclic := by
    apply attachLeaves_isAcyclic (⊥ : SimpleGraph α) x Lx isAcyclic_bot hLx hxLx
    simp
  have hLy : Ly.Nodup := by simp [Ly, secondStarNewLeaves]
  have hyLy : y ∉ Ly := by simp [Ly, secondStarNewLeaves]
  have hIso : ∀ v ∈ Ly, ∀ z, ¬ Hx.Adj v z := by
    intro v hv z
    have hv' : v ∈ (G.neighborFinset y \ G.neighborFinset x).erase x := by
      simpa [Ly, secondStarNewLeaves] using hv
    have hvx : v ≠ x := (Finset.mem_erase.mp hv').1
    have hvNotNx : v ∉ G.neighborFinset x :=
      (Finset.mem_sdiff.mp (Finset.mem_erase.mp hv').2).2
    have hvNotLx : v ∉ Lx := by
      simpa [Lx, firstStarLeaves] using hvNotNx
    exact attachLeaves_isolated_of_not_mem (⊥ : SimpleGraph α) x v Lx
      (by simp) hvx hvNotLx z
  simpa [twoCenterSeed, Hx, Lx, Ly] using
    attachLeaves_isAcyclic Hx y Ly hHx hLy hyLy hIso

lemma twoCenterSeed_le
    (G : SimpleGraph α) [DecidableRel G.Adj] (x y : α) :
    twoCenterSeed G x y ≤ G := by
  let Lx := firstStarLeaves G x
  let Ly := secondStarNewLeaves G x y
  let Hx := attachLeaves (⊥ : SimpleGraph α) x Lx
  have hHx : Hx ≤ G := by
    apply attachLeaves_le (⊥ : SimpleGraph α) G x Lx bot_le
    intro v hv
    have hv' : v ∈ G.neighborFinset x := by
      simpa [Lx, firstStarLeaves] using hv
    simpa using hv'
  apply attachLeaves_le Hx G y Ly hHx
  intro v hv
  have hv' : v ∈ (G.neighborFinset y \ G.neighborFinset x).erase x := by
    simpa [Ly, secondStarNewLeaves] using hv
  have hvNy : v ∈ G.neighborFinset y :=
    (Finset.mem_sdiff.mp (Finset.mem_erase.mp hv').2).1
  simpa using hvNy

lemma twoCenterSeed_adj_first
    (G : SimpleGraph α) [DecidableRel G.Adj] (x y : α) {z : α}
    (hz : z ∈ G.neighborFinset x) :
    (twoCenterSeed G x y).Adj x z := by
  let Hx := attachLeaves (⊥ : SimpleGraph α) x (firstStarLeaves G x)
  have hxz : Hx.Adj x z := by
    apply attachLeaves_adj_of_mem
    simpa [firstStarLeaves] using hz
  exact (base_le_attachLeaves Hx y (secondStarNewLeaves G x y)) hxz

lemma twoCenterSeed_adj_second_sdiff
    (G : SimpleGraph α) [DecidableRel G.Adj] (x y : α) {z : α}
    (hz : z ∈ G.neighborFinset y \ G.neighborFinset x) :
    (twoCenterSeed G x y).Adj y z := by
  by_cases hzx : z = x
  · subst z
    have hyx : G.Adj y x := by simpa using hz.1
    have hyNx : y ∈ G.neighborFinset x := by simpa using hyx.symm
    exact (twoCenterSeed_adj_first G x y hyNx).symm
  · have hzLy : z ∈ secondStarNewLeaves G x y := by
      simp [secondStarNewLeaves, hz.1, hz.2, hzx]
    exact attachLeaves_adj_of_mem
      (attachLeaves (⊥ : SimpleGraph α) x (firstStarLeaves G x))
      y (secondStarNewLeaves G x y) hzLy

lemma union_card_le_degree_sum_of_seed_le
    (G T : SimpleGraph α) [DecidableRel G.Adj] [DecidableRel T.Adj]
    (x y : α) (hseed : twoCenterSeed G x y ≤ T) :
    (G.neighborFinset x ∪ G.neighborFinset y).card ≤
      T.degree x + T.degree y := by
  have hx : G.degree x ≤ T.degree x := by
    rw [← G.card_neighborFinset_eq_degree, ← T.card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro z hz
    simpa using hseed (twoCenterSeed_adj_first G x y hz)
  have hy : (G.neighborFinset y \ G.neighborFinset x).card ≤ T.degree y := by
    rw [← T.card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro z hz
    simpa using hseed (twoCenterSeed_adj_second_sdiff G x y hz)
  have hcard := Finset.card_sdiff_add_card
    (G.neighborFinset y) (G.neighborFinset x)
  rw [Finset.union_comm] at hcard
  omega

#print axioms twoCenterSeed_isAcyclic
#print axioms twoCenterSeed_le
#print axioms union_card_le_degree_sum_of_seed_le

end WrittenOnTheWallII.GraphConjecture160Audit
