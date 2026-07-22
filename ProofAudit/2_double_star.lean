/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import ProofAudit.«2_ls_bridge»

namespace WrittenOnTheWallII.GraphConjecture2Audit

open Classical Finset SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

private lemma not_reachable_of_isolated
    (H : SimpleGraph α) {u v : α} (huv : u ≠ v)
    (hv : ∀ w, ¬ H.Adj v w) : ¬ H.Reachable u v := by
  rintro ⟨p⟩
  cases p with
  | nil => exact huv rfl
  | @cons a b c hab q =>
      have hn : ¬ (Walk.cons hab q).Nil := by simp
      exact hv _ ((Walk.cons hab q).adj_penultimate hn).symm

/-- Add edges from a center to the vertices of a list, processing the tail
first so induction exposes one fresh leaf at a time. -/
def attachLeaves (H : SimpleGraph α) (c : α) : List α → SimpleGraph α
  | [] => H
  | v :: vs => attachLeaves H c vs ⊔ edge c v

lemma base_le_attachLeaves
    (H : SimpleGraph α) (c : α) (L : List α) :
    H ≤ attachLeaves H c L := by
  induction L with
  | nil => simp [attachLeaves]
  | cons v vs ih =>
      exact ih.trans le_sup_left

lemma attachLeaves_isolated_of_not_mem
    (H : SimpleGraph α) (c v : α) (L : List α)
    (hvH : ∀ z, ¬ H.Adj v z) (hvc : v ≠ c) (hvL : v ∉ L) :
    ∀ z, ¬ (attachLeaves H c L).Adj v z := by
  induction L with
  | nil => simpa [attachLeaves] using hvH
  | cons w ws ih =>
      have hvw : v ≠ w := by
        intro h
        exact hvL (by simp [h])
      have hvws : v ∉ ws := by
        intro h
        exact hvL (by simp [h])
      intro z hz
      change (attachLeaves H c ws).Adj v z ∨ (edge c w).Adj v z at hz
      rcases hz with hz | hz
      · exact ih hvws z hz
      · rw [edge_adj] at hz
        rcases hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hvc rfl
        · exact hvw rfl

lemma attachLeaves_isAcyclic
    (H : SimpleGraph α) (c : α) (L : List α)
    (hH : H.IsAcyclic) (hL : L.Nodup) (hcL : c ∉ L)
    (hIso : ∀ v ∈ L, ∀ z, ¬ H.Adj v z) :
    (attachLeaves H c L).IsAcyclic := by
  induction L with
  | nil => simpa [attachLeaves] using hH
  | cons v vs ih =>
      have hnod := List.nodup_cons.mp hL
      have hcv : c ≠ v := by
        intro h
        exact hcL (by simp [h])
      have hcvs : c ∉ vs := by
        intro h
        exact hcL (by simp [h])
      have hTail : (attachLeaves H c vs).IsAcyclic :=
        ih hnod.2 hcvs (fun w hw => hIso w (by simp [hw]))
      have hvIsoH : ∀ z, ¬ H.Adj v z := hIso v (by simp)
      have hvIsoTail : ∀ z, ¬ (attachLeaves H c vs).Adj v z :=
        attachLeaves_isolated_of_not_mem H c v vs hvIsoH hcv.symm hnod.1
      have hUnreach : ¬ (attachLeaves H c vs).Reachable c v :=
        not_reachable_of_isolated (attachLeaves H c vs) hcv hvIsoTail
      simpa [attachLeaves] using hTail.sup_edge_of_not_reachable hUnreach

lemma attachLeaves_le
    (H G : SimpleGraph α) (c : α) (L : List α)
    (hHG : H ≤ G) (hAdj : ∀ v ∈ L, G.Adj c v) :
    attachLeaves H c L ≤ G := by
  induction L with
  | nil => simpa [attachLeaves] using hHG
  | cons v vs ih =>
      intro a b hab
      change (attachLeaves H c vs).Adj a b ∨ (edge c v).Adj a b at hab
      rcases hab with hab | hab
      · exact ih (fun w hw => hAdj w (by simp [hw])) hab
      · rw [edge_adj] at hab
        rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hAdj v (by simp)
        · exact (hAdj v (by simp)).symm

lemma attachLeaves_adj_of_mem
    (H : SimpleGraph α) (c : α) (L : List α) {v : α} (hv : v ∈ L) :
    (attachLeaves H c L).Adj c v := by
  induction L with
  | nil => simp at hv
  | cons w ws ih =>
      simp only [List.mem_cons] at hv
      change (attachLeaves H c ws).Adj c v ∨ (edge c w).Adj c v
      rcases hv with rfl | hv
      · right
        simp
      · exact Or.inl (ih hv)

noncomputable def firstLeaves
    (G : SimpleGraph α) [DecidableRel G.Adj] (x : α) : List α :=
  (G.neighborFinset x).toList

noncomputable def secondLeaves
    (G : SimpleGraph α) [DecidableRel G.Adj] (x y : α) : List α :=
  ((G.neighborFinset y \ G.neighborFinset x).erase x).toList

/-- The double-star contains the full star at `x` and then all genuinely new
neighbors of `y`, excluding the already-present center `x`. -/
noncomputable def doubleStarSeed
    (G : SimpleGraph α) [DecidableRel G.Adj] (x y : α) : SimpleGraph α :=
  attachLeaves (attachLeaves (⊥ : SimpleGraph α) x (firstLeaves G x))
    y (secondLeaves G x y)

lemma doubleStarSeed_isAcyclic
    (G : SimpleGraph α) [DecidableRel G.Adj] (x y : α) :
    (doubleStarSeed G x y).IsAcyclic := by
  let Lx := firstLeaves G x
  let Ly := secondLeaves G x y
  let Hx := attachLeaves (⊥ : SimpleGraph α) x Lx
  have hLx : Lx.Nodup := by
    simp [Lx, firstLeaves]
  have hxLx : x ∉ Lx := by
    simp [Lx, firstLeaves]
  have hHx : Hx.IsAcyclic := by
    apply attachLeaves_isAcyclic (⊥ : SimpleGraph α) x Lx isAcyclic_bot hLx hxLx
    simp
  have hLy : Ly.Nodup := by
    simp [Ly, secondLeaves]
  have hyLy : y ∉ Ly := by
    simp [Ly, secondLeaves]
  have hIso : ∀ v ∈ Ly, ∀ z, ¬ Hx.Adj v z := by
    intro v hv z
    have hv' : v ∈ (G.neighborFinset y \ G.neighborFinset x).erase x := by
      simpa [Ly, secondLeaves] using hv
    have hvx : v ≠ x := (Finset.mem_erase.mp hv').1
    have hvNotNx : v ∉ G.neighborFinset x :=
      (Finset.mem_sdiff.mp (Finset.mem_erase.mp hv').2).2
    have hvNotLx : v ∉ Lx := by
      simpa [Lx, firstLeaves] using hvNotNx
    exact attachLeaves_isolated_of_not_mem (⊥ : SimpleGraph α) x v Lx
      (by simp) hvx hvNotLx z
  simpa [doubleStarSeed, Hx, Lx, Ly] using
    attachLeaves_isAcyclic Hx y Ly hHx hLy hyLy hIso

lemma doubleStarSeed_le
    (G : SimpleGraph α) [DecidableRel G.Adj] (x y : α) :
    doubleStarSeed G x y ≤ G := by
  let Lx := firstLeaves G x
  let Ly := secondLeaves G x y
  let Hx := attachLeaves (⊥ : SimpleGraph α) x Lx
  have hHx : Hx ≤ G := by
    apply attachLeaves_le (⊥ : SimpleGraph α) G x Lx bot_le
    intro v hv
    have hv' : v ∈ G.neighborFinset x := by
      simpa [Lx, firstLeaves] using hv
    simpa using hv'
  apply attachLeaves_le Hx G y Ly hHx
  intro v hv
  have hv' : v ∈ (G.neighborFinset y \ G.neighborFinset x).erase x := by
    simpa [Ly, secondLeaves] using hv
  have hvNy : v ∈ G.neighborFinset y :=
    (Finset.mem_sdiff.mp (Finset.mem_erase.mp hv').2).1
  simpa using hvNy

#print axioms doubleStarSeed_isAcyclic
#print axioms doubleStarSeed_le

end WrittenOnTheWallII.GraphConjecture2Audit
