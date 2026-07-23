/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import ProofAudit.«2_ls_bridge»

/-!
# WOWII Conjecture 2: the double-star forest seed
-/

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
  | cons head tail ih =>
      exact ih.trans le_sup_left

lemma attachLeaves_isolated_of_not_mem
    (H : SimpleGraph α) (c v : α) (L : List α)
    (hvH : ∀ z, ¬ H.Adj v z) (hvc : v ≠ c) (hvL : v ∉ L) :
    ∀ z, ¬ (attachLeaves H c L).Adj v z := by
  induction L with
  | nil => simpa [attachLeaves] using hvH
  | cons head tail ih =>
      have hvhead : v ≠ head := by
        intro h
        exact hvL (by simp [h])
      have hvtail : v ∉ tail := by
        intro h
        exact hvL (by simp [h])
      intro z hz
      change (attachLeaves H c tail).Adj v z ∨ (edge c head).Adj v z at hz
      rcases hz with hz | hz
      · exact ih hvtail z hz
      · rw [edge_adj] at hz
        rcases hz.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hvc rfl
        · exact hvhead rfl

lemma attachLeaves_isAcyclic
    (H : SimpleGraph α) (c : α) (L : List α)
    (hH : H.IsAcyclic) (hL : L.Nodup) (hcL : c ∉ L)
    (hIso : ∀ v ∈ L, ∀ z, ¬ H.Adj v z) :
    (attachLeaves H c L).IsAcyclic := by
  induction L with
  | nil => simpa [attachLeaves] using hH
  | cons head tail ih =>
      have hnod := List.nodup_cons.mp hL
      have hchead : c ≠ head := by
        intro h
        exact hcL (by simp [h])
      have hctail : c ∉ tail := by
        intro h
        exact hcL (by simp [h])
      have hTail : (attachLeaves H c tail).IsAcyclic :=
        ih hnod.2 hctail (fun w hw => hIso w (by simp [hw]))
      have hheadIsoH : ∀ z, ¬ H.Adj head z := hIso head (by simp)
      have hheadIsoTail : ∀ z, ¬ (attachLeaves H c tail).Adj head z :=
        attachLeaves_isolated_of_not_mem H c head tail hheadIsoH hchead.symm hnod.1
      have hUnreach : ¬ (attachLeaves H c tail).Reachable c head :=
        not_reachable_of_isolated (attachLeaves H c tail) hchead hheadIsoTail
      simpa [attachLeaves] using hTail.sup_edge_of_not_reachable hUnreach

lemma attachLeaves_le
    (H G : SimpleGraph α) (c : α) (L : List α)
    (hHG : H ≤ G) (hAdj : ∀ v ∈ L, G.Adj c v) :
    attachLeaves H c L ≤ G := by
  induction L with
  | nil => simpa [attachLeaves] using hHG
  | cons head tail ih =>
      intro a b hab
      change (attachLeaves H c tail).Adj a b ∨ (edge c head).Adj a b at hab
      rcases hab with hab | hab
      · exact ih (fun w hw => hAdj w (List.mem_cons_of_mem head hw)) hab
      · have hchead : G.Adj c head := hAdj head List.mem_cons_self
        rw [edge_adj] at hab
        rcases hab.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hchead
        · exact hchead.symm

lemma attachLeaves_adj_of_mem
    (H : SimpleGraph α) (c : α) (L : List α) {v : α} (hv : v ∈ L) :
    (attachLeaves H c L).Adj c v := by
  induction L with
  | nil => simp at hv
  | cons head tail ih =>
      simp only [List.mem_cons] at hv
      change (attachLeaves H c tail).Adj c v ∨ (edge c head).Adj c v
      rcases hv with rfl | hv
      · right
        exact edge_adj.2 ⟨Or.inl ⟨rfl, rfl⟩, by simp⟩
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
    simpa [Lx, firstLeaves] using (G.neighborFinset x).nodup_toList
  have hxLx : x ∉ Lx := by
    simp [Lx, firstLeaves]
  have hHx : Hx.IsAcyclic := by
    apply attachLeaves_isAcyclic (⊥ : SimpleGraph α) x Lx isAcyclic_bot hLx hxLx
    simp
  have hLy : Ly.Nodup := by
    simpa [Ly, secondLeaves] using
      ((G.neighborFinset y \ G.neighborFinset x).erase x).nodup_toList
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
    exact (G.mem_neighborFinset x v).1 hv'
  apply attachLeaves_le Hx G y Ly hHx
  intro v hv
  have hv' : v ∈ (G.neighborFinset y \ G.neighborFinset x).erase x := by
    simpa [Ly, secondLeaves] using hv
  have hvNy : v ∈ G.neighborFinset y :=
    (Finset.mem_sdiff.mp (Finset.mem_erase.mp hv').2).1
  exact (G.mem_neighborFinset y v).1 hvNy

#print axioms doubleStarSeed_isAcyclic
#print axioms doubleStarSeed_le

end WrittenOnTheWallII.GraphConjecture2Audit
