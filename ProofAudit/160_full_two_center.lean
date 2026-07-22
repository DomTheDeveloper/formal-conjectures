/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import ProofAudit.«160_double_star»
import ProofAudit.«160_star_bound»
import ProofAudit.«160_common_neighbors»
import ProofAudit.«160_tree_bridge»

namespace WrittenOnTheWallII.GraphConjecture160Audit

open Classical SimpleGraph Finset

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

private lemma not_reachable_of_isolated_full
    (H : SimpleGraph α) {u v : α} (huv : u ≠ v)
    (hv : ∀ w, ¬ H.Adj v w) : ¬ H.Reachable u v := by
  rintro ⟨p⟩
  cases p with
  | nil => exact huv rfl
  | @cons a b c hab q =>
      have hn : ¬ (Walk.cons hab q).Nil := by simp
      exact hv _ ((Walk.cons hab q).adj_penultimate hn).symm

noncomputable def remainingSecondLeaves160
    (G : SimpleGraph α) [DecidableRel G.Adj] (y z : α) : List α :=
  (G.neighborFinset y).erase z |>.toList

/-- Full star at `x`, the middle edge `y-z`, and every remaining edge at `y`. -/
noncomputable def fullTwoCenterSeed160
    (G : SimpleGraph α) [DecidableRel G.Adj] (x y z : α) : SimpleGraph α :=
  let Hx := starSeed160 G x
  let Hmid := Hx ⊔ edge y z
  attachLeaves Hmid y (remainingSecondLeaves160 G y z)

lemma fullTwoCenterSeed160_isAcyclic
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hC4 : NoFourCycle G) {x y z : α}
    (hxy : x ≠ y) (hnotadj : ¬ G.Adj x y)
    (hxz : G.Adj x z) (hyz : G.Adj y z) :
    (fullTwoCenterSeed160 G x y z).IsAcyclic := by
  let Hx := starSeed160 G x
  let Hmid := Hx ⊔ edge y z
  let Ly := remainingSecondLeaves160 G y z
  have hHx : Hx.IsAcyclic := starSeed160_isAcyclic G x
  have hyNotLx : y ∉ starLeaves160 G x := by
    simpa [starLeaves160] using hnotadj
  have hyIsoHx : ∀ w, ¬ Hx.Adj y w := by
    exact attachLeaves_isolated_of_not_mem (⊥ : SimpleGraph α) x y
      (starLeaves160 G x) (by simp) hxy.symm hyNotLx
  have hyz_ne : y ≠ z := hyz.ne
  have hUnreach : ¬ Hx.Reachable y z :=
    not_reachable_of_isolated_full Hx hyz_ne hyIsoHx
  have hMid : Hmid.IsAcyclic := by
    simpa [Hmid] using hHx.sup_edge_of_not_reachable hUnreach
  have hLy : Ly.Nodup := by simp [Ly, remainingSecondLeaves160]
  have hyLy : y ∉ Ly := by simp [Ly, remainingSecondLeaves160]
  have hCommon := common_neighbors_subsingleton_of_ne G hC4 hxy
  have hzCommon : z ∈ G.neighborSet x ∩ G.neighborSet y := by
    exact ⟨hxz, hyz⟩
  have hIso : ∀ w ∈ Ly, ∀ q, ¬ Hmid.Adj w q := by
    intro w hw q hwq
    have hwNy : w ∈ G.neighborFinset y := by
      have := (Finset.mem_erase.mp (by simpa [Ly, remainingSecondLeaves160] using hw)).2
      exact this
    have hwz : w ≠ z :=
      (Finset.mem_erase.mp (by simpa [Ly, remainingSecondLeaves160] using hw)).1
    have hwy : w ≠ y := (by simpa using (show G.Adj y w from by simpa using hwNy).ne.symm)
    have hwNotNx : w ∉ G.neighborFinset x := by
      intro hwNx
      have hwCommon : w ∈ G.neighborSet x ∩ G.neighborSet y := by
        exact ⟨by simpa using hwNx, by simpa using hwNy⟩
      exact hwz (hCommon hwCommon hzCommon)
    have hwNotLx : w ∉ starLeaves160 G x := by
      simpa [starLeaves160] using hwNotNx
    have hwIsoHx : ∀ r, ¬ Hx.Adj w r :=
      attachLeaves_isolated_of_not_mem (⊥ : SimpleGraph α) x w
        (starLeaves160 G x) (by simp) (by
          intro h
          subst w
          exact hwNotNx (by simpa using hxz)) hwNotLx
    change Hx.Adj w q ∨ (edge y z).Adj w q at hwq
    rcases hwq with hwq | hwq
    · exact hwIsoHx q hwq
    · rw [edge_adj] at hwq
      rcases hwq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hwy rfl
      · exact hwz rfl
  simpa [fullTwoCenterSeed160, Hx, Hmid, Ly] using
    attachLeaves_isAcyclic Hmid y Ly hMid hLy hyLy hIso

lemma fullTwoCenterSeed160_le
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {x y z : α} (hyz : G.Adj y z) :
    fullTwoCenterSeed160 G x y z ≤ G := by
  let Hx := starSeed160 G x
  let Hmid := Hx ⊔ edge y z
  let Ly := remainingSecondLeaves160 G y z
  have hHx : Hx ≤ G := starSeed160_le G x
  have hMid : Hmid ≤ G := by
    intro a b hab
    change Hx.Adj a b ∨ (edge y z).Adj a b at hab
    rcases hab with hab | hab
    · exact hHx hab
    · rw [edge_adj] at hab
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hyz
      · exact hyz.symm
  apply attachLeaves_le Hmid G y Ly hMid
  intro w hw
  have hwNy : w ∈ G.neighborFinset y := by
    have := (Finset.mem_erase.mp (by simpa [Ly, remainingSecondLeaves160] using hw)).2
    exact this
  simpa using hwNy

lemma fullTwoCenterSeed160_adj_first
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (x y z : α) {w : α} (hw : w ∈ G.neighborFinset x) :
    (fullTwoCenterSeed160 G x y z).Adj x w := by
  let Hx := starSeed160 G x
  let Hmid := Hx ⊔ edge y z
  have hxw : Hx.Adj x w := starSeed160_adj G x hw
  have hmid : Hmid.Adj x w := Or.inl hxw
  exact (base_le_attachLeaves Hmid y (remainingSecondLeaves160 G y z)) hmid

lemma fullTwoCenterSeed160_adj_second
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (x y z : α) {w : α} (hw : w ∈ G.neighborFinset y) :
    (fullTwoCenterSeed160 G x y z).Adj y w := by
  by_cases hwz : w = z
  · subst w
    have hmid : (starSeed160 G x ⊔ edge y z).Adj y z := Or.inr (by simp)
    exact (base_le_attachLeaves (starSeed160 G x ⊔ edge y z) y
      (remainingSecondLeaves160 G y z)) hmid
  · apply attachLeaves_adj_of_mem
    simp [remainingSecondLeaves160, hw, hwz]

lemma full_degrees_le_of_fullTwoCenterSeed160_le
    (G T : SimpleGraph α) [DecidableRel G.Adj] [DecidableRel T.Adj]
    (x y z : α) (hseed : fullTwoCenterSeed160 G x y z ≤ T) :
    G.degree x ≤ T.degree x ∧ G.degree y ≤ T.degree y := by
  constructor
  · rw [← G.card_neighborFinset_eq_degree, ← T.card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro w hw
    simpa using hseed (fullTwoCenterSeed160_adj_first G x y z hw)
  · rw [← G.card_neighborFinset_eq_degree, ← T.card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro w hw
    simpa using hseed (fullTwoCenterSeed160_adj_second G x y z hw)

lemma degree_sum_sub_two_le_Ls_of_nonadj_common
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) (hC4 : NoFourCycle G)
    {x y z : α} (hxy : x ≠ y) (hnotadj : ¬ G.Adj x y)
    (hxz : G.Adj x z) (hyz : G.Adj y z) :
    (G.degree x : ℝ) + G.degree y - 2 ≤ Ls G := by
  obtain ⟨T, hseedT, hTG, hT⟩ :=
    hG.exists_isTree_le_of_le_of_isAcyclic
      (fullTwoCenterSeed160_le G hyz)
      (fullTwoCenterSeed160_isAcyclic G hC4 hxy hnotadj hxz hyz)
  letI : DecidableRel T.Adj := Classical.decRel T.Adj
  have hdeg := full_degrees_le_of_fullTwoCenterSeed160_le G T x y z hseedT
  have hdegR :
      (G.degree x : ℝ) + G.degree y - 2 ≤
        (T.degree x : ℝ) + T.degree y - 2 := by
    exact_mod_cast add_le_add hdeg.1 hdeg.2
  have hleafInt := two_degrees_sub_two_le_treeLeaves160 T hT hxy
  have hleaf :
      (T.degree x : ℝ) + T.degree y - 2 ≤ ((treeLeaves160 T).card : ℝ) := by
    exact_mod_cast hleafInt
  exact hdegR.trans (hleaf.trans (treeLeaves160_card_le_Ls G T hTG hT))

#print axioms fullTwoCenterSeed160_isAcyclic
#print axioms degree_sum_sub_two_le_Ls_of_nonadj_common

end WrittenOnTheWallII.GraphConjecture160Audit
