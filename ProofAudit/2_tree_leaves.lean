/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import ProofAudit.«2_ls_bridge»

/-!
# WOWII Conjecture 2: the tree leaf identity
-/

namespace WrittenOnTheWallII.GraphConjecture2Audit

open Classical Finset SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

private noncomputable def internalVertices
    (T : SimpleGraph α) [DecidableRel T.Adj] : Finset α :=
  Finset.univ.filter fun v => T.degree v ≠ 1

private lemma tree_leaf_identity
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) :
    ((treeLeaves T).card : ℤ) = 2 +
      ∑ v ∈ internalVertices T, ((T.degree v : ℤ) - 2) := by
  let L := treeLeaves T
  let I := internalVertices T
  have hsumNat := T.sum_degrees_eq_twice_card_edges
  have hedgeNat := hT.card_edgeFinset
  have hsum : (∑ v, (T.degree v : ℤ)) = 2 * (T.edgeFinset.card : ℤ) := by
    exact_mod_cast hsumNat
  have hedge : (T.edgeFinset.card : ℤ) + 1 = (Fintype.card α : ℤ) := by
    exact_mod_cast hedgeNat
  have hdiff : (∑ v, ((T.degree v : ℤ) - 2)) = -2 := by
    rw [Finset.sum_sub_distrib, hsum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    linarith
  have huniv : (Finset.univ : Finset α) = L ∪ I := by
    ext v
    by_cases hv : T.degree v = 1 <;>
      simp [L, I, treeLeaves, internalVertices, hv]
  have hdisj : Disjoint L I := by
    rw [Finset.disjoint_left]
    intro v hvL hvI
    have hleaf : T.degree v = 1 := by
      simpa [L, treeLeaves] using hvL
    have hinternal : T.degree v ≠ 1 := by
      simpa [I, internalVertices] using hvI
    exact hinternal hleaf
  have hsplit :
      (∑ v, ((T.degree v : ℤ) - 2)) =
        (∑ v ∈ L, ((T.degree v : ℤ) - 2)) +
          ∑ v ∈ I, ((T.degree v : ℤ) - 2) := by
    rw [← Finset.sum_union hdisj, ← huniv]
  have hleaf :
      (∑ v ∈ L, ((T.degree v : ℤ) - 2)) = -(L.card : ℤ) := by
    calc
      (∑ v ∈ L, ((T.degree v : ℤ) - 2)) = ∑ _v ∈ L, (-1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro v hv
        have hd : T.degree v = 1 := by
          simpa [L, treeLeaves] using hv
        simp [hd]
      _ = -(L.card : ℤ) := by simp
  change (L.card : ℤ) = 2 + ∑ v ∈ I, ((T.degree v : ℤ) - 2)
  linarith

private lemma internal_term_nonneg
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree)
    {v : α} (hv : v ∈ internalVertices T) :
    0 ≤ (T.degree v : ℤ) - 2 := by
  have hne : T.degree v ≠ 1 := by
    simpa [internalVertices] using hv
  have hpos : 0 < T.degree v :=
    hT.isConnected.preconnected.degree_pos_of_nontrivial v
  omega

/-- In a finite nontrivial tree, the number of leaves is at least the sum of
any two distinct vertex degrees minus two. -/
lemma two_degrees_sub_two_le_treeLeaves
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree)
    {x y : α} (hxy : x ≠ y) :
    (T.degree x : ℤ) + T.degree y - 2 ≤ ((treeLeaves T).card : ℤ) := by
  let I := internalVertices T
  let S : ℤ := ∑ v ∈ I, ((T.degree v : ℤ) - 2)
  have hleafid : ((treeLeaves T).card : ℤ) = 2 + S := by
    simpa [S, I] using tree_leaf_identity T hT
  have hnonneg : ∀ v ∈ I, 0 ≤ (T.degree v : ℤ) - 2 := by
    intro v hv
    exact internal_term_nonneg T hT (by simpa [I])
  have hsum_nonneg : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun v hv => hnonneg v hv
  by_cases hx : T.degree x = 1
  · by_cases hy : T.degree y = 1
    · calc
        (T.degree x : ℤ) + T.degree y - 2 = 0 := by simp [hx, hy]
        _ ≤ 2 + S := by linarith
        _ = ((treeLeaves T).card : ℤ) := hleafid.symm
    · have hyI : y ∈ I := by simp [I, internalVertices, hy]
      have hle : (T.degree y : ℤ) - 2 ≤ S := by
        dsimp [S]
        exact I.single_le_sum hnonneg hyI
      calc
        (T.degree x : ℤ) + T.degree y - 2 = (T.degree y : ℤ) - 1 := by
          norm_num [hx]
        _ ≤ 2 + S := by linarith
        _ = ((treeLeaves T).card : ℤ) := hleafid.symm
  · by_cases hy : T.degree y = 1
    · have hxI : x ∈ I := by simp [I, internalVertices, hx]
      have hle : (T.degree x : ℤ) - 2 ≤ S := by
        dsimp [S]
        exact I.single_le_sum hnonneg hxI
      calc
        (T.degree x : ℤ) + T.degree y - 2 = (T.degree x : ℤ) - 1 := by
          norm_num [hy]
        _ ≤ 2 + S := by linarith
        _ = ((treeLeaves T).card : ℤ) := hleafid.symm
    · have hxI : x ∈ I := by simp [I, internalVertices, hx]
      have hyI : y ∈ I := by simp [I, internalVertices, hy]
      have hle : (T.degree x : ℤ) - 2 + ((T.degree y : ℤ) - 2) ≤ S := by
        dsimp [S]
        exact I.add_le_sum hnonneg hxI hyI hxy
      calc
        (T.degree x : ℤ) + T.degree y - 2 =
            2 + ((T.degree x : ℤ) - 2 + ((T.degree y : ℤ) - 2)) := by ring
        _ ≤ 2 + S := by linarith
        _ = ((treeLeaves T).card : ℤ) := hleafid.symm

#print axioms two_degrees_sub_two_le_treeLeaves

end WrittenOnTheWallII.GraphConjecture2Audit
