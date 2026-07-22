/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import FormalConjecturesUtil

namespace WrittenOnTheWallII.GraphConjecture160Audit

open Classical SimpleGraph Finset

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

noncomputable def treeLeaves160
    (T : SimpleGraph α) [DecidableRel T.Adj] : Finset α :=
  Finset.univ.filter fun v => T.degree v = 1

private noncomputable def internal160
    (T : SimpleGraph α) [DecidableRel T.Adj] : Finset α :=
  Finset.univ.filter fun v => T.degree v ≠ 1

private lemma leaf_identity160
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) :
    ((treeLeaves160 T).card : ℤ) = 2 +
      ∑ v ∈ internal160 T, ((T.degree v : ℤ) - 2) := by
  let L := treeLeaves160 T
  let I := internal160 T
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
    simpa [L, I, treeLeaves160, internal160] using
      (Finset.filter_union_filter_neg_eq (Finset.univ : Finset α)
        (fun v => T.degree v = 1))
  have hdisj : Disjoint L I := by
    simpa [L, I, treeLeaves160, internal160] using
      (Finset.disjoint_filter_filter_neg
        (s := (Finset.univ : Finset α)) (p := fun v => T.degree v = 1))
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
          simpa [L, treeLeaves160] using hv
        simp [hd]
      _ = -(L.card : ℤ) := by simp
  change (L.card : ℤ) = 2 + ∑ v ∈ I, ((T.degree v : ℤ) - 2)
  linarith

private lemma internal_term_nonneg160
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree)
    {v : α} (hv : v ∈ internal160 T) :
    0 ≤ (T.degree v : ℤ) - 2 := by
  have hne : T.degree v ≠ 1 := by simpa [internal160] using hv
  have hpos : 0 < T.degree v := hT.connected.degree_pos_of_nontrivial v
  omega

lemma degree_le_treeLeaves160
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) (x : α) :
    (T.degree x : ℤ) ≤ ((treeLeaves160 T).card : ℤ) := by
  rw [leaf_identity160 T hT]
  let I := internal160 T
  have hnonneg : ∀ v ∈ I, 0 ≤ (T.degree v : ℤ) - 2 := by
    intro v hv
    exact internal_term_nonneg160 T hT (by simpa [I])
  by_cases hx : T.degree x = 1
  · simp [hx]
    exact Finset.sum_nonneg fun v hv => hnonneg v hv
  · have hxI : x ∈ I := by simp [I, internal160, hx]
    have hle := I.single_le_sum hnonneg hxI
    linarith

lemma two_degrees_sub_two_le_treeLeaves160
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree)
    {x y : α} (hxy : x ≠ y) :
    (T.degree x : ℤ) + T.degree y - 2 ≤ ((treeLeaves160 T).card : ℤ) := by
  rw [leaf_identity160 T hT]
  let I := internal160 T
  have hnonneg : ∀ v ∈ I, 0 ≤ (T.degree v : ℤ) - 2 := by
    intro v hv
    exact internal_term_nonneg160 T hT (by simpa [I])
  by_cases hx : T.degree x = 1
  · by_cases hy : T.degree y = 1
    · simp [hx, hy]
      exact Finset.sum_nonneg fun v hv => hnonneg v hv
    · have hyI : y ∈ I := by simp [I, internal160, hy]
      have hle := I.single_le_sum hnonneg hyI
      simp [hx]
      linarith
  · by_cases hy : T.degree y = 1
    · have hxI : x ∈ I := by simp [I, internal160, hx]
      have hle := I.single_le_sum hnonneg hxI
      simp [hy]
      linarith
    · have hxI : x ∈ I := by simp [I, internal160, hx]
      have hyI : y ∈ I := by simp [I, internal160, hy]
      have hle := I.add_le_sum hnonneg hxI hyI hxy
      linarith

lemma treeLeaves160_card_le_Ls
    (G T : SimpleGraph α) [DecidableRel G.Adj] [DecidableRel T.Adj]
    (hTG : T ≤ G) (hT : T.IsTree) :
    ((treeLeaves160 T).card : ℝ) ≤ Ls G := by
  let S : G.Subgraph := T.toSubgraph G hTG
  have hSspan : S.IsSpanning := SimpleGraph.toSubgraph.isSpanning T hTG
  have hScoe : S.coe.IsTree := by
    have hSpanTree : S.spanningCoe.IsTree := by simpa [S] using hT
    exact (SimpleGraph.Iso.isTree_iff
      (S.spanningCoeEquivCoeOfSpanning hSspan)).mp hSpanTree
  unfold Ls
  apply le_csSup
  · refine ⟨(Fintype.card α : ℝ), ?_⟩
    rintro z ⟨U, _hU, rfl⟩
    exact_mod_cast
      (U.verts.toFinset.filter (fun v => U.degree v = 1)).card_le_univ
  · refine ⟨S, ⟨hSspan, hScoe⟩, ?_⟩
    simp [treeLeaves160, S, SimpleGraph.toSubgraph]

#print axioms degree_le_treeLeaves160
#print axioms two_degrees_sub_two_le_treeLeaves160
#print axioms treeLeaves160_card_le_Ls

end WrittenOnTheWallII.GraphConjecture160Audit
