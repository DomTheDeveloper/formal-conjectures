/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import FormalConjecturesUtil

namespace WrittenOnTheWallII.GraphConjecture160Audit

open Classical SimpleGraph

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

/-- The edge graph of a path is a forest, viewed on the original vertex type
with all vertices outside the path isolated. -/
lemma Walk.IsPath.spanningCoe_toSubgraph_isAcyclic
    {G : SimpleGraph α} {u v : α} {p : G.Walk u v} (hp : p.IsPath) :
    p.toSubgraph.spanningCoe.IsAcyclic := by
  induction p with
  | nil => simp
  | @cons u v w huv p ih =>
      have hpTail : p.IsPath := hp.tail
      have huNot : u ∉ p.support := by
        simpa only [Walk.support_cons] using
          (List.nodup_cons.mp hp.support_nodup).1
      have huIso : ∀ z, ¬ p.toSubgraph.spanningCoe.Adj u z := by
        intro z huz
        exact huNot (p.mem_verts_toSubgraph.mp (p.toSubgraph.edge_vert huz))
      have hur : ¬ p.toSubgraph.spanningCoe.Reachable u v :=
        not_reachable_of_isolated p.toSubgraph.spanningCoe huv.ne huIso
      rw [Walk.toSubgraph, Subgraph.sup_spanningCoe,
        Subgraph.spanningCoe_subgraphOfAdj, sup_comm]
      exact (isAcyclic_add_edge_iff_of_not_reachable u v hur).2 (ih hpTail)

private noncomputable def leaves (T : SimpleGraph α) [DecidableRel T.Adj] : Finset α :=
  Finset.univ.filter fun v => T.degree v = 1

private noncomputable def internal (T : SimpleGraph α) [DecidableRel T.Adj] : Finset α :=
  Finset.univ.filter fun v => T.degree v ≠ 1

private lemma leaf_identity (T : SimpleGraph α) [DecidableRel T.Adj]
    (hT : T.IsTree) :
    (leaves T).card = 2 +
      ∑ v ∈ internal T, ((T.degree v : ℤ) - 2) := by
  let L := leaves T
  let I := internal T
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
    simpa [L, I] using
      (Finset.filter_union_filter_neg_eq (Finset.univ : Finset α)
        (fun v => T.degree v = 1))
  have hdisj : Disjoint L I := by
    simpa [L, I] using
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
        have hd : T.degree v = 1 := by simpa [L, leaves] using hv
        simp [hd]
      _ = -(L.card : ℤ) := by simp
  change (L.card : ℤ) = 2 + ∑ v ∈ I, ((T.degree v : ℤ) - 2)
  linarith

private lemma internal_term_nonneg (T : SimpleGraph α) [DecidableRel T.Adj]
    (hT : T.IsTree) {v : α} (hv : v ∈ internal T) :
    0 ≤ (T.degree v : ℤ) - 2 := by
  have hne : T.degree v ≠ 1 := by simpa [internal] using hv
  have hpos : 0 < T.degree v := hT.connected.degree_pos_of_nontrivial v
  omega

/-- In a finite nontrivial tree, the number of leaves is at least the sum of
any two distinct vertex degrees minus two. -/
lemma two_degrees_sub_two_le_leaves (T : SimpleGraph α) [DecidableRel T.Adj]
    (hT : T.IsTree) {x y : α} (hxy : x ≠ y) :
    (T.degree x : ℤ) + T.degree y - 2 ≤ ((leaves T).card : ℤ) := by
  rw [leaf_identity T hT]
  let I := internal T
  have hnonneg : ∀ v ∈ I, 0 ≤ (T.degree v : ℤ) - 2 := by
    intro v hv
    exact internal_term_nonneg T hT (by simpa [I])
  by_cases hx : T.degree x = 1
  · by_cases hy : T.degree y = 1
    · simp [hx, hy]
      exact Finset.sum_nonneg fun v hv => hnonneg v hv
    · have hyI : y ∈ I := by simp [I, internal, hy]
      have hle := I.single_le_sum hnonneg hyI
      simp [hx]
      linarith
  · by_cases hy : T.degree y = 1
    · have hxI : x ∈ I := by simp [I, internal, hx]
      have hle := I.single_le_sum hnonneg hxI
      simp [hy]
      linarith
    · have hxI : x ∈ I := by simp [I, internal, hx]
      have hyI : y ∈ I := by simp [I, internal, hy]
      have hle := I.add_le_sum hnonneg hxI hyI hxy
      linarith

#print axioms Walk.IsPath.spanningCoe_toSubgraph_isAcyclic
#print axioms two_degrees_sub_two_le_leaves

end WrittenOnTheWallII.GraphConjecture160Audit
