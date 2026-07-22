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

/-- Add the edges from `c` to the vertices in a list, processing the tail first. -/
def attachLeaves (H : SimpleGraph α) (c : α) : List α → SimpleGraph α
  | [] => H
  | v :: vs => attachLeaves H c vs ⊔ edge c v

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
    (H : SimpleGraph α) (c : α) (L : List α) {v : α}
    (hcL : c ∉ L) (hv : v ∈ L) :
    (attachLeaves H c L).Adj c v := by
  induction L with
  | nil => simp at hv
  | cons w ws ih =>
      have hcw : c ≠ w := by
        intro h
        exact hcL (by simp [h])
      have hcws : c ∉ ws := by
        intro h
        exact hcL (by simp [h])
      simp only [List.mem_cons] at hv
      change (attachLeaves H c ws).Adj c v ∨ (edge c w).Adj c v
      rcases hv with rfl | hv
      · right
        simp [hcw]
      · exact Or.inl (ih hcws hv)

private noncomputable def leaves (T : SimpleGraph α) [DecidableRel T.Adj] : Finset α :=
  Finset.univ.filter fun v => T.degree v = 1

private noncomputable def internal (T : SimpleGraph α) [DecidableRel T.Adj] : Finset α :=
  Finset.univ.filter fun v => T.degree v ≠ 1

private lemma leaf_identity (T : SimpleGraph α) [DecidableRel T.Adj]
    (hT : T.IsTree) :
    ((leaves T).card : ℤ) = 2 +
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
#print axioms attachLeaves_isAcyclic
#print axioms two_degrees_sub_two_le_leaves

end WrittenOnTheWallII.GraphConjecture160Audit
