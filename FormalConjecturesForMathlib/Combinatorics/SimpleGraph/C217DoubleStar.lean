/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217LeafWitness
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# The double-star tree used in the `K_{4,6}` obstruction
-/

namespace SimpleGraph.C217DoubleStar

open Classical
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Join `a` to every vertex of `B`, and `b` to every vertex of `A`. -/
def doubleStar (A B : Finset V) (a b : V) : SimpleGraph V :=
  SimpleGraph.fromRel fun x y =>
    (x = a ∧ y ∈ B) ∨ (x = b ∧ y ∈ A)

instance (A B : Finset V) (a b : V) :
    DecidableRel (doubleStar A B a b).Adj := inferInstance

@[simp] theorem doubleStar_adj
    (A B : Finset V) (a b x y : V) :
    (doubleStar A B a b).Adj x y ↔
      x ≠ y ∧
        ((x = a ∧ y ∈ B) ∨ (x = b ∧ y ∈ A) ∨
         (y = a ∧ x ∈ B) ∨ (y = b ∧ x ∈ A)) := by
  simp [doubleStar, SimpleGraph.fromRel_adj, or_assoc]

private lemma centers_ne {A B : Finset V} {a b : V}
    (hdisj : Disjoint A B) (ha : a ∈ A) (hb : b ∈ B) : a ≠ b := by
  intro h
  subst b
  exact Finset.disjoint_left.mp hdisj a ha hb

lemma neighborFinset_left_center
    {A B : Finset V} {a b : V}
    (hdisj : Disjoint A B) (ha : a ∈ A) (hb : b ∈ B) :
    (doubleStar A B a b).neighborFinset a = B := by
  have hab := centers_ne hdisj ha hb
  ext x
  constructor
  · intro hx
    have hadj : (doubleStar A B a b).Adj a x := by simpa using hx
    rw [doubleStar_adj] at hadj
    rcases hadj.2 with h | h | h | h
    · exact h.2
    · exact (hab h.1).elim
    · exact (hadj.1 h.1.symm).elim
    · simpa [h.1] using hb
  · intro hx
    have hax : a ≠ x := by
      intro h
      subst x
      exact Finset.disjoint_left.mp hdisj a ha hx
    have hadj : (doubleStar A B a b).Adj a x := by
      rw [doubleStar_adj]
      exact ⟨hax, Or.inl ⟨rfl, hx⟩⟩
    simpa using hadj

lemma neighborFinset_right_center
    {A B : Finset V} {a b : V}
    (hdisj : Disjoint A B) (ha : a ∈ A) (hb : b ∈ B) :
    (doubleStar A B a b).neighborFinset b = A := by
  have hab := centers_ne hdisj ha hb
  ext x
  constructor
  · intro hx
    have hadj : (doubleStar A B a b).Adj b x := by simpa using hx
    rw [doubleStar_adj] at hadj
    rcases hadj.2 with h | h | h | h
    · exact (hab.symm h.1).elim
    · exact h.2
    · simpa [h.1] using ha
    · exact (hadj.1 h.1.symm).elim
  · intro hx
    have hbx : b ≠ x := by
      intro h
      subst x
      exact Finset.disjoint_left.mp hdisj b hx hb
    have hadj : (doubleStar A B a b).Adj b x := by
      rw [doubleStar_adj]
      exact ⟨hbx, Or.inr (Or.inl ⟨rfl, hx⟩)⟩
    simpa using hadj

lemma neighborFinset_left_leaf
    {A B : Finset V} {a b x : V}
    (hdisj : Disjoint A B) (hxA : x ∈ A) (hxa : x ≠ a)
    (hb : b ∈ B) :
    (doubleStar A B a b).neighborFinset x = {b} := by
  have hxB : x ∉ B := fun hxB => Finset.disjoint_left.mp hdisj x hxA hxB
  have hxb : x ≠ b := by
    intro h
    subst b
    exact hxB hb
  ext y
  constructor
  · intro hy
    have hadj : (doubleStar A B a b).Adj x y := by simpa using hy
    rw [doubleStar_adj] at hadj
    rcases hadj.2 with h | h | h | h
    · exact (hxa h.1).elim
    · exact (hxb h.1).elim
    · exact (hxB h.2).elim
    · simpa using h.1
  · intro hy
    have hyb : y = b := by simpa using hy
    subst y
    have hadj : (doubleStar A B a b).Adj x b := by
      rw [doubleStar_adj]
      exact ⟨hxb, Or.inr (Or.inr (Or.inr ⟨rfl, hxA⟩))⟩
    simpa using hadj

lemma neighborFinset_right_leaf
    {A B : Finset V} {a b x : V}
    (hdisj : Disjoint A B) (ha : a ∈ A)
    (hxB : x ∈ B) (hxb : x ≠ b) :
    (doubleStar A B a b).neighborFinset x = {a} := by
  have hxA : x ∉ A := fun hxA => Finset.disjoint_left.mp hdisj x hxA hxB
  have hxa : x ≠ a := by
    intro h
    subst a
    exact hxA ha
  ext y
  constructor
  · intro hy
    have hadj : (doubleStar A B a b).Adj x y := by simpa using hy
    rw [doubleStar_adj] at hadj
    rcases hadj.2 with h | h | h | h
    · exact (hxa h.1).elim
    · exact (hxb h.1).elim
    · simpa using h.1
    · exact (hxA h.2).elim
  · intro hy
    have hya : y = a := by simpa using hy
    subst y
    have hadj : (doubleStar A B a b).Adj x a := by
      rw [doubleStar_adj]
      exact ⟨hxa, Or.inr (Or.inr (Or.inl ⟨rfl, hxB⟩))⟩
    simpa using hadj

lemma degree_left_center
    {A B : Finset V} {a b : V}
    (hdisj : Disjoint A B) (ha : a ∈ A) (hb : b ∈ B) :
    (doubleStar A B a b).degree a = B.card := by
  rw [← card_neighborFinset_eq_degree,
    neighborFinset_left_center hdisj ha hb]

lemma degree_right_center
    {A B : Finset V} {a b : V}
    (hdisj : Disjoint A B) (ha : a ∈ A) (hb : b ∈ B) :
    (doubleStar A B a b).degree b = A.card := by
  rw [← card_neighborFinset_eq_degree,
    neighborFinset_right_center hdisj ha hb]

lemma degree_left_leaf
    {A B : Finset V} {a b x : V}
    (hdisj : Disjoint A B) (hxA : x ∈ A) (hxa : x ≠ a)
    (hb : b ∈ B) :
    (doubleStar A B a b).degree x = 1 := by
  rw [← card_neighborFinset_eq_degree,
    neighborFinset_left_leaf hdisj hxA hxa hb]
  simp

lemma degree_right_leaf
    {A B : Finset V} {a b x : V}
    (hdisj : Disjoint A B) (ha : a ∈ A)
    (hxB : x ∈ B) (hxb : x ≠ b) :
    (doubleStar A B a b).degree x = 1 := by
  rw [← card_neighborFinset_eq_degree,
    neighborFinset_right_leaf hdisj ha hxB hxb]
  simp

/-- The double star is connected whenever `A,B` partition the vertex set. -/
theorem connected_doubleStar
    {A B : Finset V} {a b : V}
    (hpart : A ∪ B = Finset.univ)
    (hdisj : Disjoint A B) (ha : a ∈ A) (hb : b ∈ B) :
    (doubleStar A B a b).Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨a, ?_⟩
  intro x
  by_cases hxa : x = a
  · subst x
    exact .rfl
  have hxpart : x ∈ A ∪ B := by
    rw [hpart]
    simp
  rw [Finset.mem_union] at hxpart
  rcases hxpart with hxA | hxB
  · have hab : (doubleStar A B a b).Adj a b := by
      rw [doubleStar_adj]
      exact ⟨centers_ne hdisj ha hb, Or.inl ⟨rfl, hb⟩⟩
    have hbx : (doubleStar A B a b).Adj b x := by
      rw [doubleStar_adj]
      have hbxne : b ≠ x := by
        intro h
        subst x
        exact Finset.disjoint_left.mp hdisj b hxA hb
      exact ⟨hbxne, Or.inr (Or.inl ⟨rfl, hxA⟩)⟩
    exact hab.reachable.trans hbx.reachable
  · have hax : (doubleStar A B a b).Adj a x := by
      rw [doubleStar_adj]
      exact ⟨hxa.symm, Or.inl ⟨rfl, hxB⟩⟩
    exact hax.reachable

/-- The double star is a tree. -/
theorem isTree_doubleStar
    {A B : Finset V} {a b : V}
    (hpart : A ∪ B = Finset.univ)
    (hdisj : Disjoint A B) (ha : a ∈ A) (hb : b ∈ B) :
    (doubleStar A B a b).IsTree := by
  let T := doubleStar A B a b
  have hsumAerase :
      (∑ x ∈ A.erase a, T.degree x) = (A.erase a).card := by
    calc
      (∑ x ∈ A.erase a, T.degree x) = ∑ _x ∈ A.erase a, 1 := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxe := Finset.mem_erase.mp hx
        rw [degree_left_leaf hdisj hxe.2 hxe.1 hb]
      _ = (A.erase a).card := by simp
  have hsumBerase :
      (∑ x ∈ B.erase b, T.degree x) = (B.erase b).card := by
    calc
      (∑ x ∈ B.erase b, T.degree x) = ∑ _x ∈ B.erase b, 1 := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxe := Finset.mem_erase.mp hx
        rw [degree_right_leaf hdisj ha hxe.2 hxe.1]
      _ = (B.erase b).card := by simp
  have hsumA : (∑ x ∈ A, T.degree x) = B.card + (A.card - 1) := by
    rw [← Finset.sum_erase_add _ _ ha,
      degree_left_center hdisj ha hb, hsumAerase,
      Finset.card_erase_of_mem ha]
    omega
  have hsumB : (∑ x ∈ B, T.degree x) = A.card + (B.card - 1) := by
    rw [← Finset.sum_erase_add _ _ hb,
      degree_right_center hdisj ha hb, hsumBerase,
      Finset.card_erase_of_mem hb]
    omega
  have hsum : (∑ x, T.degree x) = 2 * (Fintype.card V - 1) := by
    rw [← Finset.sum_univ, ← hpart, Finset.sum_union hdisj, hsumA, hsumB]
    have hcard : Fintype.card V = A.card + B.card := by
      rw [← Finset.card_univ, ← hpart,
        Finset.card_union_of_disjoint hdisj]
    omega
  rw [isTree_iff_connected_and_card]
  refine ⟨connected_doubleStar hpart hdisj ha hb, ?_⟩
  rw [← edgeFinset_card]
  have hhand := T.sum_degrees_eq_twice_card_edges
  rw [hsum] at hhand
  have hcardpos : 0 < Fintype.card V := Fintype.card_pos
  have hedge : T.edgeFinset.card = Fintype.card V - 1 := by omega
  rw [Nat.card_eq_fintype_card, hedge]
  omega

/-- All noncenter vertices are leaves of the double star. -/
theorem noncenter_leaf_count_le
    {A B : Finset V} {a b : V}
    (hpart : A ∪ B = Finset.univ)
    (hdisj : Disjoint A B) (ha : a ∈ A) (hb : b ∈ B) :
    (A.card - 1) + (B.card - 1) ≤
      (doubleStar A B a b).toSubgraph.leafCount := by
  let T := doubleStar A B a b
  let L := (A.erase a) ∪ (B.erase b)
  have hdisjL : Disjoint (A.erase a) (B.erase b) :=
    hdisj.mono (Finset.erase_subset a A) (Finset.erase_subset b B)
  have hLcard : L.card = (A.card - 1) + (B.card - 1) := by
    rw [L, Finset.card_union_of_disjoint hdisjL,
      Finset.card_erase_of_mem ha, Finset.card_erase_of_mem hb]
  have hsub : L ⊆
      (T.toSubgraph.verts.toFinset.filter fun v => T.toSubgraph.degree v = 1) := by
    intro x hx
    rw [L, Finset.mem_union] at hx
    simp only [Finset.mem_filter]
    constructor
    · simp
    · rcases hx with hxA | hxB
      · have hxe := Finset.mem_erase.mp hxA
        simpa [T] using degree_left_leaf hdisj hxe.2 hxe.1 hb
      · have hxe := Finset.mem_erase.mp hxB
        simpa [T] using degree_right_leaf hdisj ha hxe.2 hxe.1
  rw [Subgraph.leafCount, ← hLcard]
  exact Finset.card_le_card hsub

#print axioms SimpleGraph.C217DoubleStar.isTree_doubleStar
#print axioms SimpleGraph.C217DoubleStar.noncenter_leaf_count_le

end SimpleGraph.C217DoubleStar
