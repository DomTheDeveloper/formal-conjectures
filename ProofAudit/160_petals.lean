/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import FormalConjecturesUtil
import Mathlib.Combinatorics.SimpleGraph.Triangle.Basic

namespace WrittenOnTheWallII.GraphConjecture160Petals

open Classical SimpleGraph Finset

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (G : SimpleGraph α) [DecidableRel G.Adj]

/-- The triangles containing a fixed vertex. -/
def trianglesAt (v : α) : Finset (Finset α) :=
  (G.cliqueFinset 3).filter fun t => v ∈ t

/-- The two vertices of a triangle other than its distinguished vertex. -/
def petal (v : α) (t : Finset α) : Finset α := t.erase v

/-- The union of the petals of all triangles through `v`. -/
def trianglePetals (v : α) : Finset α :=
  (trianglesAt G v).biUnion (petal v)

lemma mem_trianglesAt {v : α} {t : Finset α} :
    t ∈ trianglesAt G v ↔ G.IsNClique 3 t ∧ v ∈ t := by
  simp [trianglesAt]

lemma card_petal_eq_two {v : α} {t : Finset α}
    (ht : t ∈ trianglesAt G v) : #(petal v t) = 2 := by
  obtain ⟨htc, hvt⟩ := (mem_trianglesAt G).mp ht
  rw [petal, card_erase_of_mem hvt, htc.card_eq]

private lemma four_cycle_of_two_triangles_sharing_edge
    {a b c d : α}
    (hab : a ≠ b) (hca : G.Adj c a) (had : G.Adj a d)
    (hdb : G.Adj d b) (hbc : G.Adj b c)
    (hcb : c ≠ b) (hcd : c ≠ d) (hadne : a ≠ d) :
    ∃ z : α, ∃ w : G.Walk z z, w.IsCycle ∧ w.length = 4 := by
  let p : G.Path b c :=
    ⟨.cons hdb.symm (.cons had.symm (.cons hca.symm .nil)), by
      simp [hab, hcb, hcd, hadne]⟩
  have he : s(c, b) ∉ (p : G.Walk b c).edges := by
    simp [p, hab, hcb, hcd, hadne]
  let w : G.Walk c c := .cons hbc.symm (p : G.Walk b c)
  refine ⟨c, w, ?_, by simp [w, p]⟩
  exact p.cons_isCycle hbc.symm he

/-- A graph with no four-cycle has edge-disjoint triangles. -/
lemma edgeDisjointTriangles_of_no_four_cycle
    (hC4 : ¬ ∃ z : α, ∃ w : G.Walk z z, w.IsCycle ∧ w.length = 4) :
    G.EdgeDisjointTriangles := by
  intro s hs t ht hst
  intro a ha b hb
  by_contra hab
  have haS : a ∈ s := ha.1
  have haT : a ∈ t := ha.2
  have hbS : b ∈ s := hb.1
  have hbT : b ∈ t := hb.2
  have hc : ∃ c ∈ s, c ∉ t := by
    by_contra h
    push_neg at h
    have hsub : s ⊆ t := h
    have heq : s = t := Finset.eq_of_subset_of_card_le hsub (by
      rw [hs.card_eq, ht.card_eq])
    exact hst heq
  have hd : ∃ d ∈ t, d ∉ s := by
    by_contra h
    push_neg at h
    have hsub : t ⊆ s := h
    have heq : t = s := Finset.eq_of_subset_of_card_le hsub (by
      rw [ht.card_eq, hs.card_eq])
    exact hst heq.symm
  obtain ⟨c, hcS, hcT⟩ := hc
  obtain ⟨d, hdT, hdS⟩ := hd
  have hca : G.Adj c a := hs.isClique hcS haS (by
    intro h; subst c; exact hcT haT)
  have had : G.Adj a d := ht.isClique haT hdT (by
    intro h; subst d; exact hdS haS)
  have hdb : G.Adj d b := ht.isClique hdT hbT (by
    intro h; subst d; exact hdS hbS)
  have hbc : G.Adj b c := hs.isClique hbS hcS (by
    intro h; subst c; exact hcT hbT)
  have hcb : c ≠ b := by
    intro h; subst c; exact hcT hbT
  have hcd : c ≠ d := by
    intro h; subst d; exact hcT hdT
  have hadne : a ≠ d := by
    intro h; subst d; exact hdS haS
  exact hC4 (four_cycle_of_two_triangles_sharing_edge G hab hca had hdb hbc hcb hcd hadne)

lemma pairwise_disjoint_petals {v : α} (hED : G.EdgeDisjointTriangles) :
    ∀ ⦃s⦄, s ∈ trianglesAt G v → ∀ ⦃t⦄, t ∈ trianglesAt G v → s ≠ t →
      Disjoint (petal v s) (petal v t) := by
  intro s hs t ht hst
  rw [Finset.disjoint_left]
  intro z hzs hzt
  obtain ⟨hsC, hvS⟩ := (mem_trianglesAt G).mp hs
  obtain ⟨htC, hvT⟩ := (mem_trianglesAt G).mp ht
  have hsub := hED hsC htC hst
  have hzS : z ∈ s := (mem_erase.mp hzs).2
  have hzT : z ∈ t := (mem_erase.mp hzt).2
  have hzv : z ≠ v := (mem_erase.mp hzs).1
  exact hzv (hsub ⟨hzS, hzT⟩ ⟨hvS, hvT⟩)

lemma card_trianglePetals {v : α} (hED : G.EdgeDisjointTriangles) :
    #(trianglePetals G v) = 2 * #(trianglesAt G v) := by
  unfold trianglePetals
  rw [card_biUnion]
  · calc
      (∑ t ∈ trianglesAt G v, #(petal v t)) =
          ∑ _t ∈ trianglesAt G v, 2 := by
            apply sum_congr rfl
            intro t ht
            exact card_petal_eq_two G ht
      _ = 2 * #(trianglesAt G v) := by simp [mul_comm]
  · intro s hs t ht hst
    exact pairwise_disjoint_petals G hED hs ht hst

lemma independent_inter_petal_card_le_one {v : α} {S t : Finset α}
    (hS : G.IsIndepSet (S : Set α)) (ht : t ∈ trianglesAt G v) :
    #(S ∩ petal v t) ≤ 1 := by
  rw [card_le_one]
  intro a ha b hb
  by_contra hab
  obtain ⟨htC, -⟩ := (mem_trianglesAt G).mp ht
  have haS : a ∈ S := mem_inter.mp ha |>.1
  have hbS : b ∈ S := mem_inter.mp hb |>.1
  have haT : a ∈ t := (mem_erase.mp (mem_inter.mp ha).2).2
  have hbT : b ∈ t := (mem_erase.mp (mem_inter.mp hb).2).2
  exact hS haS hbS hab (htC.isClique haT hbT hab)

lemma card_inter_trianglePetals_le {v : α} {S : Finset α}
    (hED : G.EdgeDisjointTriangles) (hS : G.IsIndepSet (S : Set α)) :
    #(S ∩ trianglePetals G v) ≤ #(trianglesAt G v) := by
  have hEq : S ∩ trianglePetals G v =
      (trianglesAt G v).biUnion (fun t => S ∩ petal v t) := by
    ext z
    simp [trianglePetals, and_assoc, and_left_comm, and_comm]
  rw [hEq, card_biUnion]
  · calc
      (∑ t ∈ trianglesAt G v, #(S ∩ petal v t)) ≤
          ∑ _t ∈ trianglesAt G v, 1 := by
            apply sum_le_sum
            intro t ht
            exact independent_inter_petal_card_le_one G hS ht
      _ = #(trianglesAt G v) := by simp
  · intro s hs t ht hst
    exact (pairwise_disjoint_petals G hED hs ht hst).mono
      inter_subset_right inter_subset_right

#print axioms edgeDisjointTriangles_of_no_four_cycle
#print axioms card_trianglePetals
#print axioms card_inter_trianglePetals_le

end WrittenOnTheWallII.GraphConjecture160Petals
