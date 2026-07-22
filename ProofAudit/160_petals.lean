/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import FormalConjecturesUtil

namespace WrittenOnTheWallII.GraphConjecture160Petals

open Classical SimpleGraph Finset

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (G : SimpleGraph α) [DecidableRel G.Adj]

/-- Edges whose two endpoints lie in the neighborhood of `v`.  Its cardinality
is exactly the repository invariant `numTrianglesAtVertex G v`. -/
def triangleEdgesAt (v : α) : Finset (Sym2 α) :=
  G.edgeFinset.filter fun e => e.toFinset ⊆ G.neighborFinset v

/-- The union of all two-vertex petals opposite `v`. -/
def trianglePetals (v : α) : Finset α :=
  (triangleEdgesAt G v).biUnion Sym2.toFinset

lemma card_triangleEdgesAt (v : α) :
    #(triangleEdgesAt G v) = numTrianglesAtVertex G v := by
  rfl

lemma mem_triangleEdgesAt {v : α} {e : Sym2 α} :
    e ∈ triangleEdgesAt G v ↔
      e ∈ G.edgeFinset ∧ e.toFinset ⊆ G.neighborFinset v := by
  simp [triangleEdgesAt]

lemma card_edge_petal {v : α} {e : Sym2 α}
    (he : e ∈ triangleEdgesAt G v) : #e.toFinset = 2 := by
  have heG : e ∈ G.edgeFinset := (mem_triangleEdgesAt G).mp he |>.1
  exact G.card_toFinset_mem_edgeFinset ⟨e, heG⟩

private lemma four_cycle_of_cross
    {v z a b : α}
    (hva : G.Adj v a) (haz : G.Adj a z)
    (hzb : G.Adj z b) (hbv : G.Adj b v)
    (hav : a ≠ v) (hazne : a ≠ z) (hab : a ≠ b)
    (hzv : z ≠ v) (hzbne : z ≠ b) (hbvne : b ≠ v) :
    ∃ x : α, ∃ w : G.Walk x x, w.IsCycle ∧ w.length = 4 := by
  let p : G.Path a v :=
    ⟨.cons haz (.cons hzb (.cons hbv .nil)), by
      simp [hav, hazne, hab, hzv, hzbne, hbvne]⟩
  have he : s(v, a) ∉ (p : G.Walk a v).edges := by
    simp [p, hav, hazne, hab, hzv, hzbne, hbvne]
  let w : G.Walk v v := .cons hva (p : G.Walk a v)
  refine ⟨v, w, ?_, by simp [w, p]⟩
  exact p.cons_isCycle hva he

/-- Distinct triangle petals through the same vertex are disjoint in a graph
with no four-cycle. -/
lemma pairwise_disjoint_triangleEdges {v : α}
    (hC4 : ¬ ∃ x : α, ∃ w : G.Walk x x, w.IsCycle ∧ w.length = 4) :
    ∀ ⦃e⦄, e ∈ triangleEdgesAt G v →
      ∀ ⦃f⦄, f ∈ triangleEdgesAt G v → e ≠ f →
        Disjoint e.toFinset f.toFinset := by
  intro e he f hf hef
  induction e using Sym2.ind with
  | _ a b =>
      induction f using Sym2.ind with
      | _ c d =>
          rw [Finset.disjoint_left]
          intro z hzE hzF
          have hab : G.Adj a b := by
            have := (mem_triangleEdgesAt G).mp he |>.1
            simpa using this
          have hcd : G.Adj c d := by
            have := (mem_triangleEdgesAt G).mp hf |>.1
            simpa using this
          have hEa := (mem_triangleEdgesAt G).mp he |>.2 (by simp)
          have hEb := (mem_triangleEdgesAt G).mp he |>.2 (by simp)
          have hFc := (mem_triangleEdgesAt G).mp hf |>.2 (by simp)
          have hFd := (mem_triangleEdgesAt G).mp hf |>.2 (by simp)
          have hva : G.Adj v a := by simpa using hEa
          have hvb : G.Adj v b := by simpa using hEb
          have hvc : G.Adj v c := by simpa using hFc
          have hvd : G.Adj v d := by simpa using hFd
          simp only [Sym2.toFinset_mk, mem_insert, mem_singleton] at hzE hzF
          rcases hzE with rfl | rfl <;> rcases hzF with rfl | rfl
          · have hbd : b ≠ d := by
              intro h
              subst d
              exact hef rfl
            exact hC4 (four_cycle_of_cross G hvb hab.symm hcd hvd.symm
              hvb.ne hab.ne.symm hbd hva.ne hcd.ne hvd.ne)
          · have hbc : b ≠ c := by
              intro h
              subst c
              exact hef Sym2.eq_swap
            exact hC4 (four_cycle_of_cross G hvb hab.symm hcd.symm hvc.symm
              hvb.ne hab.ne.symm hbc hva.ne hcd.ne.symm hvc.ne)
          · have had : a ≠ d := by
              intro h
              subst d
              exact hef Sym2.eq_swap
            exact hC4 (four_cycle_of_cross G hva hab hcd hvd.symm
              hva.ne hab.ne had hvb.ne hcd.ne hvd.ne)
          · have hac : a ≠ c := by
              intro h
              subst c
              exact hef rfl
            exact hC4 (four_cycle_of_cross G hva hab hcd.symm hvc.symm
              hva.ne hab.ne hac hvb.ne hcd.ne.symm hvc.ne)

lemma card_trianglePetals {v : α}
    (hC4 : ¬ ∃ x : α, ∃ w : G.Walk x x, w.IsCycle ∧ w.length = 4) :
    #(trianglePetals G v) = 2 * numTrianglesAtVertex G v := by
  unfold trianglePetals
  rw [card_biUnion]
  · calc
      (∑ e ∈ triangleEdgesAt G v, #e.toFinset) =
          ∑ _e ∈ triangleEdgesAt G v, 2 := by
            apply sum_congr rfl
            intro e he
            exact card_edge_petal G he
      _ = 2 * #(triangleEdgesAt G v) := by simp [mul_comm]
      _ = 2 * numTrianglesAtVertex G v := by rw [card_triangleEdgesAt]
  · intro e he f hf hef
    exact pairwise_disjoint_triangleEdges G hC4 he hf hef

lemma independent_inter_edge_card_le_one {v : α} {S : Finset α} {e : Sym2 α}
    (hS : G.IsIndepSet (S : Set α)) (he : e ∈ triangleEdgesAt G v) :
    #(S ∩ e.toFinset) ≤ 1 := by
  induction e using Sym2.ind with
  | _ a b =>
      rw [card_le_one]
      intro x hx y hy
      have hab : G.Adj a b := by
        have := (mem_triangleEdgesAt G).mp he |>.1
        simpa using this
      have hxS : x ∈ S := (mem_inter.mp hx).1
      have hyS : y ∈ S := (mem_inter.mp hy).1
      simp only [Sym2.toFinset_mk, mem_insert, mem_singleton] at hx hy
      rcases hx.2 with rfl | rfl <;> rcases hy.2 with rfl | rfl
      · rfl
      · exact (hS hxS hyS hab.ne hab).elim
      · exact (hS hxS hyS hab.ne.symm hab.symm).elim
      · rfl

lemma card_inter_trianglePetals_le {v : α} {S : Finset α}
    (hC4 : ¬ ∃ x : α, ∃ w : G.Walk x x, w.IsCycle ∧ w.length = 4)
    (hS : G.IsIndepSet (S : Set α)) :
    #(S ∩ trianglePetals G v) ≤ numTrianglesAtVertex G v := by
  have hEq : S ∩ trianglePetals G v =
      (triangleEdgesAt G v).biUnion (fun e => S ∩ e.toFinset) := by
    ext z
    simp [trianglePetals, and_assoc, and_left_comm, and_comm]
  rw [hEq, card_biUnion]
  · calc
      (∑ e ∈ triangleEdgesAt G v, #(S ∩ e.toFinset)) ≤
          ∑ _e ∈ triangleEdgesAt G v, 1 := by
            apply sum_le_sum
            intro e he
            exact independent_inter_edge_card_le_one G hS he
      _ = #(triangleEdgesAt G v) := by simp
      _ = numTrianglesAtVertex G v := card_triangleEdgesAt G v
  · intro e he f hf hef
    exact (pairwise_disjoint_triangleEdges G hC4 he hf hef).mono
      inter_subset_right inter_subset_right

#print axioms pairwise_disjoint_triangleEdges
#print axioms card_trianglePetals
#print axioms card_inter_trianglePetals_le

end WrittenOnTheWallII.GraphConjecture160Petals
