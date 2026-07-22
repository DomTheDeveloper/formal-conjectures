/-
Copyright (c) 2024 Shuhao Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuhao Song
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.HamiltonianNextTwo
import Mathlib.Combinatorics.SimpleGraph.Operations

/-!
The degree-counting core of the Bondy--Chvátal argument.  This is a focused
adaptation of Shuhao Song's unmerged Mathlib development at
`c83689ab8f1abfba1f646e65dc8b131fd256b73f`.
-/

namespace SimpleGraph

open Classical Walk Function

variable {V : Type*} [Fintype V]

/-- On a Hamiltonian cycle in any supergraph, a nonedge of `G` whose degree sum
is at least the order of the graph forces a suitable crossing dart. -/
theorem exists_crossing_dart_of_degree_sum
    {G H : SimpleGraph V} {u v : V} {q : H.Walk u u}
    (hq : q.IsHamiltonianCycle) (hV : Fintype.card V ≥ 3)
    (huv : G.degree u + G.degree v ≥ Fintype.card V)
    (hv : v = hq.next u) (not_adj : ¬G.Adj u v) :
    ∃ w w' d, G.Adj w v ∧ G.Adj w' u ∧ d ∈ q.darts ∧ d.fst = w' ∧ d.snd = w := by
  let X := (hq.next ·) '' {w | G.Adj u w} \ {u}
  let Y := {w | G.Adj v w} \ {hq.next v}
  have cardX : G.degree u - 1 ≤ X.toFinset.card := calc
    _ = (G.neighborFinset u).card - 1 := by simp
    _ = (Finset.univ.filter (G.Adj u)).card - 1 := by rw [neighborFinset_eq_filter]
    _ ≤ ((Finset.univ.filter (G.Adj u)).image (hq.next ·)).card - ({u} : Finset _).card := by
      simp [Finset.card_image_of_injective _ hq.next_inj]
    _ ≤ (((Finset.univ.filter (G.Adj u)).image (hq.next ·)) \ {u}).card := by
      apply Finset.le_card_sdiff
    _ = _ := by simp [X]
  have cardY : G.degree v - 1 ≤ Y.toFinset.card := calc
    _ = (G.neighborFinset v).card - 1 := by simp
    _ ≤ (Finset.univ.filter (G.Adj v)).card - ({hq.next v} : Finset _).card := by
      simp [neighborFinset_eq_filter]
    _ ≤ (Finset.univ.filter (G.Adj v) \ {hq.next v}).card := by
      apply Finset.le_card_sdiff
    _ = _ := by simp [Y]
  have card_union : (X ∪ Y).toFinset.card ≤ Fintype.card V - 3 := calc
    _ ≤ ({v, hq.next v, u}ᶜ : Finset V).card := by
      apply Finset.card_le_card
      rw [Finset.subset_compl_comm]
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton, Set.mem_setOf_eq, Set.toFinset_union,
        Set.toFinset_diff, Set.toFinset_image, Set.toFinset_setOf, Set.toFinset_singleton,
        Finset.compl_union, Finset.mem_inter, Finset.mem_compl, Finset.mem_sdiff, Finset.mem_image,
        Finset.mem_filter, Finset.mem_univ, true_and, not_and, Decidable.not_not,
        forall_exists_index, and_imp, X, Y] at hw ⊢
      apply And.intro
      · intro w' adj next
        rcases hw with hw | hw | hw
        · rw [hw, hv] at next
          rw [hq.next_inj next] at adj
          simp at adj
        · rw [hw] at next
          rw [hq.next_inj next] at adj
          exact False.elim (not_adj adj)
        · exact hw
      · intro adj
        rcases hw with hw | hw | hw
        · rw [hw] at adj
          simp at adj
        · exact hw
        · rw [hw] at adj
          exact False.elim (not_adj adj.symm)
    _ = _ := by
      suffices ({v, hq.next v, u} : Finset V).card = 3 by rw [Finset.card_compl, this]
      rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem]
      · simp
      · simpa [hv] using hq.next_next_ne
      · simpa [hv] using And.intro hq.next_ne.symm hq.next_ne
  have non_empty : (X ∩ Y).toFinset.card ≠ 0 := fun h => by
    suffices Fintype.card V - 2 ≤ Fintype.card V - 3 by omega
    calc
      _ ≤ (G.degree u + G.degree v) - 2 := Nat.sub_le_sub_right huv _
      _ ≤ (G.degree u - 1) + (G.degree v - 1) := by omega
      _ ≤ X.toFinset.card + Y.toFinset.card := add_le_add cardX cardY
      _ = (X ∪ Y).toFinset.card + (X ∩ Y).toFinset.card := by
        simpa [-Set.toFinset_card] using (Finset.card_union_add_card_inter _ _).symm
      _ ≤ Fintype.card V - 3 + 0 := add_le_add card_union (le_of_eq h)
      _ = Fintype.card V - 3 := by simp
  obtain ⟨w, hw⟩ := Finset.card_ne_zero.mp non_empty
  simp only [Set.mem_setOf_eq, Set.toFinset_inter, Set.toFinset_diff, Set.toFinset_image,
    Set.toFinset_setOf, Set.toFinset_singleton, Finset.mem_inter, Finset.mem_sdiff,
    Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    X, Y] at hw
  rcases hw with ⟨⟨⟨w', hw'₁, hw'₂⟩, -⟩, hw₂, -⟩
  obtain ⟨d, hd₁, hd₂⟩ := hq.self_next_in_darts w'
  rw [hw'₂] at hd₂
  exact ⟨w, w', d, hw₂.symm, hw'₁.symm, hd₁, hd₂⟩

#print axioms SimpleGraph.exists_crossing_dart_of_degree_sum

end SimpleGraph
