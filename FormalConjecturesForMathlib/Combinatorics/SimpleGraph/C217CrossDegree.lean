/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217ClosureHelpers
import Lean.Elab.Tactic.Omega

/-!
# Cross-degree accounting for WOWII Conjecture 217

The exceptional seed rows are closed by comparing the total original degree
available in a universal high-degree set with the degree demand outside it.
This file packages the required finite double counting.
-/

namespace SimpleGraph.C217CrossDegree

open Classical
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]

/-- Number of neighbors of `v` lying in `A`, written as an adjacency-indicator
sum so cross-edge symmetry is transparent. -/
def crossDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (v : V) : ℕ :=
  ∑ a ∈ A, if G.Adj v a then 1 else 0

/-- Cross degree is the cardinality of the filtered neighbor set. -/
lemma crossDegree_eq_card_filter
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (v : V) :
    crossDegree G A v = (A.filter fun a => G.Adj v a).card := by
  simp [crossDegree, Finset.card_eq_sum_ones]

/-- Cross degree is at most total degree. -/
lemma crossDegree_le_degree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (v : V) :
    crossDegree G A v ≤ G.degree v := by
  rw [crossDegree_eq_card_filter, ← card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro x hx
  simpa using (Finset.mem_filter.mp hx).2

/-- If every neighbor of `v` lies in `A`, cross degree equals total degree. -/
lemma crossDegree_eq_degree_of_neighborFinset_subset
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (v : V)
    (hsub : G.neighborFinset v ⊆ A) :
    crossDegree G A v = G.degree v := by
  rw [crossDegree_eq_card_filter, ← card_neighborFinset_eq_degree]
  congr
  ext x
  constructor
  · intro hx
    simpa using (Finset.mem_filter.mp hx).2
  · intro hx
    exact Finset.mem_filter.mpr ⟨hsub hx, by simpa using hx⟩

/-- Double-count the edges crossing from `A` to its complement. -/
theorem sum_crossDegree_compl
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) :
    (∑ v ∈ Finset.univ \ A, crossDegree G A v) =
      ∑ a ∈ A, crossDegree G (Finset.univ \ A) a := by
  simp only [crossDegree]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro v hv
  rw [G.adj_comm]

/-- If `A` is universal in the path closure, has cardinality `r`, and the
outside original degree demand exceeds the degree capacity inside `A`, then an
outside closure vertex must have degree at least `r+1`. -/
theorem exists_outside_seed_of_degree_sum_lt
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (r : ℕ)
    (hAcard : A.card = r)
    (huniv : ∀ a ∈ A, ∀ v, v ≠ a → (pathClosure G).Adj a v)
    (hsum : (∑ a ∈ A, G.degree a) <
      ∑ v ∈ Finset.univ \ A, G.degree v) :
    ∃ s ∉ A, r + 1 ≤ (pathClosure G).degree s := by
  let H := pathClosure G
  by_contra hseed
  push_neg at hseed
  have hneighbor : ∀ v ∈ Finset.univ \ A, G.neighborFinset v ⊆ A := by
    intro v hv
    have hvA : v ∉ A := by simpa using hv
    have hAsub : A ⊆ H.neighborFinset v := by
      intro a ha
      have hav : a ≠ v := by
        intro h
        subst a
        exact hvA ha
      simpa [H] using (huniv a ha v hav).symm
    have hHdeg : H.degree v ≤ r := by
      have hnot := hseed v hvA
      omega
    have hHeq : H.neighborFinset v = A := by
      apply Finset.eq_of_subset_of_card_le hAsub
      rw [card_neighborFinset_eq_degree, hAcard]
      exact hHdeg
    intro x hx
    have hxH : H.Adj v x := (self_le_pathClosure G) (by simpa using hx)
    have hxmem : x ∈ H.neighborFinset v := by simpa using hxH
    rw [hHeq] at hxmem
    exact hxmem
  have houtEq :
      (∑ v ∈ Finset.univ \ A, crossDegree G A v) =
        ∑ v ∈ Finset.univ \ A, G.degree v := by
    apply Finset.sum_congr rfl
    intro v hv
    exact crossDegree_eq_degree_of_neighborFinset_subset G A v (hneighbor v hv)
  have hinLe :
      (∑ a ∈ A, crossDegree G (Finset.univ \ A) a) ≤
        ∑ a ∈ A, G.degree a := by
    exact Finset.sum_le_sum fun a ha => crossDegree_le_degree G (Finset.univ \ A) a
  have hcross := sum_crossDegree_compl G A
  rw [houtEq] at hcross
  have : (∑ v ∈ Finset.univ \ A, G.degree v) ≤
      ∑ a ∈ A, G.degree a := by
    rw [hcross]
    exact hinLe
  omega

#print axioms SimpleGraph.C217CrossDegree.crossDegree_le_degree
#print axioms SimpleGraph.C217CrossDegree.sum_crossDegree_compl
#print axioms SimpleGraph.C217CrossDegree.exists_outside_seed_of_degree_sum_lt

end SimpleGraph.C217CrossDegree
