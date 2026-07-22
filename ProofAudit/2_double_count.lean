/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import ProofAudit.«2_counting_core»
import ProofAudit.«2_local_choice»

namespace WrittenOnTheWallII.GraphConjecture2Audit

open Classical Finset SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Summing the pointwise neighborhood-union bound over all selected
incidences gives the two quadratic terms used in the C2 argument. -/
lemma selected_incidence_sum_le
    (G : SimpleGraph α) [DecidableRel G.Adj] (M : ℝ)
    (hM : ∀ v u, u ∈ chosenLocalIndep G v →
      ((G.neighborFinset v ∪ G.neighborFinset u).card : ℝ) ≤ M) :
    (∑ v, (indepNeighborsCard G v : ℝ) ^ 2) +
        ∑ u, (reverseCount (chosenLocalIndep G) u : ℝ) * (G.degree u : ℝ) ≤
      M * ∑ v, (indepNeighborsCard G v : ℝ) := by
  classical
  have hsum :
      (∑ v, ∑ u ∈ chosenLocalIndep G v,
          ((indepNeighborsCard G v : ℝ) + (G.degree u : ℝ))) ≤
        ∑ v, ∑ u ∈ chosenLocalIndep G v, M := by
    apply Finset.sum_le_sum
    intro v _hv
    apply Finset.sum_le_sum
    intro u hu
    have hnat := indepNeighbors_add_degree_le_neighbor_union G hu
    have hcast :
        (indepNeighborsCard G v : ℝ) + (G.degree u : ℝ) ≤
          ((G.neighborFinset v ∪ G.neighborFinset u).card : ℝ) := by
      exact_mod_cast hnat
    exact hcast.trans (hM v u hu)
  have hsplit :
      (∑ v, ∑ u ∈ chosenLocalIndep G v,
          ((indepNeighborsCard G v : ℝ) + (G.degree u : ℝ))) =
        (∑ v, ∑ _u ∈ chosenLocalIndep G v,
          (indepNeighborsCard G v : ℝ)) +
        (∑ v, ∑ u ∈ chosenLocalIndep G v, (G.degree u : ℝ)) := by
    calc
      _ = ∑ v,
          ((∑ _u ∈ chosenLocalIndep G v, (indepNeighborsCard G v : ℝ)) +
           (∑ u ∈ chosenLocalIndep G v, (G.degree u : ℝ))) := by
            apply Finset.sum_congr rfl
            intro v _hv
            exact Finset.sum_add_distrib
      _ = _ := Finset.sum_add_distrib
  have hfirst :
      (∑ v, ∑ _u ∈ chosenLocalIndep G v,
          (indepNeighborsCard G v : ℝ)) =
        ∑ v, (indepNeighborsCard G v : ℝ) ^ 2 := by
    rw [sum_selected_constant_eq_sum_card_mul]
    apply Finset.sum_congr rfl
    intro v _hv
    rw [chosenLocalIndep_card]
    ring
  have hsecond :
      (∑ v, ∑ u ∈ chosenLocalIndep G v, (G.degree u : ℝ)) =
        ∑ u, (reverseCount (chosenLocalIndep G) u : ℝ) * (G.degree u : ℝ) :=
    sum_selected_weight_eq_sum_reverseCount_mul
      (chosenLocalIndep G) (fun u => (G.degree u : ℝ))
  have hleft :
      (∑ v, ∑ u ∈ chosenLocalIndep G v,
          ((indepNeighborsCard G v : ℝ) + (G.degree u : ℝ))) =
        (∑ v, (indepNeighborsCard G v : ℝ) ^ 2) +
          ∑ u, (reverseCount (chosenLocalIndep G) u : ℝ) * (G.degree u : ℝ) := by
    rw [hsplit, hfirst, hsecond]
  have hright :
      (∑ v, ∑ _u ∈ chosenLocalIndep G v, M) =
        M * ∑ v, (indepNeighborsCard G v : ℝ) := by
    rw [sum_selected_constant_eq_sum_card_mul]
    calc
      (∑ v, ((chosenLocalIndep G v).card : ℝ) * M) =
          ∑ v, (indepNeighborsCard G v : ℝ) * M := by
            apply Finset.sum_congr rfl
            intro v _hv
            rw [chosenLocalIndep_card]
      _ = (∑ v, (indepNeighborsCard G v : ℝ)) * M := by
            rw [Finset.sum_mul]
      _ = M * ∑ v, (indepNeighborsCard G v : ℝ) := by ring
  rw [hleft, hright] at hsum
  exact hsum

/-- The complete double-counting/Cauchy half of WOWII Conjecture 2, stated
against any common upper bound `M` for the selected edge-neighborhood unions. -/
lemma two_mul_averageIndepNeighbors_le_of_selected_union_bound
    [Nontrivial α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (M : ℝ)
    (hS : 0 < ∑ v, (indepNeighborsCard G v : ℝ))
    (hM : ∀ v u, u ∈ chosenLocalIndep G v →
      ((G.neighborFinset v ∪ G.neighborFinset u).card : ℝ) ≤ M) :
    2 * averageIndepNeighbors G ≤ M := by
  classical
  have hsumEq :
      (∑ u, (reverseCount (chosenLocalIndep G) u : ℝ)) =
        ∑ v, (indepNeighborsCard G v : ℝ) := by
    calc
      _ = ∑ v, ((chosenLocalIndep G v).card : ℝ) :=
        sum_reverseCount_cast_eq_sum_card_cast (chosenLocalIndep G)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro v _hv
        rw [chosenLocalIndep_card]
  have hA := square_sum_le_card_mul_sum_square
    (fun v => (indepNeighborsCard G v : ℝ))
  have hC := square_sum_le_card_mul_sum_square
    (fun u => (reverseCount (chosenLocalIndep G) u : ℝ))
  rw [hsumEq] at hC
  have hCD := sum_reverseCount_square_le_mul_degree
    G (chosenLocalIndep G) (chosenLocalIndep_subset_neighborFinset G)
  have hAD := selected_incidence_sum_le G M hM
  have hAC :
      (∑ v, (indepNeighborsCard G v : ℝ) ^ 2) +
          ∑ u, (reverseCount (chosenLocalIndep G) u : ℝ) ^ 2 ≤
        M * ∑ v, (indepNeighborsCard G v : ℝ) := by
    linarith
  have hfinal := average_bound_core
    (Fintype.card α : ℝ)
    (∑ v, (indepNeighborsCard G v : ℝ))
    (∑ v, (indepNeighborsCard G v : ℝ) ^ 2)
    (∑ u, (reverseCount (chosenLocalIndep G) u : ℝ) ^ 2)
    M (by positivity) hS hA hC hAC
  simpa [averageIndepNeighbors, indepNeighbors] using hfinal

#print axioms selected_incidence_sum_le
#print axioms two_mul_averageIndepNeighbors_le_of_selected_union_bound

end WrittenOnTheWallII.GraphConjecture2Audit
