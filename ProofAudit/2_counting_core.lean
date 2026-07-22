/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import FormalConjecturesUtil

/-!
# WOWII Conjecture 2 counting core

Finite incidence double counts, Cauchy bounds, and the algebraic averaging
endgame used by the complete C2 proof.
-/

namespace WrittenOnTheWallII.GraphConjecture2Audit

open Classical Finset SimpleGraph

/-- Number of selected neighborhoods containing a fixed vertex. -/
def reverseCount {β : Type*} [Fintype β] [DecidableEq β]
    (I : β → Finset β) (u : β) : ℕ :=
  (Finset.univ.filter fun v => u ∈ I v).card

/-- Counting selected incidences by their first or second coordinate gives the
same total. -/
lemma sum_reverseCount_eq_sum_card
    {β : Type*} [Fintype β] [DecidableEq β]
    (I : β → Finset β) :
    (∑ u, reverseCount I u) = ∑ v, (I v).card := by
  classical
  calc
    (∑ u, reverseCount I u) =
        ∑ u, ∑ v, if u ∈ I v then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro u _hu
          rw [reverseCount, Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ v, ∑ u, if u ∈ I v then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ v, (I v).card := by
          apply Finset.sum_congr rfl
          intro v _hv
          calc
            (∑ u, if u ∈ I v then 1 else 0) =
                ∑ u ∈ I v, 1 := by
                  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
                    Finset.univ_inter]
            _ = (I v).card := by
                  rw [← Finset.card_eq_sum_ones]

/-- Real-valued form of the incidence double count. -/
lemma sum_reverseCount_cast_eq_sum_card_cast
    {β : Type*} [Fintype β] [DecidableEq β]
    (I : β → Finset β) :
    (∑ u, (reverseCount I u : ℝ)) = ∑ v, ((I v).card : ℝ) := by
  exact_mod_cast sum_reverseCount_eq_sum_card I

/-- The contribution depending only on the first coordinate of a selected
incidence is its value times the selected-set cardinality. -/
lemma sum_selected_constant_eq_sum_card_mul
    {β : Type*} [Fintype β] [DecidableEq β]
    (I : β → Finset β) (a : β → ℝ) :
    (∑ v, ∑ _u ∈ I v, a v) = ∑ v, ((I v).card : ℝ) * a v := by
  apply Finset.sum_congr rfl
  intro v _hv
  simp [nsmul_eq_mul]

/-- Reversing a weighted selected-incidence sum introduces `reverseCount`. -/
lemma sum_selected_weight_eq_sum_reverseCount_mul
    {β : Type*} [Fintype β] [DecidableEq β]
    (I : β → Finset β) (d : β → ℝ) :
    (∑ v, ∑ u ∈ I v, d u) =
      ∑ u, (reverseCount I u : ℝ) * d u := by
  classical
  calc
    (∑ v, ∑ u ∈ I v, d u) =
        ∑ v, ∑ u, if u ∈ I v then d u else 0 := by
          apply Finset.sum_congr rfl
          intro v _hv
          simp
    _ = ∑ u, ∑ v, if u ∈ I v then d u else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ u, (reverseCount I u : ℝ) * d u := by
          apply Finset.sum_congr rfl
          intro u _hu
          calc
            (∑ v, if u ∈ I v then d u else 0) =
                ∑ v ∈ (Finset.univ.filter fun v => u ∈ I v), d u := by
                  rw [Finset.sum_filter]
            _ = ((Finset.univ.filter fun v => u ∈ I v).card : ℝ) * d u := by
                  simp [nsmul_eq_mul]
            _ = (reverseCount I u : ℝ) * d u := by
                  rfl

/-- Sum a pointwise bound over all selected incidences. If `|I v| = a v` and
`a v + d u ≤ M` whenever `u ∈ I v`, then the first-coordinate square mass and
the reverse-incidence weighted mass are at most `M * Σ a`. -/
lemma selected_incidence_sum_bound
    {β : Type*} [Fintype β] [DecidableEq β]
    (I : β → Finset β) (a d : β → ℝ) (M : ℝ)
    (hcard : ∀ v, ((I v).card : ℝ) = a v)
    (hpoint : ∀ v u, u ∈ I v → a v + d u ≤ M) :
    (∑ v, (a v) ^ 2) +
        ∑ u, (reverseCount I u : ℝ) * d u ≤
      M * ∑ v, a v := by
  have hsum :
      (∑ v, ∑ u ∈ I v, (a v + d u)) ≤
        ∑ v, ∑ u ∈ I v, M := by
    apply Finset.sum_le_sum
    intro v _hv
    apply Finset.sum_le_sum
    intro u hu
    exact hpoint v u hu
  have hfirst :
      (∑ v, ∑ _u ∈ I v, a v) = ∑ v, (a v) ^ 2 := by
    rw [sum_selected_constant_eq_sum_card_mul]
    apply Finset.sum_congr rfl
    intro v _hv
    rw [hcard v]
    ring
  have hsecond :
      (∑ v, ∑ u ∈ I v, d u) =
        ∑ u, (reverseCount I u : ℝ) * d u :=
    sum_selected_weight_eq_sum_reverseCount_mul I d
  have hright :
      (∑ v, ∑ _u ∈ I v, M) = M * ∑ v, a v := by
    calc
      (∑ v, ∑ _u ∈ I v, M) =
          ∑ v, ((I v).card : ℝ) * M :=
        sum_selected_constant_eq_sum_card_mul I (fun _ => M)
      _ = ∑ v, a v * M := by
        apply Finset.sum_congr rfl
        intro v _hv
        rw [hcard v]
      _ = M * ∑ v, a v := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _hv
        ring
  calc
    (∑ v, (a v) ^ 2) +
        ∑ u, (reverseCount I u : ℝ) * d u =
      (∑ v, ∑ _u ∈ I v, a v) +
        ∑ v, ∑ u ∈ I v, d u := by
          rw [hfirst, hsecond]
    _ = ∑ v, ((∑ _u ∈ I v, a v) + ∑ u ∈ I v, d u) := by
          rw [← Finset.sum_add_distrib]
    _ = ∑ v, ∑ u ∈ I v, (a v + d u) := by
          apply Finset.sum_congr rfl
          intro v _hv
          rw [Finset.sum_add_distrib]
    _ ≤ ∑ v, ∑ u ∈ I v, M := hsum
    _ = M * ∑ v, a v := hright

/-- If every selected vertex at `v` is a neighbor of `v`, then the number of
selected neighborhoods containing `u` is at most the degree of `u`. -/
lemma reverseCount_le_degree
    {β : Type*} [Fintype β] [DecidableEq β]
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (I : β → Finset β)
    (hI : ∀ v, I v ⊆ G.neighborFinset v) (u : β) :
    reverseCount I u ≤ G.degree u := by
  classical
  change (Finset.univ.filter fun v => u ∈ I v).card ≤ (G.neighborFinset u).card
  apply Finset.card_le_card
  intro v hv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
  have hvu : G.Adj v u := by
    simpa using hI v hv
  simpa using hvu.symm

/-- The finite Cauchy inequality in exactly the form needed for both sides of
the selected-neighborhood incidence count. -/
lemma square_sum_le_card_mul_sum_square
    {β : Type*} [Fintype β] (f : β → ℝ) :
    (∑ i, f i) ^ 2 ≤ (Fintype.card β : ℝ) * ∑ i, (f i) ^ 2 := by
  simpa using
    (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset β)) (f := f))

/-- If `0 ≤ c ≤ d`, then the incidence contribution `c*d` dominates `c²`.
This is the pointwise inequality used after reversing the selected-neighborhood
incidence double count. -/
lemma sq_le_mul_of_nonneg_of_le
    (c d : ℝ) (hc : 0 ≤ c) (hcd : c ≤ d) :
    c ^ 2 ≤ c * d := by
  nlinarith [mul_nonneg hc (sub_nonneg.mpr hcd)]

/-- Summed form of `reverseCount_le_degree`. -/
lemma sum_reverseCount_square_le_mul_degree
    {β : Type*} [Fintype β] [DecidableEq β]
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (I : β → Finset β)
    (hI : ∀ v, I v ⊆ G.neighborFinset v) :
    (∑ u, (reverseCount I u : ℝ) ^ 2) ≤
      ∑ u, (reverseCount I u : ℝ) * (G.degree u : ℝ) := by
  apply Finset.sum_le_sum
  intro u _hu
  apply sq_le_mul_of_nonneg_of_le
  · positivity
  · exact_mod_cast reverseCount_le_degree G I hI u

/-- Algebraic endgame of the C2 double-counting argument.

`S` is the total selected local-independence mass, `n` is the number of
vertices, `A` and `C` are the two sums of squares, and `M` is the largest
neighborhood-union size over an edge. Two Cauchy bounds and the incidence
upper bound imply `2(S/n) ≤ M`. -/
lemma average_bound_core
    (n S A C M : ℝ)
    (hn : 0 < n) (hS : 0 < S)
    (hA : S ^ 2 ≤ n * A)
    (hC : S ^ 2 ≤ n * C)
    (hM : A + C ≤ M * S) :
    2 * (S / n) ≤ M := by
  calc
    2 * (S / n) = (2 * S) / n := by ring
    _ ≤ M := (div_le_iff₀ hn).2 (by
      have hsq : 2 * S ^ 2 ≤ n * (A + C) := by
        nlinarith
      have hupper : n * (A + C) ≤ n * (M * S) :=
        mul_le_mul_of_nonneg_left hM hn.le
      have hprod : S * (2 * S) ≤ S * (n * M) := by
        nlinarith
      have hcancel : 2 * S ≤ n * M := by
        by_contra h
        have hlt : n * M < 2 * S := lt_of_not_ge h
        have hmul : S * (n * M) < S * (2 * S) :=
          mul_lt_mul_of_pos_left hlt hS
        exact (not_lt_of_ge hprod) hmul
      nlinarith)

#print axioms sum_reverseCount_eq_sum_card
#print axioms sum_reverseCount_cast_eq_sum_card_cast
#print axioms sum_selected_constant_eq_sum_card_mul
#print axioms sum_selected_weight_eq_sum_reverseCount_mul
#print axioms selected_incidence_sum_bound
#print axioms reverseCount_le_degree
#print axioms square_sum_le_card_mul_sum_square
#print axioms sq_le_mul_of_nonneg_of_le
#print axioms sum_reverseCount_square_le_mul_degree
#print axioms average_bound_core

end WrittenOnTheWallII.GraphConjecture2Audit
