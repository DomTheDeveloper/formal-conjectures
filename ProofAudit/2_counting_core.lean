/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import FormalConjecturesUtil

namespace WrittenOnTheWallII.GraphConjecture2Audit

open Classical Finset

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
  simp [reverseCount, Finset.card_eq_sum_ones, Finset.sum_comm]

/-- Real-valued form of the incidence double count. -/
lemma sum_reverseCount_cast_eq_sum_card_cast
    {β : Type*} [Fintype β] [DecidableEq β]
    (I : β → Finset β) :
    (∑ u, (reverseCount I u : ℝ)) = ∑ v, ((I v).card : ℝ) := by
  exact_mod_cast sum_reverseCount_eq_sum_card I

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
      have hcancel : 2 * S ≤ n * M :=
        (mul_le_mul_left hS).mp hprod
      nlinarith)

#print axioms sum_reverseCount_eq_sum_card
#print axioms sum_reverseCount_cast_eq_sum_card_cast
#print axioms square_sum_le_card_mul_sum_square
#print axioms sq_le_mul_of_nonneg_of_le
#print axioms average_bound_core

end WrittenOnTheWallII.GraphConjecture2Audit
