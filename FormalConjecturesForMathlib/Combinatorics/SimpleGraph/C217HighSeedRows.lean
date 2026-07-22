/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217MultiSeed
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217RowFacts

/-!
# Uniform high-degree closure rows for WOWII Conjecture 217
-/

namespace SimpleGraph.C217HighSeedRows

open Classical
open SimpleGraph
open SimpleGraph.C217OrderBound
open SimpleGraph.C217RowFacts
open SimpleGraph.C217ClosureHelpers
open SimpleGraph.C217MultiSeed

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]

private lemma sum_degreeClass
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) :
    (∑ v ∈ degreeClass G d, G.degree v) = d * (degreeClass G d).card := by
  calc
    (∑ v ∈ degreeClass G d, G.degree v) = ∑ _v ∈ degreeClass G d, d := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [(mem_degreeClass G d v).mp hv]
    _ = d * (degreeClass G d).card := by simp [mul_comm]

/-- Generic uniform-outside high-degree pattern. -/
theorem isTraceable_high_seed_pattern
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (r m : ℕ)
    (hn : Fintype.card V = 2 * r + 2)
    (hAmin : ∀ a ∈ A, r + 1 ≤ G.degree a)
    (hBdeg : ∀ v ∉ A, G.degree v = r)
    (hm : m ≤ (Finset.univ \ A).card)
    (hcount : r + 1 ≤ A.card + m)
    (hcapacity : (∑ a ∈ A, G.degree a) <
      A.card * ((Finset.univ \ A).card - (m - 1))) :
    IsTraceable G := by
  have huniv : ∀ a ∈ A, ∀ v, v ≠ a → (pathClosure G).Adj a v := by
    intro a ha v hav
    apply pathClosure_adj_of_degree_sum G hav
    by_cases hvA : v ∈ A
    · have haD := hAmin a ha
      have hvD := hAmin v hvA
      rw [hn]
      omega
    · have haD := hAmin a ha
      have hvD := hBdeg v hvA
      rw [hn]
      omega
  exact isTraceable_of_seed_capacity G A r m hn huniv hBdeg hm hcount hcapacity

/-- Row 23: `[5,5,4^8]`. -/
theorem row_5544444444
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hrow : degreeSequence G = [5,5,4,4,4,4,4,4,4,4]) :
    IsTraceable G := by
  let A := degreeClass G 5
  have hn : Fintype.card V = 10 := by
    have h := card_eq_length_of_degreeSequence_eq G hrow
    norm_num at h
    exact h
  have hAcard : A.card = 2 := by
    have h := card_degreeClass_of_degreeSequence_eq G hrow 5
    norm_num at h
    simpa [A] using h
  have hcases : ∀ v, G.degree v = 5 ∨ G.degree v = 4 := by
    intro v
    have h := degree_mem_degreeSequence G v
    rw [hrow] at h
    simpa using h
  have hAmin : ∀ a ∈ A, 5 ≤ G.degree a := by
    intro a ha
    have : G.degree a = 5 := by simpa [A] using ha
    omega
  have hBdeg : ∀ v ∉ A, G.degree v = 4 := by
    intro v hv
    rcases hcases v with h5 | h4
    · exact (hv (by simpa [A, h5])).elim
    · exact h4
  have hsum : (∑ a ∈ A, G.degree a) = 10 := by
    rw [show (∑ a ∈ A, G.degree a) = 5 * A.card by simpa [A] using sum_degreeClass G 5,
      hAcard]
  have hBcard : (Finset.univ \ A).card = 8 := by
    rw [Finset.card_sdiff (Finset.subset_univ A), Finset.card_univ, hn, hAcard]
  apply isTraceable_high_seed_pattern G A 4 3
  · omega
  · exact hAmin
  · exact hBdeg
  · omega
  · omega
  · rw [hsum, hAcard, hBcard]
    norm_num

/-- Row 24: `[6,5,5,4^7]`. -/
theorem row_6554444444
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hrow : degreeSequence G = [6,5,5,4,4,4,4,4,4,4]) :
    IsTraceable G := by
  let A6 := degreeClass G 6
  let A5 := degreeClass G 5
  let A := A6 ∪ A5
  have hn : Fintype.card V = 10 := by
    have h := card_eq_length_of_degreeSequence_eq G hrow
    norm_num at h
    exact h
  have h6card : A6.card = 1 := by
    have h := card_degreeClass_of_degreeSequence_eq G hrow 6
    norm_num at h
    simpa [A6] using h
  have h5card : A5.card = 2 := by
    have h := card_degreeClass_of_degreeSequence_eq G hrow 5
    norm_num at h
    simpa [A5] using h
  have hdisj : Disjoint A6 A5 := by
    rw [Finset.disjoint_left]
    intro x hx6 hx5
    have h6 : G.degree x = 6 := by simpa [A6] using hx6
    have h5 : G.degree x = 5 := by simpa [A5] using hx5
    omega
  have hAcard : A.card = 3 := by
    rw [A, Finset.card_union_of_disjoint hdisj, h6card, h5card]
  have hcases : ∀ v, G.degree v = 6 ∨ G.degree v = 5 ∨ G.degree v = 4 := by
    intro v
    have h := degree_mem_degreeSequence G v
    rw [hrow] at h
    simpa using h
  have hAmin : ∀ a ∈ A, 5 ≤ G.degree a := by
    intro a ha
    rw [A, Finset.mem_union] at ha
    rcases ha with ha6 | ha5
    · have : G.degree a = 6 := by simpa [A6] using ha6
      omega
    · have : G.degree a = 5 := by simpa [A5] using ha5
      omega
  have hBdeg : ∀ v ∉ A, G.degree v = 4 := by
    intro v hv
    rcases hcases v with h6 | h5 | h4
    · exact (hv (by simp [A, A6, h6])).elim
    · exact (hv (by simp [A, A5, h5])).elim
    · exact h4
  have hsum6 : (∑ a ∈ A6, G.degree a) = 6 := by
    rw [show (∑ a ∈ A6, G.degree a) = 6 * A6.card by simpa [A6] using sum_degreeClass G 6,
      h6card]
  have hsum5 : (∑ a ∈ A5, G.degree a) = 10 := by
    rw [show (∑ a ∈ A5, G.degree a) = 5 * A5.card by simpa [A5] using sum_degreeClass G 5,
      h5card]
  have hsum : (∑ a ∈ A, G.degree a) = 16 := by
    rw [A, Finset.sum_union hdisj, hsum6, hsum5]
  have hBcard : (Finset.univ \ A).card = 7 := by
    rw [Finset.card_sdiff (Finset.subset_univ A), Finset.card_univ, hn, hAcard]
  apply isTraceable_high_seed_pattern G A 4 2
  · omega
  · exact hAmin
  · exact hBdeg
  · omega
  · omega
  · rw [hsum, hAcard, hBcard]
    norm_num

/-- Row 25: `[5^4,4^6]`. -/
theorem row_5555444444
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hrow : degreeSequence G = [5,5,5,5,4,4,4,4,4,4]) :
    IsTraceable G := by
  let A := degreeClass G 5
  have hn : Fintype.card V = 10 := by
    have h := card_eq_length_of_degreeSequence_eq G hrow
    norm_num at h
    exact h
  have hAcard : A.card = 4 := by
    have h := card_degreeClass_of_degreeSequence_eq G hrow 5
    norm_num at h
    simpa [A] using h
  have hcases : ∀ v, G.degree v = 5 ∨ G.degree v = 4 := by
    intro v
    have h := degree_mem_degreeSequence G v
    rw [hrow] at h
    simpa using h
  have hAmin : ∀ a ∈ A, 5 ≤ G.degree a := by
    intro a ha
    have : G.degree a = 5 := by simpa [A] using ha
    omega
  have hBdeg : ∀ v ∉ A, G.degree v = 4 := by
    intro v hv
    rcases hcases v with h5 | h4
    · exact (hv (by simpa [A, h5])).elim
    · exact h4
  have hsum : (∑ a ∈ A, G.degree a) = 20 := by
    rw [show (∑ a ∈ A, G.degree a) = 5 * A.card by simpa [A] using sum_degreeClass G 5,
      hAcard]
  have hBcard : (Finset.univ \ A).card = 6 := by
    rw [Finset.card_sdiff (Finset.subset_univ A), Finset.card_univ, hn, hAcard]
  apply isTraceable_high_seed_pattern G A 4 1
  · omega
  · exact hAmin
  · exact hBdeg
  · omega
  · omega
  · rw [hsum, hAcard, hBcard]
    norm_num

/-- Row 26: `[6,6,5,5,4^6]`. -/
theorem row_6655444444
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hrow : degreeSequence G = [6,6,5,5,4,4,4,4,4,4]) :
    IsTraceable G := by
  let A6 := degreeClass G 6
  let A5 := degreeClass G 5
  let A := A6 ∪ A5
  have hn : Fintype.card V = 10 := by
    have h := card_eq_length_of_degreeSequence_eq G hrow
    norm_num at h
    exact h
  have h6card : A6.card = 2 := by
    have h := card_degreeClass_of_degreeSequence_eq G hrow 6
    norm_num at h
    simpa [A6] using h
  have h5card : A5.card = 2 := by
    have h := card_degreeClass_of_degreeSequence_eq G hrow 5
    norm_num at h
    simpa [A5] using h
  have hdisj : Disjoint A6 A5 := by
    rw [Finset.disjoint_left]
    intro x hx6 hx5
    have h6 : G.degree x = 6 := by simpa [A6] using hx6
    have h5 : G.degree x = 5 := by simpa [A5] using hx5
    omega
  have hAcard : A.card = 4 := by
    rw [A, Finset.card_union_of_disjoint hdisj, h6card, h5card]
  have hcases : ∀ v, G.degree v = 6 ∨ G.degree v = 5 ∨ G.degree v = 4 := by
    intro v
    have h := degree_mem_degreeSequence G v
    rw [hrow] at h
    simpa using h
  have hAmin : ∀ a ∈ A, 5 ≤ G.degree a := by
    intro a ha
    rw [A, Finset.mem_union] at ha
    rcases ha with ha6 | ha5
    · have : G.degree a = 6 := by simpa [A6] using ha6
      omega
    · have : G.degree a = 5 := by simpa [A5] using ha5
      omega
  have hBdeg : ∀ v ∉ A, G.degree v = 4 := by
    intro v hv
    rcases hcases v with h6 | h5 | h4
    · exact (hv (by simp [A, A6, h6])).elim
    · exact (hv (by simp [A, A5, h5])).elim
    · exact h4
  have hsum6 : (∑ a ∈ A6, G.degree a) = 12 := by
    rw [show (∑ a ∈ A6, G.degree a) = 6 * A6.card by simpa [A6] using sum_degreeClass G 6,
      h6card]
  have hsum5 : (∑ a ∈ A5, G.degree a) = 10 := by
    rw [show (∑ a ∈ A5, G.degree a) = 5 * A5.card by simpa [A5] using sum_degreeClass G 5,
      h5card]
  have hsum : (∑ a ∈ A, G.degree a) = 22 := by
    rw [A, Finset.sum_union hdisj, hsum6, hsum5]
  have hBcard : (Finset.univ \ A).card = 6 := by
    rw [Finset.card_sdiff (Finset.subset_univ A), Finset.card_univ, hn, hAcard]
  apply isTraceable_high_seed_pattern G A 4 1
  · omega
  · exact hAmin
  · exact hBdeg
  · omega
  · omega
  · rw [hsum, hAcard, hBcard]
    norm_num

/-- Row 37: `[6,6,5^10]`. -/
theorem row_665555555555
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hrow : degreeSequence G = [6,6,5,5,5,5,5,5,5,5,5,5]) :
    IsTraceable G := by
  let A := degreeClass G 6
  have hn : Fintype.card V = 12 := by
    have h := card_eq_length_of_degreeSequence_eq G hrow
    norm_num at h
    exact h
  have hAcard : A.card = 2 := by
    have h := card_degreeClass_of_degreeSequence_eq G hrow 6
    norm_num at h
    simpa [A] using h
  have hcases : ∀ v, G.degree v = 6 ∨ G.degree v = 5 := by
    intro v
    have h := degree_mem_degreeSequence G v
    rw [hrow] at h
    simpa using h
  have hAmin : ∀ a ∈ A, 6 ≤ G.degree a := by
    intro a ha
    have : G.degree a = 6 := by simpa [A] using ha
    omega
  have hBdeg : ∀ v ∉ A, G.degree v = 5 := by
    intro v hv
    rcases hcases v with h6 | h5
    · exact (hv (by simpa [A, h6])).elim
    · exact h5
  have hsum : (∑ a ∈ A, G.degree a) = 12 := by
    rw [show (∑ a ∈ A, G.degree a) = 6 * A.card by simpa [A] using sum_degreeClass G 6,
      hAcard]
  have hBcard : (Finset.univ \ A).card = 10 := by
    rw [Finset.card_sdiff (Finset.subset_univ A), Finset.card_univ, hn, hAcard]
  apply isTraceable_high_seed_pattern G A 5 4
  · omega
  · exact hAmin
  · exact hBdeg
  · omega
  · omega
  · rw [hsum, hAcard, hBcard]
    norm_num

/-- Row 38: `[6^4,5^8]`. -/
theorem row_666655555555
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hrow : degreeSequence G = [6,6,6,6,5,5,5,5,5,5,5,5]) :
    IsTraceable G := by
  let A := degreeClass G 6
  have hn : Fintype.card V = 12 := by
    have h := card_eq_length_of_degreeSequence_eq G hrow
    norm_num at h
    exact h
  have hAcard : A.card = 4 := by
    have h := card_degreeClass_of_degreeSequence_eq G hrow 6
    norm_num at h
    simpa [A] using h
  have hcases : ∀ v, G.degree v = 6 ∨ G.degree v = 5 := by
    intro v
    have h := degree_mem_degreeSequence G v
    rw [hrow] at h
    simpa using h
  have hAmin : ∀ a ∈ A, 6 ≤ G.degree a := by
    intro a ha
    have : G.degree a = 6 := by simpa [A] using ha
    omega
  have hBdeg : ∀ v ∉ A, G.degree v = 5 := by
    intro v hv
    rcases hcases v with h6 | h5
    · exact (hv (by simpa [A, h6])).elim
    · exact h5
  have hsum : (∑ a ∈ A, G.degree a) = 24 := by
    rw [show (∑ a ∈ A, G.degree a) = 6 * A.card by simpa [A] using sum_degreeClass G 6,
      hAcard]
  have hBcard : (Finset.univ \ A).card = 8 := by
    rw [Finset.card_sdiff (Finset.subset_univ A), Finset.card_univ, hn, hAcard]
  apply isTraceable_high_seed_pattern G A 5 2
  · omega
  · exact hAmin
  · exact hBdeg
  · omega
  · omega
  · rw [hsum, hAcard, hBcard]
    norm_num

#print axioms SimpleGraph.C217HighSeedRows.row_5544444444
#print axioms SimpleGraph.C217HighSeedRows.row_6554444444
#print axioms SimpleGraph.C217HighSeedRows.row_5555444444
#print axioms SimpleGraph.C217HighSeedRows.row_6655444444
#print axioms SimpleGraph.C217HighSeedRows.row_665555555555
#print axioms SimpleGraph.C217HighSeedRows.row_666655555555

end SimpleGraph.C217HighSeedRows
