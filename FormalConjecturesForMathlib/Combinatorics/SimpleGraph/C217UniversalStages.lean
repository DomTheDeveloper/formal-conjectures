/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217ClosureHelpers

/-!
# Staged universality in the Bondy--Chvátal path closure

Several C217 rows have three degree classes. High vertices first join the high
and middle classes. The resulting counted degree then forces their remaining
edges to the low class. This module packages that repeated argument.
-/

namespace SimpleGraph.C217UniversalStages

open Classical
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]

/-- If every high vertex is adjacent in the final closure to the other high
vertices and all middle vertices, and this counted neighborhood plus the low
class degree reaches the closure threshold, then the high set is universal. -/
theorem universal_of_high_middle
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C : Finset V) (d : ℕ)
    (hdisj : Disjoint A C)
    (hAA : ∀ a ∈ A, ∀ b ∈ A, b ≠ a → (pathClosure G).Adj a b)
    (hAC : ∀ a ∈ A, ∀ c ∈ C, (pathClosure G).Adj a c)
    (hDdeg : ∀ v ∉ A ∪ C, d ≤ (pathClosure G).degree v)
    (hthreshold : Fintype.card V - 1 ≤ (A.card - 1 + C.card) + d) :
    ∀ a ∈ A, ∀ v, v ≠ a → (pathClosure G).Adj a v := by
  intro a ha v hav
  by_cases hvA : v ∈ A
  · exact hAA a ha v hvA hav
  by_cases hvC : v ∈ C
  · exact hAC a ha v hvC
  let H := pathClosure G
  have hACdisj : Disjoint (A.erase a) C :=
    hdisj.mono (Finset.erase_subset a A) (by rfl)
  have hsub : (A.erase a) ∪ C ⊆ H.neighborFinset a := by
    intro x hx
    rw [Finset.mem_union] at hx
    rcases hx with hxA | hxC
    · have hxe := Finset.mem_erase.mp hxA
      simpa [H] using hAA a ha x hxe.2 hxe.1
    · simpa [H] using hAC a ha x hxC
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hACdisj,
    Finset.card_erase_of_mem ha, card_neighborFinset_eq_degree] at hcard
  apply pathClosure_spec G hav
  have hvD : v ∉ A ∪ C := by simp [hvA, hvC]
  exact hthreshold.trans (Nat.add_le_add hcard (hDdeg v hvD))

#print axioms SimpleGraph.C217UniversalStages.universal_of_high_middle

end SimpleGraph.C217UniversalStages
