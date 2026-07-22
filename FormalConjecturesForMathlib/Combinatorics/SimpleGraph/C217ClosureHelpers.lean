/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.ChvatalPath
import Lean.Elab.Tactic.Omega

/-!
# Reusable path-closure completion lemmas for WOWII Conjecture 217

These lemmas isolate the graph-theoretic core of the exceptional degree-row
proofs. In particular, the seed lemma explicitly retains the necessary
hypothesis `r ≤ A.card`: without it, the informal seed statement is false.
The one low-degree row where the universal set has size `r - 1` is handled by
a two-seed completion lemma.
-/

namespace SimpleGraph.C217ClosureHelpers

open Classical
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]

/-- If the Bondy--Chvátal path closure is complete, then the original graph is
traceable. -/
theorem isTraceable_of_pathClosure_eq_top
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : pathClosure G = (⊤ : SimpleGraph V)) :
    IsTraceable G := by
  apply (pathClosure_traceable_iff G).mp
  rw [h]
  exact top_isTraceable

/-- An original degree-sum lower bound is enough to force an edge in the final
path closure. -/
lemma pathClosure_adj_of_degree_sum
    (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V}
    (huv : u ≠ v)
    (hdeg : Fintype.card V - 1 ≤ G.degree u + G.degree v) :
    (pathClosure G).Adj u v := by
  apply pathClosure_spec G huv
  exact hdeg.trans (Nat.add_le_add
    (degree_le_of_le (self_le_pathClosure G))
    (degree_le_of_le (self_le_pathClosure G)))

/-- A uniform degree lower bound in the final path closure makes it complete
once twice that lower bound reaches the path-closure threshold. -/
lemma pathClosure_eq_top_of_degree_lower_bound
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (hdeg : ∀ v, d ≤ (pathClosure G).degree v)
    (hthreshold : Fintype.card V - 1 ≤ d + d) :
    pathClosure G = (⊤ : SimpleGraph V) := by
  ext u v
  constructor
  · intro huv
    simpa using huv.ne
  · intro huv
    apply pathClosure_spec G huv
    exact hthreshold.trans (Nat.add_le_add (hdeg u) (hdeg v))

/-- Correct one-seed completion lemma.

Let `H` be the final path closure of a graph of order `2r+2`. Suppose `A` is
a universal set in `H`, has at least `r` vertices, every vertex outside `A`
has degree at least `r`, and one outside vertex has degree at least `r+1`.
Then `H` is complete.

The cardinality condition on `A` is essential. It ensures that, after the seed
is forced adjacent to an outside vertex, that vertex has the `A`-neighbors
plus the seed and hence degree at least `r+1`, even when the seed edge was
already present. -/
theorem pathClosure_eq_top_of_universal_seed
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (r : ℕ)
    (hn : Fintype.card V = 2 * r + 2)
    (hAcard : r ≤ A.card)
    (huniv : ∀ a ∈ A, ∀ v, v ≠ a → (pathClosure G).Adj a v)
    (hout : ∀ v ∉ A, r ≤ (pathClosure G).degree v)
    (hseed : ∃ s ∉ A, r + 1 ≤ (pathClosure G).degree s) :
    pathClosure G = (⊤ : SimpleGraph V) := by
  let H := pathClosure G
  obtain ⟨s, hsA, hsdeg⟩ := hseed
  have houtStrong : ∀ v ∉ A, r + 1 ≤ H.degree v := by
    intro v hvA
    by_cases hvs : v = s
    · simpa [H, hvs] using hsdeg
    · have hsv : H.Adj s v := by
        apply pathClosure_spec G hvs.symm
        have hvdeg := hout v hvA
        simpa [H, hn] using (show 2 * r + 1 ≤ H.degree s + H.degree v by omega)
      have hsub : insert s A ⊆ H.neighborFinset v := by
        intro x hx
        rw [Finset.mem_insert] at hx
        rcases hx with rfl | hxA
        · simpa using hsv.symm
        · have hxv : x ≠ v := by
            intro h
            subst x
            exact hvA hxA
          simpa [H] using (huniv x hxA v hxv).symm
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hsA, card_neighborFinset_eq_degree] at hcard
      omega
  ext u v
  constructor
  · intro huv
    simpa using huv.ne
  · intro huv
    by_cases huA : u ∈ A
    · exact huniv u huA v huv
    · by_cases hvA : v ∈ A
      · exact (huniv v hvA u huv.symm).symm
      · apply pathClosure_spec G huv
        have hu := houtStrong u huA
        have hv := houtStrong v hvA
        simpa [H, hn] using (show 2 * r + 1 ≤ H.degree u + H.degree v by omega)

/-- Two-seed completion for the case where the universal set has size only
`r - 1`.

Two distinct outside vertices of degree at least `r+1` force their edges to
every other outside vertex. Together with the universal set this gives each
outside vertex at least `r+1` neighbors, after which the outside set closes to
a clique. This is the reusable endgame for the exceptional row `[4²,3⁶]`. -/
theorem pathClosure_eq_top_of_universal_two_seeds
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (r : ℕ)
    (hn : Fintype.card V = 2 * r + 2)
    (hAcard : r ≤ A.card + 1)
    (huniv : ∀ a ∈ A, ∀ v, v ≠ a → (pathClosure G).Adj a v)
    (hout : ∀ v ∉ A, r ≤ (pathClosure G).degree v)
    (hseeds : ∃ s t, s ∉ A ∧ t ∉ A ∧ s ≠ t ∧
      r + 1 ≤ (pathClosure G).degree s ∧
      r + 1 ≤ (pathClosure G).degree t) :
    pathClosure G = (⊤ : SimpleGraph V) := by
  let H := pathClosure G
  obtain ⟨s, t, hsA, htA, hst, hsdeg, htdeg⟩ := hseeds
  have houtStrong : ∀ v ∉ A, r + 1 ≤ H.degree v := by
    intro v hvA
    by_cases hvs : v = s
    · simpa [H, hvs] using hsdeg
    · by_cases hvt : v = t
      · simpa [H, hvt] using htdeg
      · have hsv : H.Adj s v := by
          apply pathClosure_spec G hvs.symm
          have hvdeg := hout v hvA
          simpa [H, hn] using (show 2 * r + 1 ≤ H.degree s + H.degree v by omega)
        have htv : H.Adj t v := by
          apply pathClosure_spec G hvt.symm
          have hvdeg := hout v hvA
          simpa [H, hn] using (show 2 * r + 1 ≤ H.degree t + H.degree v by omega)
        have hsInsert : s ∉ insert t A := by simp [hsA, hst]
        have hsub : insert s (insert t A) ⊆ H.neighborFinset v := by
          intro x hx
          simp only [Finset.mem_insert] at hx
          rcases hx with rfl | rfl | hxA
          · simpa using hsv.symm
          · simpa using htv.symm
          · have hxv : x ≠ v := by
              intro h
              subst x
              exact hvA hxA
            simpa [H] using (huniv x hxA v hxv).symm
        have hcard := Finset.card_le_card hsub
        rw [Finset.card_insert_of_notMem hsInsert,
          Finset.card_insert_of_notMem htA, card_neighborFinset_eq_degree] at hcard
        omega
  ext u v
  constructor
  · intro huv
    simpa using huv.ne
  · intro huv
    by_cases huA : u ∈ A
    · exact huniv u huA v huv
    · by_cases hvA : v ∈ A
      · exact (huniv v hvA u huv.symm).symm
      · apply pathClosure_spec G huv
        have hu := houtStrong u huA
        have hv := houtStrong v hvA
        simpa [H, hn] using (show 2 * r + 1 ≤ H.degree u + H.degree v by omega)

/-- The corrected one-seed hypotheses imply traceability of the original graph. -/
theorem isTraceable_of_universal_seed
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (r : ℕ)
    (hn : Fintype.card V = 2 * r + 2)
    (hAcard : r ≤ A.card)
    (huniv : ∀ a ∈ A, ∀ v, v ≠ a → (pathClosure G).Adj a v)
    (hout : ∀ v ∉ A, r ≤ (pathClosure G).degree v)
    (hseed : ∃ s ∉ A, r + 1 ≤ (pathClosure G).degree s) :
    IsTraceable G :=
  isTraceable_of_pathClosure_eq_top G
    (pathClosure_eq_top_of_universal_seed G A r hn hAcard huniv hout hseed)

/-- The two-seed hypotheses imply traceability of the original graph. -/
theorem isTraceable_of_universal_two_seeds
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (r : ℕ)
    (hn : Fintype.card V = 2 * r + 2)
    (hAcard : r ≤ A.card + 1)
    (huniv : ∀ a ∈ A, ∀ v, v ≠ a → (pathClosure G).Adj a v)
    (hout : ∀ v ∉ A, r ≤ (pathClosure G).degree v)
    (hseeds : ∃ s t, s ∉ A ∧ t ∉ A ∧ s ≠ t ∧
      r + 1 ≤ (pathClosure G).degree s ∧
      r + 1 ≤ (pathClosure G).degree t) :
    IsTraceable G :=
  isTraceable_of_pathClosure_eq_top G
    (pathClosure_eq_top_of_universal_two_seeds G A r hn hAcard huniv hout hseeds)

#print axioms SimpleGraph.C217ClosureHelpers.pathClosure_adj_of_degree_sum
#print axioms SimpleGraph.C217ClosureHelpers.pathClosure_eq_top_of_degree_lower_bound
#print axioms SimpleGraph.C217ClosureHelpers.pathClosure_eq_top_of_universal_seed
#print axioms SimpleGraph.C217ClosureHelpers.pathClosure_eq_top_of_universal_two_seeds
#print axioms SimpleGraph.C217ClosureHelpers.isTraceable_of_universal_seed
#print axioms SimpleGraph.C217ClosureHelpers.isTraceable_of_universal_two_seeds

end SimpleGraph.C217ClosureHelpers
