/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

/-!
# Written on the Wall II - Conjecture 109

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture109

open Classical SimpleGraph

/--
A counterexample built from three seven-vertex gadgets.  In gadget `i`, the
vertices `7i`, `7i+1`, `7i+2` form a triangle; two leaves are attached to each
of the first two triangle vertices.  The three gadgets are connected by the
edges `0-7`, `1-14`, and `8-15`.
-/
def counterexample : SimpleGraph (Fin 21) :=
  SimpleGraph.fromEdgeSet {
    s(0, 1), s(1, 2), s(2, 0), s(0, 3), s(0, 4), s(1, 5), s(1, 6),
    s(7, 8), s(8, 9), s(9, 7), s(7, 10), s(7, 11), s(8, 12), s(8, 13),
    s(14, 15), s(15, 16), s(16, 14), s(14, 17), s(14, 18), s(15, 19), s(15, 20),
    s(0, 7), s(1, 14), s(8, 15) }

private instance : DecidableRel counterexample.Adj := inferInstance

private lemma counterexample_connected : counterexample.Connected := by
  decide +native

private lemma counterexample_residue : residue counterexample = 8 := by
  unfold residue counterexample
  decide +native

private def independentWitness : Finset (Fin 21) :=
  {2, 3, 4, 5, 6, 9, 10, 11, 12, 13, 16, 17, 18, 19, 20}

private lemma independentWitness_isIndep :
    counterexample.IsIndepSet (independentWitness : Set (Fin 21)) := by
  decide +native

private lemma fifteen_le_indepNum : 15 ≤ counterexample.indepNum := by
  have h := independentWitness_isIndep.card_le_indepNum
  norm_num [independentWitness] at h ⊢
  exact h

/-- A bipartite induced subgraph cannot contain all three vertices of a triangle. -/
private lemma misses_triangle (S : Finset (Fin 21))
    (hBip : (counterexample.induce (S : Set (Fin 21))).IsBipartite)
    (a b c : Fin 21)
    (hab : counterexample.Adj a b) (hbc : counterexample.Adj b c)
    (hca : counterexample.Adj c a) :
    ∃ x ∈ ({a, b, c} : Finset (Fin 21)), x ∉ S := by
  by_contra h
  push_neg at h
  have ha : a ∈ S := h a (by simp)
  have hb : b ∈ S := h b (by simp)
  have hc : c ∈ S := h c (by simp)
  let a' : ↥(S : Set (Fin 21)) := ⟨a, by simpa using ha⟩
  let b' : ↥(S : Set (Fin 21)) := ⟨b, by simpa using hb⟩
  let c' : ↥(S : Set (Fin 21)) := ⟨c, by simpa using hc⟩
  have hab' : (counterexample.induce (S : Set (Fin 21))).Adj a' b' := by
    change counterexample.Adj a b
    exact hab
  have hbc' : (counterexample.induce (S : Set (Fin 21))).Adj b' c' := by
    change counterexample.Adj b c
    exact hbc
  have hca' : (counterexample.induce (S : Set (Fin 21))).Adj c' a' := by
    change counterexample.Adj c a
    exact hca
  obtain ⟨L, R, hLR⟩ := hBip.exists_isBipartiteWith
  have hd : ∀ ⦃v⦄, v ∈ L → v ∈ R → False := Set.disjoint_left.mp hLR.disjoint
  have eab := hLR.mem_of_adj hab'
  have ebc := hLR.mem_of_adj hbc'
  have eca := hLR.mem_of_adj hca'
  rcases eab with eab | eab <;>
    rcases ebc with ebc | ebc <;>
    rcases eca with eca | eca <;> aesop

private def triangle0 : Finset (Fin 21) := {0, 1, 2}
private def triangle1 : Finset (Fin 21) := {7, 8, 9}
private def triangle2 : Finset (Fin 21) := {14, 15, 16}

private lemma triangle01_disjoint : Disjoint triangle0 triangle1 := by decide +native
private lemma triangle02_disjoint : Disjoint triangle0 triangle2 := by decide +native
private lemma triangle12_disjoint : Disjoint triangle1 triangle2 := by decide +native

/-- Every induced bipartite subgraph omits at least one vertex from each of the
three disjoint triangles, and therefore has at most eighteen vertices. -/
private lemma bipartite_card_le_eighteen (S : Finset (Fin 21))
    (hBip : (counterexample.induce (S : Set (Fin 21))).IsBipartite) :
    S.card ≤ 18 := by
  obtain ⟨x0, hx0, hx0S⟩ := misses_triangle S hBip 0 1 2 (by decide) (by decide) (by decide)
  obtain ⟨x1, hx1, hx1S⟩ := misses_triangle S hBip 7 8 9 (by decide) (by decide) (by decide)
  obtain ⟨x2, hx2, hx2S⟩ := misses_triangle S hBip 14 15 16 (by decide) (by decide) (by decide)
  have hx0' : x0 ∈ triangle0 := by simpa [triangle0] using hx0
  have hx1' : x1 ∈ triangle1 := by simpa [triangle1] using hx1
  have hx2' : x2 ∈ triangle2 := by simpa [triangle2] using hx2
  have hx01 : x0 ≠ x1 := by
    intro h
    subst x1
    exact Finset.disjoint_left.mp triangle01_disjoint hx0' hx1'
  have hx02 : x0 ≠ x2 := by
    intro h
    subst x2
    exact Finset.disjoint_left.mp triangle02_disjoint hx0' hx2'
  have hx12 : x1 ≠ x2 := by
    intro h
    subst x2
    exact Finset.disjoint_left.mp triangle12_disjoint hx1' hx2'
  have hmissing_card : ({x0, x1, x2} : Finset (Fin 21)).card = 3 := by
    simp [hx01, hx02, hx12]
  have hmissing_subset : ({x0, x1, x2} : Finset (Fin 21)) ⊆ Finset.univ \ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · exact hx0S
    · exact hx1S
    · exact hx2S
  have hcomp : 3 ≤ (Finset.univ \ S).card := by
    rw [← hmissing_card]
    exact Finset.card_le_card hmissing_subset
  have hpartition := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  simp at hpartition
  omega

private lemma largestInducedBipartiteSubgraphSize_le_eighteen :
    largestInducedBipartiteSubgraphSize counterexample ≤ 18 := by
  unfold largestInducedBipartiteSubgraphSize
  apply csSup_le
  · exact ⟨0, ∅, by simp, rfl⟩
  · rintro n ⟨S, hBip, rfl⟩
    exact bipartite_card_le_eighteen S hBip

private lemma b_le_eighteen : b counterexample ≤ 18 := by
  unfold b
  exact_mod_cast largestInducedBipartiteSubgraphSize_le_eighteen

private lemma counterexample_violates_bound :
    ¬ ((counterexample.indepNum : ℝ) ≤
      ⌊((residue counterexample : ℝ) + 2 * b counterexample) / 3⌋) := by
  intro h
  have ha : (15 : ℝ) ≤ counterexample.indepNum := by
    exact_mod_cast fifteen_le_indepNum
  have hx : ((residue counterexample : ℝ) + 2 * b counterexample) / 3 < 15 := by
    norm_num [counterexample_residue]
    nlinarith [b_le_eighteen]
  have hfInt :
      ⌊((residue counterexample : ℝ) + 2 * b counterexample) / 3⌋ < (15 : ℤ) :=
    Int.floor_lt.mpr hx
  have hf :
      (⌊((residue counterexample : ℝ) + 2 * b counterexample) / 3⌋ : ℝ) < 15 := by
    exact_mod_cast hfInt
  linarith

/--
WOWII [Conjecture 109](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/):

For a simple connected graph $G$, the independence number $\alpha(G)$ was conjectured to satisfy
$\alpha(G) \le \lfloor (\mathrm{residue}(G) + 2 \cdot b(G)) / 3 \rfloor$, where
$\mathrm{residue}(G)$ is the Havel-Hakimi residue and $b(G)$ is the size of a
largest induced bipartite subgraph.

This is false.  The explicit graph `counterexample` is connected, has an independent set of
size 15, residue 8, and every induced bipartite subgraph has at most 18 vertices.  Thus the
conjectured right-hand side is at most $\lfloor(8+2\cdot18)/3\rfloor=14$.
-/
@[category research solved, AMS 5]
theorem conjecture109 : answer(False) ↔
    ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected),
      (G.indepNum : ℝ) ≤ ⌊((residue G : ℝ) + 2 * b G) / 3⌋ :=
  ⟨False.elim, fun h =>
    counterexample_violates_bound (h (Fin 21) counterexample counterexample_connected)⟩

-- Sanity checks

/-- The invariant `b G` is nonneg (cast of a natural number). -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ b G := Nat.cast_nonneg _

/-- The residue of $K_2$ equals $1$: degree sequence is $[1, 1]$; one Havel-Hakimi
step gives $[0]$, leaving a single zero. -/
@[category test, AMS 5]
example : residue (⊤ : SimpleGraph (Fin 2)) = 1 := by
  unfold residue; decide +native

end WrittenOnTheWallII.GraphConjecture109
