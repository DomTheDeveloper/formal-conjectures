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

open SimpleGraph

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false

private def counterexampleEdges : Finset (Sym2 (Fin 21)) := {
  s(0, 1), s(1, 2), s(2, 0), s(0, 3), s(0, 4), s(1, 5), s(1, 6),
  s(7, 8), s(8, 9), s(9, 7), s(7, 10), s(7, 11), s(8, 12), s(8, 13),
  s(14, 15), s(15, 16), s(16, 14), s(14, 17), s(14, 18), s(15, 19), s(15, 20),
  s(0, 7), s(1, 14), s(8, 15) }

/--
A counterexample built from three seven-vertex gadgets. In gadget `i`, the
vertices `7i`, `7i+1`, `7i+2` form a triangle; two leaves are attached to each
of the first two triangle vertices. The three gadgets are connected by the
edges `0-7`, `1-14`, and `8-15`.
-/
def counterexample : SimpleGraph (Fin 21) :=
  SimpleGraph.fromEdgeSet (counterexampleEdges : Set (Sym2 (Fin 21)))

private instance : DecidableRel counterexample.Adj := by
  dsimp [counterexample]
  infer_instance

private lemma counterexample_reachable_zero (v : Fin 21) :
    counterexample.Reachable 0 v := by
  have r01 : counterexample.Reachable 0 1 :=
    (show counterexample.Adj 0 1 by decide).reachable
  have r02 : counterexample.Reachable 0 2 :=
    (show counterexample.Adj 0 2 by decide).reachable
  have r03 : counterexample.Reachable 0 3 :=
    (show counterexample.Adj 0 3 by decide).reachable
  have r04 : counterexample.Reachable 0 4 :=
    (show counterexample.Adj 0 4 by decide).reachable
  have r05 : counterexample.Reachable 0 5 :=
    r01.trans (show counterexample.Adj 1 5 by decide).reachable
  have r06 : counterexample.Reachable 0 6 :=
    r01.trans (show counterexample.Adj 1 6 by decide).reachable
  have r07 : counterexample.Reachable 0 7 :=
    (show counterexample.Adj 0 7 by decide).reachable
  have r08 : counterexample.Reachable 0 8 :=
    r07.trans (show counterexample.Adj 7 8 by decide).reachable
  have r09 : counterexample.Reachable 0 9 :=
    r07.trans (show counterexample.Adj 7 9 by decide).reachable
  have r10 : counterexample.Reachable 0 10 :=
    r07.trans (show counterexample.Adj 7 10 by decide).reachable
  have r11 : counterexample.Reachable 0 11 :=
    r07.trans (show counterexample.Adj 7 11 by decide).reachable
  have r12 : counterexample.Reachable 0 12 :=
    r08.trans (show counterexample.Adj 8 12 by decide).reachable
  have r13 : counterexample.Reachable 0 13 :=
    r08.trans (show counterexample.Adj 8 13 by decide).reachable
  have r14 : counterexample.Reachable 0 14 :=
    r01.trans (show counterexample.Adj 1 14 by decide).reachable
  have r15 : counterexample.Reachable 0 15 :=
    r14.trans (show counterexample.Adj 14 15 by decide).reachable
  have r16 : counterexample.Reachable 0 16 :=
    r14.trans (show counterexample.Adj 14 16 by decide).reachable
  have r17 : counterexample.Reachable 0 17 :=
    r14.trans (show counterexample.Adj 14 17 by decide).reachable
  have r18 : counterexample.Reachable 0 18 :=
    r14.trans (show counterexample.Adj 14 18 by decide).reachable
  have r19 : counterexample.Reachable 0 19 :=
    r15.trans (show counterexample.Adj 15 19 by decide).reachable
  have r20 : counterexample.Reachable 0 20 :=
    r15.trans (show counterexample.Adj 15 20 by decide).reachable
  fin_cases v
  · exact .rfl
  · exact r01
  · exact r02
  · exact r03
  · exact r04
  · exact r05
  · exact r06
  · exact r07
  · exact r08
  · exact r09
  · exact r10
  · exact r11
  · exact r12
  · exact r13
  · exact r14
  · exact r15
  · exact r16
  · exact r17
  · exact r18
  · exact r19
  · exact r20

private lemma counterexample_connected : counterexample.Connected := by
  rw [connected_iff_exists_forall_reachable]
  exact ⟨0, counterexample_reachable_zero⟩

private def degreeFiveVertices : Finset (Fin 21) := {0, 1, 7, 8, 14, 15}
private def degreeTwoVertices : Finset (Fin 21) := {2, 9, 16}

private lemma counterexample_degree (v : Fin 21) :
    counterexample.degree v =
      if v ∈ degreeFiveVertices then 5 else if v ∈ degreeTwoVertices then 2 else 1 := by
  fin_cases v <;> decide

private def degreeSequence0 : List ℕ :=
  [5, 5, 5, 5, 5, 5, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
private def degreeSequence1 : List ℕ :=
  [4, 4, 4, 4, 4, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
private def degreeSequence2 : List ℕ :=
  [3, 3, 3, 3, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
private def degreeSequence3 : List ℕ :=
  [2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
private def degreeSequence4 : List ℕ :=
  [2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
private def degreeSequence5 : List ℕ :=
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
private def degreeSequence6 : List ℕ :=
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0]
private def degreeSequence7 : List ℕ :=
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0]
private def degreeSequence8 : List ℕ :=
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0]
private def degreeSequence9 : List ℕ :=
  [1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0]
private def degreeSequence10 : List ℕ :=
  [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0]
private def degreeSequence11 : List ℕ :=
  [1, 1, 1, 1, 0, 0, 0, 0, 0, 0]
private def degreeSequence12 : List ℕ :=
  [1, 1, 0, 0, 0, 0, 0, 0, 0]
private def degreeSequence13 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0]

private lemma counterexample_degree_sequence :
    (Finset.univ.val.map fun v : Fin 21 => counterexample.degree v).sort (· ≥ ·) =
      degreeSequence0 := by
  simp_rw [counterexample_degree]
  norm_num [degreeFiveVertices, degreeTwoVertices, degreeSequence0, Multiset.sort,
    List.mergeSort]

private lemma hhStep0 : havelHakimiStep degreeSequence0 = degreeSequence1 := by
  norm_num [havelHakimiStep, degreeSequence0, degreeSequence1, List.mergeSort]
private lemma hhStep1 : havelHakimiStep degreeSequence1 = degreeSequence2 := by
  norm_num [havelHakimiStep, degreeSequence1, degreeSequence2, List.mergeSort]
private lemma hhStep2 : havelHakimiStep degreeSequence2 = degreeSequence3 := by
  norm_num [havelHakimiStep, degreeSequence2, degreeSequence3, List.mergeSort]
private lemma hhStep3 : havelHakimiStep degreeSequence3 = degreeSequence4 := by
  norm_num [havelHakimiStep, degreeSequence3, degreeSequence4, List.mergeSort]
private lemma hhStep4 : havelHakimiStep degreeSequence4 = degreeSequence5 := by
  norm_num [havelHakimiStep, degreeSequence4, degreeSequence5, List.mergeSort]
private lemma hhStep5 : havelHakimiStep degreeSequence5 = degreeSequence6 := by
  norm_num [havelHakimiStep, degreeSequence5, degreeSequence6, List.mergeSort]
private lemma hhStep6 : havelHakimiStep degreeSequence6 = degreeSequence7 := by
  norm_num [havelHakimiStep, degreeSequence6, degreeSequence7, List.mergeSort]
private lemma hhStep7 : havelHakimiStep degreeSequence7 = degreeSequence8 := by
  norm_num [havelHakimiStep, degreeSequence7, degreeSequence8, List.mergeSort]
private lemma hhStep8 : havelHakimiStep degreeSequence8 = degreeSequence9 := by
  norm_num [havelHakimiStep, degreeSequence8, degreeSequence9, List.mergeSort]
private lemma hhStep9 : havelHakimiStep degreeSequence9 = degreeSequence10 := by
  norm_num [havelHakimiStep, degreeSequence9, degreeSequence10, List.mergeSort]
private lemma hhStep10 : havelHakimiStep degreeSequence10 = degreeSequence11 := by
  norm_num [havelHakimiStep, degreeSequence10, degreeSequence11, List.mergeSort]
private lemma hhStep11 : havelHakimiStep degreeSequence11 = degreeSequence12 := by
  norm_num [havelHakimiStep, degreeSequence11, degreeSequence12, List.mergeSort]
private lemma hhStep12 : havelHakimiStep degreeSequence12 = degreeSequence13 := by
  norm_num [havelHakimiStep, degreeSequence12, degreeSequence13, List.mergeSort]

private lemma counterexample_residue_aux : residueAux degreeSequence0 = 8 := by
  rw [SimpleGraph.residueAux.eq_def, hhStep0]
  rw [SimpleGraph.residueAux.eq_def, hhStep1]
  rw [SimpleGraph.residueAux.eq_def, hhStep2]
  rw [SimpleGraph.residueAux.eq_def, hhStep3]
  rw [SimpleGraph.residueAux.eq_def, hhStep4]
  rw [SimpleGraph.residueAux.eq_def, hhStep5]
  rw [SimpleGraph.residueAux.eq_def, hhStep6]
  rw [SimpleGraph.residueAux.eq_def, hhStep7]
  rw [SimpleGraph.residueAux.eq_def, hhStep8]
  rw [SimpleGraph.residueAux.eq_def, hhStep9]
  rw [SimpleGraph.residueAux.eq_def, hhStep10]
  rw [SimpleGraph.residueAux.eq_def, hhStep11]
  rw [SimpleGraph.residueAux.eq_def, hhStep12]
  norm_num [SimpleGraph.residueAux.eq_def, degreeSequence13]

private lemma counterexample_residue : residue counterexample = 8 := by
  unfold residue
  rw [counterexample_degree_sequence]
  exact counterexample_residue_aux

private def independentWitness : Finset (Fin 21) :=
  {2, 3, 4, 5, 6, 9, 10, 11, 12, 13, 16, 17, 18, 19, 20}

private lemma independentWitness_isIndep :
    counterexample.IsIndepSet (independentWitness : Set (Fin 21)) := by
  decide

private lemma independentWitness_card : independentWitness.card = 15 := by
  decide

private lemma fifteen_le_indepNum : 15 ≤ counterexample.indepNum := by
  rw [← independentWitness_card]
  exact independentWitness_isIndep.card_le_indepNum

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

private lemma triangle01_disjoint : Disjoint triangle0 triangle1 := by decide
private lemma triangle02_disjoint : Disjoint triangle0 triangle2 := by decide
private lemma triangle12_disjoint : Disjoint triangle1 triangle2 := by decide

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

private lemma empty_induced_isBipartite :
    (counterexample.induce ((∅ : Finset (Fin 21)) : Set (Fin 21))).IsBipartite := by
  rw [isBipartite_iff_exists_isBipartiteWith]
  refine ⟨∅, ∅, ⟨by simp, ?_⟩⟩
  intro v w _
  have hv : v.val ∈ ((∅ : Finset (Fin 21)) : Set (Fin 21)) := v.property
  simp at hv

private lemma largestInducedBipartiteSubgraphSize_le_eighteen :
    largestInducedBipartiteSubgraphSize counterexample ≤ 18 := by
  unfold largestInducedBipartiteSubgraphSize
  apply csSup_le
  · exact ⟨0, ∅, empty_induced_isBipartite, rfl⟩
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

set_option linter.style.ams_attribute true
set_option linter.style.category_attribute true

/--
WOWII [Conjecture 109](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/):

For a simple connected graph $G$, the independence number $\alpha(G)$ was conjectured to satisfy
$\alpha(G) \le \lfloor (\mathrm{residue}(G) + 2 \cdot b(G)) / 3 \rfloor$, where
$\mathrm{residue}(G)$ is the Havel-Hakimi residue and $b(G)$ is the size of a
largest induced bipartite subgraph.

This is false. The explicit graph `counterexample` is connected, has an independent set of
size 15, residue 8, and every induced bipartite subgraph has at most 18 vertices. Thus the
conjectured right-hand side is at most $\lfloor(8+2\cdot18)/3\rfloor=14$.
-/
@[category research solved, AMS 5]
theorem conjecture109 : answer(False) ↔
    ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) [DecidableRel G.Adj] (_h : G.Connected),
      (G.indepNum : ℝ) ≤ ⌊((residue G : ℝ) + 2 * b G) / 3⌋ :=
  ⟨False.elim, fun h =>
    counterexample_violates_bound (h (Fin 21) counterexample counterexample_connected)⟩

-- Sanity checks

/-- The invariant `b G` is nonneg (cast of a natural number). -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ b G := Nat.cast_nonneg _

/-- The residue of $K_2$ equals $1$: degree sequence is $[1, 1]`; one Havel-Hakimi
step gives $[0]`, leaving a single zero. -/
@[category test, AMS 5]
example : residue (⊤ : SimpleGraph (Fin 2)) = 1 := by
  unfold residue
  decide +native

end WrittenOnTheWallII.GraphConjecture109
