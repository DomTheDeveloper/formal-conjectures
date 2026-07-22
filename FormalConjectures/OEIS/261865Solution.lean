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
module

public import FormalConjectures.OEIS.A261865Base
public import FormalConjecturesForMathlib.Analysis.Equidistribution.TerminalBox

@[expose] public section

open Filter
open scoped BigOperators Topology

namespace OeisA261865

/-- The reciprocal-square-root rotation parameters lie strictly between zero and one. -/
theorem alpha_pos_of_two_le {s : ℕ} (hs : 2 ≤ s) : 0 < alpha s := by
  unfold alpha
  exact one_div_pos.mpr (Real.sqrt_pos.2 (by positivity))

theorem alpha_lt_one_of_two_le {s : ℕ} (hs : 2 ≤ s) : alpha s < 1 := by
  have hspos : (0 : ℝ) < s := by positivity
  have hsqrtpos : (0 : ℝ) < Real.sqrt (s : ℝ) := Real.sqrt_pos.2 hspos
  have hsqrtsq : (Real.sqrt (s : ℝ)) ^ 2 = (s : ℝ) := Real.sq_sqrt hspos.le
  have hsqrtone : 1 < Real.sqrt (s : ℝ) := by
    nlinarith [show (2 : ℝ) ≤ s by exact_mod_cast hs]
  unfold alpha
  exact (div_lt_one hsqrtpos).2 hsqrtone

/-- The distinguished element `j` as an element of the relevant-radicand subtype. -/
noncomputable def distinguishedRadicand (j : ℕ) : relevantRadicands j :=
  ⟨j, by simp⟩

/-- The generic terminal-box event is exactly the A261865 least-radicand event. -/
theorem orbit_mem_terminalBox_iff (n j : ℕ) (hj : 2 ≤ j) :
    n • (fun s : relevantRadicands j => (alpha s.1 : UnitAddCircle)) ∈
        UnitAddTorus.terminalBox (distinguishedRadicand j)
          (fun s : relevantRadicands j => alpha s.1) ↔
      0 < n ∧ IsValue n j := by
  classical
  have hge : ∀ s : relevantRadicands j, 2 ≤ s.1 := by
    intro s
    rcases mem_relevantRadicands.mp s.2 with hsj | hs
    · simpa [hsj] using hj
    · exact hs.1
  have ha0 : ∀ s : relevantRadicands j, 0 < alpha s.1 :=
    fun s => alpha_pos_of_two_le (hge s)
  have ha1 : ∀ s : relevantRadicands j, alpha s.1 < 1 :=
    fun s => alpha_lt_one_of_two_le (hge s)
  rw [UnitAddTorus.nsmul_mem_terminalBox_iff (distinguishedRadicand j)
    (fun s : relevantRadicands j => alpha s.1) ha0 ha1 n]
  constructor
  · rintro ⟨hjhit, hmiss⟩
    have hnpos : 0 < n := by
      by_contra hn
      have hnzero : n = 0 := Nat.eq_zero_of_not_pos hn
      subst n
      norm_num at hjhit
      linarith [ha1 (distinguishedRadicand j)]
    refine ⟨hnpos, (isValue_iff_coordinateConditions n j hj).2 ?_⟩
    refine ⟨by simpa [distinguishedRadicand] using hjhit, ?_⟩
    intro s hs hcoord
    let sr : relevantRadicands j :=
      ⟨s, mem_relevantRadicands.mpr (Or.inr (mem_squarefreeBelow.mp hs))⟩
    have hne : sr ≠ distinguishedRadicand j := by
      intro h
      have : s = j := congrArg Subtype.val h
      exact (mem_squarefreeBelow.mp hs).2.1.ne this
    exact hmiss sr hne (by simpa [sr] using hcoord)
  · rintro ⟨hnpos, hvalue⟩
    obtain ⟨hjhit, hsmall⟩ := (isValue_iff_coordinateConditions n j hj).1 hvalue
    refine ⟨by simpa [distinguishedRadicand] using hjhit, ?_⟩
    intro s hne hcoord
    have hsne : s.1 ≠ j := by
      intro h
      apply hne
      apply Subtype.ext
      simpa [distinguishedRadicand] using h
    have hsbelow : s.1 ∈ squarefreeBelow j := by
      rcases mem_relevantRadicands.mp s.2 with hs | hs
      · exact (hsne hs).elim
      · exact mem_squarefreeBelow.mpr hs
    exact hsmall s.1 hsbelow (by simpa using hcoord)

/-- The subtype product over all relevant radicands except `j` is the advertised product over
`squarefreeBelow j`. -/
theorem product_erase_distinguished (j : ℕ) :
    ∏ s ∈ (Finset.univ.erase (distinguishedRadicand j)), (1 - alpha s.1) =
      ∏ s ∈ squarefreeBelow j, (1 - alpha s) := by
  classical
  refine Finset.prod_bij (fun s _ => s.1) ?_ ?_ ?_ ?_
  · intro s hs
    have hne : s ≠ distinguishedRadicand j := Finset.ne_of_mem_erase hs
    rcases mem_relevantRadicands.mp s.2 with hsj | hsj
    · exfalso
      apply hne
      apply Subtype.ext
      simpa [distinguishedRadicand] using hsj
    · exact mem_squarefreeBelow.mpr hsj
  · intro a ha b hb hab
    exact Subtype.ext hab
  · intro s hs
    let sr : relevantRadicands j :=
      ⟨s, mem_relevantRadicands.mpr (Or.inr (mem_squarefreeBelow.mp hs))⟩
    have hne : sr ≠ distinguishedRadicand j := by
      intro h
      have : s = j := congrArg Subtype.val h
      exact (mem_squarefreeBelow.mp hs).2.1.ne this
    exact ⟨sr, Finset.mem_erase.mpr ⟨hne, Finset.mem_univ sr⟩, rfl⟩
  · intro s hs
    rfl

/-- Axiom-free proof candidate for Peter Kagey's Problem 13 / OEIS A261865. -/
theorem density_formula_solution (j : ℕ) (hj : 2 ≤ j) (hsq : Squarefree j) :
    {n : ℕ | 0 < n ∧ IsValue n j}.HasDensity (predictedDensity j) := by
  classical
  have hge : ∀ s ∈ relevantRadicands j, 2 ≤ s := by
    intro s hs
    rcases mem_relevantRadicands.mp hs with rfl | hs
    · exact hj
    · exact hs.1
  have hsqR : ∀ s ∈ relevantRadicands j, Squarefree s := by
    intro s hs
    rcases mem_relevantRadicands.mp hs with rfl | hs
    · exact hsq
    · exact hs.2.2
  have ha0 : ∀ s : relevantRadicands j, 0 < alpha s.1 :=
    fun s => alpha_pos_of_two_le (hge s.1 s.2)
  have ha1 : ∀ s : relevantRadicands j, alpha s.1 < 1 :=
    fun s => alpha_lt_one_of_two_le (hge s.1 s.2)
  have hrel : UnitAddTorus.NoIntegerRelation
      (fun s : relevantRadicands j => alpha s.1) :=
    noIntegerRelation_alpha (relevantRadicands j) hge hsqR
  have hgeneric := UnitAddTorus.hasDensity_terminalBox
    (distinguishedRadicand j) (fun s : relevantRadicands j => alpha s.1) ha0 ha1 hrel
  have hevent :
      {n : ℕ | n • (fun s : relevantRadicands j => (alpha s.1 : UnitAddCircle)) ∈
        UnitAddTorus.terminalBox (distinguishedRadicand j)
          (fun s : relevantRadicands j => alpha s.1)} =
      {n : ℕ | 0 < n ∧ IsValue n j} := by
    ext n
    exact orbit_mem_terminalBox_iff n j hj
  rw [hevent] at hgeneric
  convert hgeneric using 1
  rw [predictedDensity, product_erase_distinguished]
  rfl

end OeisA261865
