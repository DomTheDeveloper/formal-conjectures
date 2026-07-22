/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.MaximumLeafDegree
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.DegreeTwoTraceable
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Residue

open Classical
namespace SimpleGraph.C217BaseReduction

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

noncomputable def residueEqTwoIndicator
    (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  if residue G = 2 then 1 else 0

/-- The entire `residue G ≠ 2` branch of WOWII Conjecture 217. -/
theorem traceable_of_residue_ne_two
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2)
    (hres : residue G ≠ 2) :
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  have hLtwo : Ls G ≤ 2 := by
    simpa [residueEqTwoIndicator, hres] using hL
  have hdeg : ∀ v, G.degree v ≤ 2 := by
    intro v
    have hcast : (G.degree v : ℝ) ≤ 2 :=
      (degree_cast_le_Ls_of_connected G hG v).trans hLtwo
    exact_mod_cast hcast
  exact hG.exists_hamiltonianPath_of_degree_le_two G hdeg

/-- In the exceptional residue-two branch, the leaf hypothesis gives `Ls G ≤ 6`. -/
theorem Ls_le_six_of_residue_eq_two
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2)
    (hres : residue G = 2) :
    Ls G ≤ 6 := by
  norm_num [residueEqTwoIndicator, hres] at hL ⊢
  exact hL

/-- Every vertex has degree at most six in the exceptional branch. -/
theorem degree_le_six_of_residue_eq_two
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2)
    (hres : residue G = 2) :
    ∀ v, G.degree v ≤ 6 := by
  intro v
  have hcast : (G.degree v : ℝ) ≤ 6 :=
    (degree_cast_le_Ls_of_connected G hG v).trans
      (Ls_le_six_of_residue_eq_two G hL hres)
  exact_mod_cast hcast

#print axioms SimpleGraph.C217BaseReduction.traceable_of_residue_ne_two
#print axioms SimpleGraph.C217BaseReduction.Ls_le_six_of_residue_eq_two
#print axioms SimpleGraph.C217BaseReduction.degree_le_six_of_residue_eq_two

end SimpleGraph.C217BaseReduction
