import C217DegreeBound
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Residue

open Classical SimpleGraph
namespace C217

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

noncomputable def residueEqTwoIndicator' (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  if residue G = 2 then 1 else 0

/-- In the exceptional residue-two branch, the leaf hypothesis forces `Ls G ≤ 6`. -/
theorem Ls_le_six_of_residue_eq_two
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hL : Ls G ≤ 4 * (residueEqTwoIndicator' G : ℝ) + 2)
    (hres : residue G = 2) :
    Ls G ≤ 6 := by
  norm_num [residueEqTwoIndicator', hres] at hL ⊢
  exact hL

/-- In the exceptional branch every vertex has degree at most six. -/
theorem degree_le_six_of_residue_eq_two
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    (hL : Ls G ≤ 4 * (residueEqTwoIndicator' G : ℝ) + 2)
    (hres : residue G = 2) :
    ∀ v, G.degree v ≤ 6 := by
  intro v
  have hcast : (G.degree v : ℝ) ≤ 6 :=
    (degree_cast_le_Ls_of_connected G hG v).trans
      (Ls_le_six_of_residue_eq_two G hL hres)
  exact_mod_cast hcast

#print axioms Ls_le_six_of_residue_eq_two
#print axioms degree_le_six_of_residue_eq_two

end C217
