import C217DegreeBound
import C217DegreeTwoTraceable
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Residue

open Classical SimpleGraph
namespace C217

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

noncomputable def residueEqTwoIndicator (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  if residue G = 2 then 1 else 0

/-- The entire `residue G ≠ 2` branch of WOWII 217. -/
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

#print axioms traceable_of_residue_ne_two

end C217
