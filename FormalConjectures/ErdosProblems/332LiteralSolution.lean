import FormalConjectures.ErdosProblems.«332»

/-!
# Literal solution of Erdős Problem 332's answer placeholder

The catalog asks for an unrestricted predicate on sets of naturals that is
sufficient for bounded gaps in `D_A A`. Choosing the predicate to be constantly
false makes the implication vacuous. This proves that the literal answer format
does not encode the intended task of finding a meaningful sufficient condition.
-/

namespace Erdos332

/-- The literal statement admits the vacuous sufficient condition `False`. -/
@[category research solved, AMS 11]
theorem erdos_332_literal_solution (A : Set ℕ) :
    ∃ condition : Set ℕ → Prop, condition A → HasBoundedGaps (D_A A) := by
  refine ⟨fun _ => False, ?_⟩
  intro h
  exact h.elim

#print axioms erdos_332_literal_solution

end Erdos332
