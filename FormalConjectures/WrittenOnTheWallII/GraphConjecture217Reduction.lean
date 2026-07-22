/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
-/
import FormalConjectures.WrittenOnTheWallII.GraphConjecture217
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217TerminalReduction

/-!
# Exact catalog reduction for WOWII Conjecture 217

This file proves the original public statement from the one remaining finite
exceptional dispatcher.  No statement is weakened: the graph, inequality, and
Hamiltonian-path conclusion are exactly those of `conjecture217`.
-/

namespace WrittenOnTheWallII.GraphConjecture217

open Classical SimpleGraph
open SimpleGraph.C217TerminalReduction

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The catalog indicator agrees with the internal reduction indicator. -/
lemma residueEqTwoIndicator_eq_internal
    (G : SimpleGraph α) [DecidableRel G.Adj] :
    residueEqTwoIndicator G =
      SimpleGraph.C217BaseReduction.residueEqTwoIndicator G := by
  simp [residueEqTwoIndicator,
    SimpleGraph.C217BaseReduction.residueEqTwoIndicator]

/-- The exact catalog theorem follows from the certified exceptional-row
dispatcher. -/
theorem conjecture217_of_exceptionalDispatcher
    (dispatch : ExceptionalDispatcher (α := α))
    (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected)
    (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) :
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  apply traceable_of_exceptionalDispatcher dispatch G h
  simpa [residueEqTwoIndicator_eq_internal] using hL

#print axioms WrittenOnTheWallII.GraphConjecture217.conjecture217_of_exceptionalDispatcher

end WrittenOnTheWallII.GraphConjecture217
