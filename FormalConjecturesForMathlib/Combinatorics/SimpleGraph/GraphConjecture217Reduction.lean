/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217TerminalReduction
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217ExceptionalDispatcher
import FormalConjectures.WrittenOnTheWallII.GraphConjecture217

/-!
# Exact catalog-namespace reduction for WOWII Conjecture 217

This file proves that the public catalog theorem follows immediately from the
finite exceptional dispatcher. Keeping the bridge in a separate module avoids
introducing a circular import while the final dispatcher is developed.
-/

namespace WrittenOnTheWallII.GraphConjecture217

open Classical SimpleGraph
open SimpleGraph.C217TerminalReduction
open SimpleGraph.C217RegularCertificate
open SimpleGraph.C217ExceptionalDispatcher

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

lemma residueEqTwoIndicator_eq_base
    (G : SimpleGraph α) [DecidableRel G.Adj] :
    residueEqTwoIndicator G =
      SimpleGraph.C217BaseReduction.residueEqTwoIndicator G := by
  rfl

/-- The exact public C217 conclusion follows from the exceptional dispatcher. -/
theorem conjecture217_of_exceptionalDispatcher
    (dispatch : ExceptionalDispatcher (α := α))
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) :
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  have hL' : Ls G ≤
      4 * (SimpleGraph.C217BaseReduction.residueEqTwoIndicator G : ℝ) + 2 := by
    simpa [residueEqTwoIndicator_eq_base G] using hL
  exact traceable_of_exceptionalDispatcher dispatch G hG hL'

/-- Four proof-producing regular certificates imply the exact public catalog
statement. This is the final theorem used when the LRAT files are imported. -/
theorem conjecture217_of_regularCertificates
    (cert83 : RegularCertificate 8 3)
    (cert104 : RegularCertificate 10 4)
    (cert125 : RegularCertificate 12 5)
    (cert146 : RegularCertificate 14 6)
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) :
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  apply conjecture217_of_exceptionalDispatcher
    (exceptionalDispatcher_of_regularCertificates cert83 cert104 cert125 cert146)
    G hG hL

#print axioms WrittenOnTheWallII.GraphConjecture217.conjecture217_of_exceptionalDispatcher
#print axioms WrittenOnTheWallII.GraphConjecture217.conjecture217_of_regularCertificates

end WrittenOnTheWallII.GraphConjecture217
