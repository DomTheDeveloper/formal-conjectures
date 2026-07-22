/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217BaseReduction
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217DegreeBridge

/-!
# Terminal reduction for WOWII Conjecture 217

All infinite and nonexceptional reasoning is discharged here.  The sole
remaining input is a dispatcher proving traceability for a connected graph
whose exact degree sequence is one of the forty certified exceptional rows.
-/

namespace SimpleGraph.C217TerminalReduction

open Classical
open C217BaseReduction
open C217DegreeBridge
open C217FiniteCertificate

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The exact exceptional theorem still required by the finite certificate
layer.  It is deliberately stated with only graph-theoretic hypotheses that
have already been derived by the general reduction. -/
def ExceptionalDispatcher : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj],
    G.Connected →
    residue G = 2 →
    (∀ v, G.degree v ≤ 6) →
    degreeSequence G ∈ exceptionalSequences →
    IsTraceable G

/-- Once the exceptional dispatcher is supplied, the full C217 inequality
implies traceability. -/
theorem traceable_of_exceptionalDispatcher
    (dispatch : ExceptionalDispatcher (α := α))
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    (hL : Ls G ≤ 4 * (C217BaseReduction.residueEqTwoIndicator G : ℝ) + 2) :
    IsTraceable G := by
  by_cases hres : residue G = 2
  · have hdeg : ∀ v, G.degree v ≤ 6 :=
      degree_le_six_of_residue_eq_two G hG hL hres
    rcases chvatal_or_exceptional G hG hres hdeg with hch | hex
    · exact isTraceable_of_chvatalPathCondition G hch
    · exact dispatch G hG hres hdeg hex
  · exact traceable_of_residue_ne_two G hG hL hres

#print axioms SimpleGraph.C217TerminalReduction.traceable_of_exceptionalDispatcher

end SimpleGraph.C217TerminalReduction
