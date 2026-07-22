/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217PartialDispatcher
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217RegularRows
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217TerminalReduction

/-!
# Complete exceptional dispatcher for WOWII Conjecture 217

All graph-theoretic and finite degree-sequence work is complete here. The only
inputs are the four proof-producing finite certificates for the regular
boundary rows.
-/

namespace SimpleGraph.C217ExceptionalDispatcher

open Classical
open SimpleGraph
open SimpleGraph.C217OrderBound
open SimpleGraph.C217FiniteCertificate
open SimpleGraph.C217PartialDispatcher
open SimpleGraph.C217RegularCertificate
open SimpleGraph.C217RegularRows
open SimpleGraph.C217TerminalReduction

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]

/-- Four regular finite certificates complete the exact exceptional theorem. -/
theorem exceptionalDispatcher_of_regularCertificates
    (cert83 : RegularCertificate 8 3)
    (cert104 : RegularCertificate 10 4)
    (cert125 : RegularCertificate 12 5)
    (cert146 : RegularCertificate 14 6) :
    ExceptionalDispatcher (α := V) := by
  intro G _ hG hres hLs hdeg hrow
  rcases exceptional_mem_handled_or_remaining hrow with hhandled | hremaining
  · exact isTraceable_of_mem_handledRows G hG hLs hhandled
  · simp only [remainingRows, List.mem_cons, List.mem_singleton] at hremaining
    rcases hremaining with h83 | h104 | h125 | h146
    · exact row_33333333 cert83 G hG h83
    · exact row_4444444444 cert104 G hG h104
    · exact row_555555555555 cert125 G hG h125
    · exact row_66666666666666 cert146 G hG h146

/-- The full C217 inequality follows from the four regular certificates. -/
theorem traceable_of_regularCertificates
    (cert83 : RegularCertificate 8 3)
    (cert104 : RegularCertificate 10 4)
    (cert125 : RegularCertificate 12 5)
    (cert146 : RegularCertificate 14 6)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (hL : Ls G ≤
      4 * (SimpleGraph.C217BaseReduction.residueEqTwoIndicator G : ℝ) + 2) :
    IsTraceable G :=
  traceable_of_exceptionalDispatcher
    (exceptionalDispatcher_of_regularCertificates cert83 cert104 cert125 cert146)
    G hG hL

#print axioms SimpleGraph.C217ExceptionalDispatcher.exceptionalDispatcher_of_regularCertificates
#print axioms SimpleGraph.C217ExceptionalDispatcher.traceable_of_regularCertificates

end SimpleGraph.C217ExceptionalDispatcher
